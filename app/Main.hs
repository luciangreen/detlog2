-- | detlog2 command line.
module Main (main) where

import Control.Monad (forM, forM_, unless, when)
import Data.List (intercalate, isPrefixOf)
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import System.Directory (getTemporaryDirectory, removeFile)
import System.Environment (getArgs)
import System.Exit
import System.IO

import Detlog2.Builtins
import Detlog2.Check
import Detlog2.Convert
import Detlog2.Equiv
import Detlog2.Interp
import Detlog2.Memo
import Detlog2.Mnns
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference
import Detlog2.Term

usage :: String
usage = unlines
  [ "detlog2 - a choicepointless, cutless Prolog interpreter and Detlog converter"
  , ""
  , "  detlog2 run FILE QUERY [--max N] [--det]      run on the cutless interpreter"
  , "  detlog2 ref FILE QUERY [--max N]              run with ordinary cut semantics (reference)"
  , "  detlog2 convert FILE [-o OUT] [--no-splice]   cuts -> if_commit, choicepoints -> splices"
  , "  detlog2 packets FILE QUERY                    convert, then run the query as one packet"
  , "  detlog2 check FILE QUERY... [--max N]         convert, verify no choicepoints, compare answers"
  , "  detlog2 memoise FILE --goal G ... [--complete] [-o OUT] [--check Q ...]"
  , "                                                expand calls into answer tables"
  , "  detlog2 mnns FILE [--mnns DIR] [-o OUT] [--check Q ...]"
  , "                                                rewrite with mnns optimise.pl, then convert"
  ]

data Flags = Flags
  { fMax :: Int
  , fDet :: Bool
  , fOut :: Maybe FilePath
  , fSplice :: Bool
  , fGoals :: [String]
  , fChecks :: [String]
  , fComplete :: Bool
  , fMnns :: Maybe FilePath
  , fPositional :: [String]
  }

parseFlags :: [String] -> Either String Flags
parseFlags = go (Flags 50 False Nothing True [] [] False Nothing [])
  where
    go f [] = Right f { fPositional = reverse (fPositional f), fGoals = reverse (fGoals f)
                      , fChecks = reverse (fChecks f) }
    go f ("--max" : n : r) = go f { fMax = read n } r
    go f ("--max-answers" : n : r) = go f { fMax = read n } r
    go f ("--det" : r) = go f { fDet = True } r
    go f ("-o" : o : r) = go f { fOut = Just o } r
    go f ("--no-splice" : r) = go f { fSplice = False } r
    go f ("--goal" : g : r) = go f { fGoals = g : fGoals f } r
    go f ("--check" : q : r) = go f { fChecks = q : fChecks f } r
    go f ("--complete" : r) = go f { fComplete = True } r
    go f ("--mnns" : d : r) = go f { fMnns = Just d } r
    go _ (x : _) | "--" `isPrefixOf` x = Left ("unknown option " ++ x)
    go f (x : r) = go f { fPositional = x : fPositional f } r

main :: IO ()
main = do
  hSetEncoding stdout utf8
  args <- getArgs
  case args of
    [] -> putStr usage
    ("help" : _) -> putStr usage
    (cmd : rest) -> case parseFlags rest of
      Left e -> die' e
      Right fl -> dispatch cmd fl

die' :: String -> IO a
die' msg = hPutStrLn stderr ("detlog2: " ++ msg) >> exitWith (ExitFailure 1)

loadProgram :: FilePath -> IO Program
loadProgram path = do
  src <- readFile path
  case parseProgram src of
    Left e -> die' (path ++ ": " ++ e)
    Right p -> return p

parseQ :: String -> IO (Term, [(String, Term)], Int)
parseQ q = either (\e -> die' ("query: " ++ e)) return (parseQuery q)

dispatch :: String -> Flags -> IO ()
dispatch cmd fl = case (cmd, fPositional fl) of
  ("run", [file, q]) -> do
    p <- loadProgram file
    (g, vs, nv) <- parseQ q
    let opts = defaultOptions { optDetCheck = fDet fl }
    printAnswers (fMax fl) vs (runGoal opts (withPrelude p) g nv)
  ("ref", [file, q]) -> do
    p <- loadProgram file
    (g, vs, nv) <- parseQ q
    printAnswers (fMax fl) vs (refRun defaultOptions (withPrelude p) g nv)
  ("convert", [file]) -> do
    p <- loadProgram file
    conv <- convertOrDie fl p
    writeConverted fl file (crEvents conv) (crProgram conv)
  ("packets", [file, q]) -> do
    p <- loadProgram file
    (g, vs, nv) <- parseQ q
    let (p', qk) = addQueryClause g (map snd vs) nv p
    conv <- either (\e -> die' ("conversion failed: " ++ e)) return
              (convertProgram defaultConvertOptions { coSpliceEarly = fSplice fl, coRoots = Just [qk] } p')
    reportCheck (crProgram conv)
    let k = length vs
        vars = [ Var i ("V" ++ show i) | i <- [0 .. k - 1] ]
        rowsV = Var k "Rows"
        goal = Comp (cpName "$query") (vars ++ [rowsV])
        stream = runGoal defaultOptions { optDetCheck = True } (crProgram conv) goal (k + 1)
    forM_ stream $ \ev -> case ev of
      Out t -> putStr t
      Err e -> putStrLn ("error: " ++ e)
      Ans s -> do
        let rows = resolve s rowsV
        putStrLn ("packet: cp(" ++ showTermQ rows ++ ")")
        case termToList s rows of
          Just rs | not (null rs) -> forM_ rs $ \r -> case termToList s r of
            Just vals -> putStrLn (showBindings (zip (map fst vs) vals))
            Nothing -> return ()
          _ -> putStrLn "false."
  ("check", file : qs@(_ : _)) -> do
    p <- loadProgram file
    okAll <- forM qs $ \q -> checkQuery fl p q
    if and okAll then putStrLn "all checks passed" else exitWith (ExitFailure 1)
  ("memoise", [file]) -> memoise fl file
  ("memoize", [file]) -> memoise fl file
  ("mnns", [file]) -> mnnsPass fl file
  _ -> die' ("bad arguments\n" ++ usage)

convertOrDie :: Flags -> Program -> IO ConvertResult
convertOrDie fl p =
  either (\e -> die' ("conversion failed: " ++ e)) return
    (convertProgram defaultConvertOptions { coSpliceEarly = fSplice fl } p)

reportCheck :: Program -> IO ()
reportCheck conv = do
  let problems = checkDeterministic conv
  unless (null problems) $ do
    hPutStrLn stderr "choicepoint check FAILED:"
    mapM_ (hPutStrLn stderr . ("  " ++)) problems
    exitWith (ExitFailure 2)

writeConverted :: Flags -> FilePath -> [String] -> Program -> IO ()
writeConverted fl source events prog = do
  reportCheck prog
  let header = unlines $
        [ "% Detlog code generated by detlog2 from " ++ source
        , "% No cuts and no choicepoints: every predicate succeeds exactly once and"
        , "% returns its answer packet in its last argument (see README)."
        , "% Run it with: detlog2 run --det FILE 'p__cp(Args..., Rows)'"
        , "%"
        ] ++ [ "% " ++ e | e <- events ]
      text = header ++ "\n" ++ showProgram prog
  case fOut fl of
    Nothing -> putStr text
    Just o -> writeFile o text >> hPutStrLn stderr ("wrote " ++ o)

-- | A query variable that is still unbound and unaliased is not shown.
unboundSelf :: Term -> Term -> Bool
unboundSelf (Var i _) (Var j _) = i == j
unboundSelf _ _ = False

showBindings :: [(String, Term)] -> String
showBindings [] = "true."
showBindings bs = intercalate ", " [ n ++ " = " ++ showAnswerVal v | (n, v) <- bs ] ++ "."
  where showAnswerVal = showTermQ

printAnswers :: Int -> [(String, Term)] -> Stream -> IO ()
printAnswers maxAns vs stream = loop (0 :: Int) stream
  where
    named = [ (n, v) | (n, v) <- vs, not ("_" `isPrefixOf` n) ]
    loop k _ | k >= maxAns = putStrLn ("% stopped after " ++ show maxAns ++ " answers")
    loop k [] = when (k == 0) (putStrLn "false.")
    loop k (Out t : r) = putStr t >> hFlush stdout >> loop k r
    loop _ (Err e : _) = putStrLn ("error: " ++ e) >> exitWith (ExitFailure 3)
    loop k (Ans s : r) = do
      putStrLn (showBindings [ (n, t) | (n, v) <- named, let t = resolve s v, not (unboundSelf v t) ])
      loop (k + 1) r

checkQuery :: Flags -> Program -> String -> IO Bool
checkQuery fl p q = do
  (g, vs, nv) <- parseQ q
  let vars = map snd vs
      (p', qk) = addQueryClause g vars nv p
  case convertProgram defaultConvertOptions { coSpliceEarly = fSplice fl, coRoots = Just [qk] } p' of
    Left e -> putStrLn ("FAIL " ++ q ++ "\n  conversion failed: " ++ e) >> return False
    Right conv -> do
      let problems = checkDeterministic (crProgram conv)
          src = sourceOutcome defaultOptions (fMax fl) p g vars nv
          out = convertedOutcome defaultOptions (fMax fl) (crProgram conv) (length vars)
      reportOutcome q problems src out

reportOutcome :: String -> [String] -> Outcome -> Outcome -> IO Bool
reportOutcome q problems src out = do
  let sameAnswers = ocAnswers src == ocAnswers out && ocError out == Nothing
      sameOutput = ocOutput src == ocOutput out
      good = null problems && sameAnswers && ocError src == Nothing
  putStrLn ((if good then "ok   " else "FAIL ") ++ q)
  unless (null problems) $ mapM_ (putStrLn . ("  choicepoint check: " ++)) problems
  unless (sameAnswers && ocError src == Nothing) $ do
    putStrLn " source (cut semantics):" >> putStr (showOutcome src)
    putStrLn " converted (choicepoint-free):" >> putStr (showOutcome out)
  when (good && not sameOutput) $
    putStrLn ("  note: same answers; output order differs (packets are computed before their continuation):\n"
              ++ "    source:    " ++ show (ocOutput src) ++ "\n    converted: " ++ show (ocOutput out))
  when good $ putStrLn ("  " ++ show (length (ocAnswers out)) ++ " answer(s), identical order")
  return good

memoise :: Flags -> FilePath -> IO ()
memoise fl file = do
  p <- loadProgram file
  when (null (fGoals fl)) $ die' "memoise: give at least one --goal"
  table <- foldlM' (\t gs -> do
                      (g, _, nv) <- parseQ gs
                      either die' return (memoCall defaultOptions (fMax fl) p g nv t))
                   emptyTable (fGoals fl)
  let memoKeys = Set.fromList (tableKeys table)
      -- with --complete, memoised predicates are answered from their tables
      -- only, so their own (possibly cut-using) clauses are not converted.
      external = if fComplete fl then memoKeys else Set.empty
      p1 = if fComplete fl then dropPreds memoKeys p else p
      opts = defaultConvertOptions { coSpliceEarly = fSplice fl, coExternal = external
                                   , coRoots = Just (Set.toList memoKeys) }
      withQ q = do
        (g, vs, nv) <- parseQ q
        return (addQueryClause g (map snd vs) nv p1, (g, vs, nv))
  conv <- either (\e -> die' ("conversion failed: " ++ e)) return (convertProgram opts p1)
  let memoProg = addMemoTables (fComplete fl) table (crProgram conv)
      events = crEvents conv ++ [ "memoised(" ++ f ++ "/" ++ show n ++ ", " ++ show k ++ " call pattern(s)"
                                  ++ (if fComplete fl then ", complete" else "") ++ ")"
                                | ((f, n), k) <- tableSizes table ]
  writeConverted fl file events memoProg
  okAll <- forM (fChecks fl) $ \q -> do
    ((pq, qk), (g, vs, nv)) <- withQ q
    case convertProgram opts { coRoots = Just (qk : Set.toList memoKeys) } pq of
      Left e -> putStrLn ("FAIL " ++ q ++ ": " ++ e) >> return False
      Right cq -> do
        let prog = addMemoTables (fComplete fl) table (crProgram cq)
            src = sourceOutcome defaultOptions (fMax fl) p g (map snd vs) nv
            out = convertedOutcome defaultOptions (fMax fl) prog (length vs)
        reportOutcome q (checkDeterministic prog) src out
  unless (and okAll) $ exitWith (ExitFailure 1)
  where
    foldlM' f z xs = foldl (\acc x -> acc >>= \a -> f a x) (return z) xs

mnnsPass :: Flags -> FilePath -> IO ()
mnnsPass fl file = do
  dir <- findMnnsDir (fMnns fl) >>= either die' return
  tmp <- getTemporaryDirectory
  let mid = tmp ++ "/detlog2_mnns_out.pl"
  r <- runMnnsOptimise dir file mid
  (p, events) <- case r of
    Right report -> do
      hPutStrLn stderr ("mnns: " ++ report)
      p <- loadProgram mid
      removeFile mid
      return (p, ["mnns optimise.pl: " ++ report])
    Left e -> do
      hPutStrLn stderr ("mnns pass not applied: " ++ e)
      p <- loadProgram file
      return (p, ["mnns optimise.pl not applied: " ++ takeWhile (/= '\n') e])
  conv <- convertOrDie fl p
  writeConverted fl file (events ++ crEvents conv) (crProgram conv)
  okAll <- forM (fChecks fl) $ \q -> do
    orig <- loadProgram file
    (g, vs, nv) <- parseQ q
    let (pq, qk) = addQueryClause g (map snd vs) nv p
    case convertProgram defaultConvertOptions { coSpliceEarly = fSplice fl, coRoots = Just [qk] } pq of
      Left e -> putStrLn ("FAIL " ++ q ++ ": " ++ e) >> return False
      Right cq -> do
        let src = sourceOutcome defaultOptions (fMax fl) orig g (map snd vs) nv
            out = convertedOutcome defaultOptions (fMax fl) (crProgram cq) (length vs)
        reportOutcome q (checkDeterministic (crProgram cq)) src out
  unless (and okAll) $ exitWith (ExitFailure 1)

-- small helpers over memo tables -------------------------------------------

emptyTable :: MemoTable
emptyTable = M.empty

tableKeys :: MemoTable -> [PredKey]
tableKeys = M.keys

tableSizes :: MemoTable -> [(PredKey, Int)]
tableSizes t = [ (k, length es) | (k, es) <- M.toList t ]

dropPreds :: Set.Set PredKey -> Program -> Program
dropPreds ks p = programFromClauses [ c | (k, cs) <- programClauses p, not (Set.member k ks), c <- cs ]
