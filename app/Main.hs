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
import Detlog2.Proof
import Detlog2.Reference
import Detlog2.Term

usage :: String
usage = unlines
  [ "detlog2 - a choicepointless, cutless Prolog interpreter and a proof-carrying Detlog converter"
  , ""
  , "  detlog2 run FILE QUERY [--max N] [--det]      run on the cutless interpreter"
  , "  detlog2 ref FILE QUERY [--max N]              run with ordinary cut semantics (reference)"
  , "  detlog2 convert FILE [-o OUT] [--no-splice]   cuts -> if_commit, choicepoints -> splices;"
  , "                                                writes OUT and its proof OUT.proof"
  , "  detlog2 proof-check FILE OUT OUT.proof        check a conversion proof independently"
  , "  detlog2 packets FILE QUERY                    convert, then run the query as one packet"
  , "  detlog2 check FILE QUERY... [--max N]         convert, check the proof and choicepoint-freedom,"
  , "                                                compare answers and output with the source"
  , "  detlog2 memoise FILE --goal G ... [--complete] [-o OUT] [--check Q ...]"
  , "                                                expand calls into answer tables"
  , "  detlog2 mnns FILE [--mnns DIR] [-o OUT] [--check Q ...]"
  , "                                                rewrite with mnns optimise.pl, then convert"
  , ""
  , "Every conversion is proof-gated: nothing is written unless Detlog2.Proof accepts its proof."
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

convOpts :: Flags -> ConvertOptions
convOpts fl = defaultConvertOptions { coSpliceEarly = fSplice fl }

-- | Convert and check the proof; nothing unproved is returned.
provedConversion :: ConvertOptions -> Program -> Program -> Either String (ConvertResult, [String])
provedConversion opts original p = do
  conv <- either (\e -> Left ("conversion failed: " ++ e)) Right (convertProgram opts p)
  report <- either (\e -> Left ("proof rejected: " ++ e)) Right
              (checkProof (ProofContext p (coExternal opts) original) (crProof conv) (crProgram conv))
  return (conv, report)

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
    (conv, report) <- either die' return (provedConversion (convOpts fl) p p)
    writeConverted fl file (crEvents conv ++ report) (crProgram conv) (crProof conv)
  ("proof-check", [file, out, proofFile]) -> do
    p <- loadProgram file
    conv <- loadProgram out
    steps <- readFile proofFile >>= either (\e -> die' (proofFile ++ ": " ++ e)) return . proofFromText
    case checkProof (ProofContext p Set.empty p) steps conv of
      Left e -> die' ("proof rejected: " ++ e)
      Right report -> mapM_ putStrLn report
  ("packets", [file, q]) -> do
    p <- loadProgram file
    (g, vs, nv) <- parseQ q
    let (p', qk) = addQueryClause g (map snd vs) nv p
    (conv, report) <- either die' return (provedConversion (convOpts fl) { coRoots = Just [qk] } p p')
    reportCheck (crProgram conv)
    mapM_ (hPutStrLn stderr) report
    let k = length vs
        vars = [ Var i ("V" ++ show i) | i <- [0 .. k - 1] ]
        rowsV = Var k "Rows"
        goal = Comp (cpName "$query") (vars ++ [rowsV])
        stream = runGoal defaultOptions { optDetCheck = True } (crProgram conv) goal (k + 1)
    forM_ stream $ \ev -> case ev of
      Out t -> putStr t
      Err e -> putStrLn ("error: " ++ e)
      Ans s -> do
        let items = resolve s rowsV
        putStrLn ("packet: cp(" ++ showTermQ items ++ ")")
        case termToList s items of
          Just is -> do
            let rows = [ r | r <- map (resolve s) is, not (isOutItem r) ]
            forM_ (map (resolve s) is) $ \it -> case it of
              Comp "out" [Atom t] -> putStr t
              _ -> case termToList s it of
                Just vals -> putStrLn (showBindings (zip (map fst vs) vals))
                Nothing -> return ()
            when (null rows) (putStrLn "false.")
          Nothing -> putStrLn "false."
  ("check", file : qs@(_ : _)) -> do
    p <- loadProgram file
    okAll <- forM qs $ \q -> checkQuery fl p q
    if and okAll then putStrLn "all checks passed" else exitWith (ExitFailure 1)
  ("memoise", [file]) -> memoise fl file
  ("memoize", [file]) -> memoise fl file
  ("mnns", [file]) -> mnnsPass fl file
  _ -> die' ("bad arguments\n" ++ usage)

isOutItem :: Term -> Bool
isOutItem (Comp "out" [_]) = True
isOutItem _ = False

reportCheck :: Program -> IO ()
reportCheck conv = do
  let problems = checkDeterministic conv
  unless (null problems) $ do
    hPutStrLn stderr "choicepoint check FAILED:"
    mapM_ (hPutStrLn stderr . ("  " ++)) problems
    exitWith (ExitFailure 2)

writeConverted :: Flags -> FilePath -> [String] -> Program -> [Term] -> IO ()
writeConverted fl source events prog steps = do
  reportCheck prog
  let header = unlines $
        [ "% Detlog code generated by detlog2 from " ++ source
        , "% No cuts and no choicepoints: every predicate succeeds exactly once and"
        , "% returns its answer packet (rows and out(Text) items) in its last argument."
        , "% Run it with: detlog2 run --det FILE 'p__cp(Args..., Packet)'"
        , "%"
        ] ++ [ "% " ++ e | e <- events ]
      text = header ++ "\n" ++ showProgram prog
  case fOut fl of
    Nothing -> putStr text
    Just o -> do
      writeFile o text
      writeFile (o ++ ".proof") (proofToText steps)
      hPutStrLn stderr ("wrote " ++ o ++ " and " ++ o ++ ".proof")

showBindings :: [(String, Term)] -> String
showBindings [] = "true."
showBindings bs = intercalate ", " [ n ++ " = " ++ showTermQ v | (n, v) <- bs ] ++ "."

-- | A query variable that is still unbound and unaliased is not shown.
unboundSelf :: Term -> Term -> Bool
unboundSelf (Var i _) (Var j _) = i == j
unboundSelf _ _ = False

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
  case provedConversion (convOpts fl) { coRoots = Just [qk] } p p' of
    Left e -> putStrLn ("FAIL " ++ q ++ "\n  " ++ e) >> return False
    Right (conv, report) -> do
      let src = sourceOutcome defaultOptions (fMax fl) p g vars nv
          out = convertedOutcome defaultOptions (fMax fl) (crProgram conv) (length vars)
      reportOutcome q report (checkDeterministic (crProgram conv)) src out

reportOutcome :: String -> [String] -> [String] -> Outcome -> Outcome -> IO Bool
reportOutcome q report problems src out = do
  let sameAnswers = ocAnswers src == ocAnswers out && ocError out == Nothing
      sameOutput = ocOutput src == ocOutput out
      good = null problems && sameAnswers && sameOutput && ocError src == Nothing
  putStrLn ((if good then "ok   " else "FAIL ") ++ q)
  unless (null problems) $ mapM_ (putStrLn . ("  choicepoint check: " ++)) problems
  unless good $ do
    putStrLn " source (cut semantics):" >> putStr (showOutcome src)
    putStrLn " converted (choicepoint-free):" >> putStr (showOutcome out)
  when good $ do
    mapM_ (putStrLn . ("  " ++)) report
    putStrLn ("  " ++ show (length (ocAnswers out)) ++ " answer(s) and the output, identical and in the same order")
  return good

memoise :: Flags -> FilePath -> IO ()
memoise fl file = do
  p <- loadProgram file
  when (null (fGoals fl)) $ die' "memoise: give at least one --goal"
  table <- foldlM' (\t gs -> do
                      (g, _, nv) <- parseQ gs
                      either die' return (memoCall defaultOptions (fMax fl) p g nv t))
                   M.empty (fGoals fl)
  let memoKeys = Set.fromList (M.keys table)
      -- with --complete, memoised predicates are answered from their tables
      -- only, so their own (possibly cut-using) clauses are not converted.
      external = if fComplete fl then memoKeys else Set.empty
      p1 = if fComplete fl then dropPreds memoKeys p else p
      opts roots = (convOpts fl) { coExternal = external, coRoots = Just roots }
      build roots prog = do
        conv <- either (\e -> Left ("conversion failed: " ++ e)) Right (convertProgram (opts roots) prog)
        let (memoProg, memoSteps) = addMemoTables (fComplete fl) table (crProgram conv)
            steps = crProof conv ++ memoSteps
        report <- either (\e -> Left ("proof rejected: " ++ e)) Right
                    (checkProof (ProofContext prog external p) steps memoProg)
        return (conv, memoProg, steps, report)
  (conv, memoProg, steps, report) <- either die' return (build (Set.toList memoKeys) p1)
  let events = crEvents conv ++ [ "memoised(" ++ f ++ "/" ++ show n ++ ", " ++ show (length es) ++ " call pattern(s)"
                                  ++ (if fComplete fl then ", complete" else "") ++ ")"
                                | ((f, n), es) <- M.toList table ] ++ report
  writeConverted fl file events memoProg steps
  okAll <- forM (fChecks fl) $ \q -> do
    (g, vs, nv) <- parseQ q
    let (pq, qk) = addQueryClause g (map snd vs) nv p1
    case build (qk : Set.toList memoKeys) pq of
      Left e -> putStrLn ("FAIL " ++ q ++ ": " ++ e) >> return False
      Right (_, prog, _, rep) -> do
        let src = sourceOutcome defaultOptions (fMax fl) p g (map snd vs) nv
            out = convertedOutcome defaultOptions (fMax fl) prog (length vs)
        reportOutcome q rep (checkDeterministic prog) src out
  unless (and okAll) $ exitWith (ExitFailure 1)
  where
    foldlM' f z xs = foldl (\acc x -> acc >>= \a -> f a x) (return z) xs

mnnsPass :: Flags -> FilePath -> IO ()
mnnsPass fl file = do
  dir <- findMnnsDir (fMnns fl) >>= either die' return
  tmp <- getTemporaryDirectory
  let mid = tmp ++ "/detlog2_mnns_out.pl"
  orig <- loadProgram file
  r <- runMnnsOptimise dir file mid
  (p, events) <- case r of
    Right report -> do
      hPutStrLn stderr ("mnns: " ++ report)
      p <- loadProgram mid
      removeFile mid
      return (p, [ "mnns optimise.pl (its rewrites are proved by mnns's own checker): " ++ report
                 , "detlog2's proof below is relative to the mnns output" ])
    Left e -> do
      hPutStrLn stderr ("mnns pass not applied: " ++ e)
      return (orig, ["mnns optimise.pl not applied: " ++ takeWhile (/= '\n') e])
  (conv, report) <- either die' return (provedConversion (convOpts fl) p p)
  writeConverted fl file (events ++ crEvents conv ++ report) (crProgram conv) (crProof conv)
  okAll <- forM (fChecks fl) $ \q -> do
    (g, vs, nv) <- parseQ q
    let (pq, qk) = addQueryClause g (map snd vs) nv p
    case provedConversion (convOpts fl) { coRoots = Just [qk] } p pq of
      Left e -> putStrLn ("FAIL " ++ q ++ ": " ++ e) >> return False
      Right (cq, rep) -> do
        let src = sourceOutcome defaultOptions (fMax fl) orig g (map snd vs) nv
            out = convertedOutcome defaultOptions (fMax fl) (crProgram cq) (length vs)
        reportOutcome q rep (checkDeterministic (crProgram cq)) src out
  unless (and okAll) $ exitWith (ExitFailure 1)

dropPreds :: Set.Set PredKey -> Program -> Program
dropPreds ks p = programFromClauses [ c | (k, cs) <- programClauses p, not (Set.member k ks), c <- cs ]
