-- | A small standard-Prolog reader: tokens, operator-precedence parsing,
-- and programs as ordered clause lists.
module Detlog2.Parser
  ( Clause(..)
  , Program(..)
  , PredKey
  , parseProgram
  , parseTermString
  , parseQuery
  , programFromClauses
  , emptyProgram
  , programClauses
  , infixOps
  , prefixOps
  , Assoc(..)
  , PAssoc(..)
  ) where

import Data.Char
import qualified Data.Map.Strict as M
import Detlog2.Term

type PredKey = (String, Int)

data Clause = Clause
  { clHead :: Term
  , clBody :: Term
  , clNVars :: Int        -- variables are numbered 0 .. clNVars-1
  } deriving (Show)

data Program = Program
  { progPreds :: M.Map PredKey [Clause]
  , progOrder :: [PredKey]
  , progDirectives :: [Term]
  } deriving (Show)

emptyProgram :: Program
emptyProgram = Program M.empty [] []

programClauses :: Program -> [(PredKey, [Clause])]
programClauses p = [ (k, M.findWithDefault [] k (progPreds p)) | k <- progOrder p ]

programFromClauses :: [Clause] -> Program
programFromClauses = foldl add emptyProgram
  where
    add p c = case goalKey (clHead c) of
      Nothing -> p
      Just k
        | M.member k (progPreds p) ->
            p { progPreds = M.adjust (++ [c]) k (progPreds p) }
        | otherwise ->
            p { progPreds = M.insert k [c] (progPreds p)
              , progOrder = progOrder p ++ [k] }

-- ---------------------------------------------------------------------------
-- Operators

data Assoc = XFX | XFY | YFX deriving (Eq, Show)
data PAssoc = FY | FX deriving (Eq, Show)

infixOps :: M.Map String (Int, Assoc)
infixOps = M.fromList $
  [ (":-", (1200, XFX)), ("-->", (1200, XFX))
  , (";", (1100, XFY)), ("|", (1100, XFY))
  , ("->", (1050, XFY)), ("*->", (1050, XFY))
  , (",", (1000, XFY))
  ] ++
  [ (o, (700, XFX)) | o <- [ "=", "\\=", "==", "\\==", "@<", "@>", "@=<", "@>="
                            , "=..", "is", "=:=", "=\\=", "<", ">", "=<", ">="
                            , "=@=", "\\=@=" ] ] ++
  [ (":", (200, XFY)) ] ++
  [ (o, (500, YFX)) | o <- ["+", "-", "/\\", "\\/", "xor"] ] ++
  [ (o, (400, YFX)) | o <- ["*", "/", "//", "mod", "rem", "<<", ">>", "div"] ] ++
  [ ("**", (200, XFX)), ("^", (200, XFY)) ]

prefixOps :: M.Map String (Int, PAssoc)
prefixOps = M.fromList
  [ (":-", (1200, FX)), ("?-", (1200, FX))
  , ("\\+", (900, FY))
  , ("-", (200, FY)), ("+", (200, FY)), ("\\", (200, FY))
  , ("dynamic", (1150, FX)), ("discontiguous", (1150, FX))
  ]

-- ---------------------------------------------------------------------------
-- Lexer

data Tok
  = TName String
  | TFunct String          -- a name immediately followed by "("
  | TVarT String
  | TIntT Integer
  | TFltT Double
  | TStrT String
  | TBackq String
  | TPunct String
  | TEnd
  deriving (Eq, Show)

isSymCh :: Char -> Bool
isSymCh c = c `elem` "+-*/\\^<>=~:.?@#&$"

isAlnumU :: Char -> Bool
isAlnumU c = isAlphaNum c || c == '_'

lexer :: Int -> String -> Either String [(Tok, Int)]
lexer _ [] = Right []
lexer ln s@(c:r)
  | c == '\n' = lexer (ln + 1) r
  | isSpace c = lexer ln r
  | c == '%' = lexer ln (dropWhile (/= '\n') r)
  | c == '/' , take 1 r == "*" = skipBlock ln (drop 1 r)
  | isLower c = let (w, rest) = span isAlnumU s in nameTok w rest
  | isUpper c || c == '_' =
      let (w, rest) = span isAlnumU s in ((TVarT w, ln) :) <$> lexer ln rest
  | isDigit c = number s
  | c == '\'' = do
      (str, rest, ln') <- quoted '\'' ln r
      nameTokL ln' str rest
  | c == '"' = do
      (str, rest, ln') <- quoted '"' ln r
      ((TStrT str, ln) :) <$> lexer ln' rest
  | c == '`' = do
      (str, rest, ln') <- quoted '`' ln r
      ((TBackq str, ln) :) <$> lexer ln' rest
  | c `elem` "()[]{},|" = ((TPunct [c], ln) :) <$> lexer ln r
  | c == '!' = nameTok "!" r
  | c == ';' = nameTok ";" r
  | c == '.' && endFollows r = ((TEnd, ln) :) <$> lexer ln r
  | isSymCh c = let (w, rest) = span isSymCh s in nameTok w rest
  | otherwise = Left ("line " ++ show ln ++ ": unexpected character " ++ show c)
  where
    nameTok w rest = nameTokL ln w rest
    nameTokL l w rest
      | take 1 rest == "(" = ((TFunct w, l) :) <$> lexer l rest
      | otherwise = ((TName w, l) :) <$> lexer l rest
    endFollows rest = case rest of
      [] -> True
      (d:_) -> isSpace d || d == '%'
    skipBlock l ('*':'/':rest) = lexer l rest
    skipBlock l ('\n':rest) = skipBlock (l + 1) rest
    skipBlock l (_:rest) = skipBlock l rest
    skipBlock l [] = Left ("line " ++ show l ++ ": unterminated block comment")
    number str = case str of
      ('0':'\'':rest) -> charCode rest
      ('0':'x':rest) | not (null (takeWhile isHexDigit rest)) ->
        let (h, rest') = span isHexDigit rest
        in ((TIntT (read ("0x" ++ h)), ln) :) <$> lexer ln rest'
      _ ->
        let (ds, rest) = span isDigit str
        in case rest of
             ('.':d:rest2) | isDigit d ->
               let (fs, rest3) = span isDigit (d:rest2)
                   (ex, rest4) = expo rest3
               in ((TFltT (read (ds ++ "." ++ fs ++ ex)), ln) :) <$> lexer ln rest4
             _ -> ((TIntT (read ds), ln) :) <$> lexer ln rest
    expo (e:rest) | e `elem` "eE" =
      case rest of
        (sgn:d:more) | sgn `elem` "+-" && isDigit d ->
          let (ds, r') = span isDigit (d:more) in ("e" ++ [sgn | sgn == '-'] ++ ds, r')
        (d:more) | isDigit d ->
          let (ds, r') = span isDigit (d:more) in ("e" ++ ds, r')
        _ -> ("", e:rest)
    expo rest = ("", rest)
    charCode rest = case rest of
      ('\\':e:more) -> ((TIntT (fromIntegral (ord (escape e))), ln) :) <$> lexer ln more
      ('\'':'\'':more) -> ((TIntT 39, ln) :) <$> lexer ln more
      (ch:more) -> ((TIntT (fromIntegral (ord ch)), ln) :) <$> lexer ln more
      [] -> Left ("line " ++ show ln ++ ": bad character code")

escape :: Char -> Char
escape e = case e of
  'n' -> '\n'
  't' -> '\t'
  'r' -> '\r'
  'a' -> '\a'
  'b' -> '\b'
  'f' -> '\f'
  'v' -> '\v'
  '0' -> '\0'
  's' -> ' '
  'e' -> '\ESC'
  other -> other

quoted :: Char -> Int -> String -> Either String (String, String, Int)
quoted q = go []
  where
    go acc ln s = case s of
      [] -> Left ("line " ++ show ln ++ ": unterminated quoted item")
      (c:d:rest) | c == q && d == q -> go (q : acc) ln rest
      (c:rest) | c == q -> Right (reverse acc, rest, ln)
      ('\\':'\n':rest) -> go acc (ln + 1) rest
      ('\\':e:rest) -> go (escape e : acc) ln rest
      ('\n':rest) -> go ('\n' : acc) (ln + 1) rest
      (c:rest) -> go (c : acc) ln rest

-- ---------------------------------------------------------------------------
-- Parser

data PS = PS
  { psToks :: [(Tok, Int)]
  , psVars :: M.Map String Int
  , psNext :: Int
  }

newtype P a = P { runP :: PS -> Either String (a, PS) }

instance Functor P where
  fmap f (P g) = P $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> Right (f a, s')

instance Applicative P where
  pure a = P $ \s -> Right (a, s)
  P f <*> P g = P $ \s -> case f s of
    Left e -> Left e
    Right (h, s') -> case g s' of
      Left e -> Left e
      Right (a, s'') -> Right (h a, s'')

instance Monad P where
  P g >>= k = P $ \s -> case g s of
    Left e -> Left e
    Right (a, s') -> runP (k a) s'

failP :: String -> P a
failP msg = P $ \s -> Left (where' s ++ msg)
  where
    where' s = case psToks s of
      ((_, l):_) -> "line " ++ show l ++ ": "
      [] -> "end of input: "

peek :: P (Maybe Tok)
peek = P $ \s -> Right (fst <$> safeHead (psToks s), s)
  where safeHead (x:_) = Just x
        safeHead [] = Nothing

peek2 :: P (Maybe Tok)
peek2 = P $ \s -> Right (case psToks s of
                           (_:(t, _):_) -> Just t
                           _ -> Nothing, s)

advance :: P ()
advance = P $ \s -> Right ((), s { psToks = drop 1 (psToks s) })

next :: P Tok
next = do
  mt <- peek
  case mt of
    Nothing -> failP "unexpected end of input"
    Just t -> advance >> return t

expect :: Tok -> P ()
expect t = do
  t' <- next
  if t' == t then return () else failP ("expected " ++ showTok t ++ " but found " ++ showTok t')

showTok :: Tok -> String
showTok t = case t of
  TName n -> n
  TFunct n -> n ++ "("
  TVarT n -> n
  TIntT i -> show i
  TFltT d -> show d
  TStrT s -> show s
  TBackq s -> show s
  TPunct p -> p
  TEnd -> "end of clause"

varFor :: String -> P Term
varFor "_" = P $ \s -> Right (Var (psNext s) "_", s { psNext = psNext s + 1 })
varFor n = P $ \s -> case M.lookup n (psVars s) of
  Just i -> Right (Var i n, s)
  Nothing -> let i = psNext s
             in Right (Var i n, s { psVars = M.insert n i (psVars s), psNext = i + 1 })

-- | Parse a term with maximum priority, returning the term and its priority.
term :: Int -> P (Term, Int)
term maxP = do
  (left, lp) <- primary maxP
  infixLoop maxP left lp

infixLoop :: Int -> Term -> Int -> P (Term, Int)
infixLoop maxP left lp = do
  mt <- peek
  let opName = case mt of
        Just (TName n) -> Just n
        Just (TPunct ",") -> Just ","
        Just (TPunct "|") -> Just "|"
        _ -> Nothing
  case opName >>= \n -> fmap ((,) n) (M.lookup n infixOps) of
    Just (n, (p, a)) ->
      let (la, ra) = case a of
            XFX -> (p - 1, p - 1)
            XFY -> (p - 1, p)
            YFX -> (p, p - 1)
      in if p <= maxP && lp <= la
           then do
             advance
             (right, _) <- term ra
             let n' = if n == "|" then ";" else n
             infixLoop maxP (Comp n' [left, right]) p
           else return (left, lp)
    Nothing -> return (left, lp)

canStart :: Maybe Tok -> Bool
canStart mt = case mt of
  Just (TName n) -> not (M.member n infixOps && not (M.member n prefixOps))
  Just (TPunct p) -> p `elem` ["(", "[", "{"]
  Just TEnd -> False
  Nothing -> False
  Just _ -> True

primary :: Int -> P (Term, Int)
primary maxP = do
  t <- next
  case t of
    TIntT i -> return (Int i, 0)
    TFltT d -> return (Flt d, 0)
    TVarT n -> do v <- varFor n; return (v, 0)
    TStrT s -> return (charList s, 0)
    TBackq s -> return (mkList [Int (fromIntegral (ord c)) | c <- s] (Atom "[]"), 0)
    TPunct "(" -> do
      (x, _) <- term 1200
      expect (TPunct ")")
      return (x, 0)
    TPunct "[" -> do
      mt <- peek
      if mt == Just (TPunct "]")
        then advance >> return (Atom "[]", 0)
        else do
          items <- argList
          mt2 <- peek
          tl <- if mt2 == Just (TPunct "|")
                  then advance >> (fst <$> term 999)
                  else return (Atom "[]")
          expect (TPunct "]")
          return (mkList items tl, 0)
    TPunct "{" -> do
      mt <- peek
      if mt == Just (TPunct "}")
        then advance >> return (Atom "{}", 0)
        else do
          (x, _) <- term 1200
          expect (TPunct "}")
          return (Comp "{}" [x], 0)
    TFunct n -> do
      expect (TPunct "(")
      args <- argList
      expect (TPunct ")")
      return (Comp n args, 0)
    TName n -> do
      mt <- peek
      case (n, mt) of
        ("-", Just (TIntT i)) -> advance >> return (Int (negate i), 0)
        ("-", Just (TFltT d)) -> advance >> return (Flt (negate d), 0)
        _ -> case M.lookup n prefixOps of
          Just (p, pa) | canStart mt -> do
            mt2 <- peek2
            -- an operator followed by an infix operator is an atom: (- = x)
            let isAtomUse = case (mt, mt2) of
                  (Just (TName m), _) | M.member m infixOps && not (M.member m prefixOps) -> True
                  _ -> False
            if isAtomUse
              then return (Atom n, 0)
              else do
                let p' = min p maxP
                    argMax = case pa of
                      FY -> p'
                      FX -> p' - 1
                (arg, _) <- term argMax
                return (Comp n [arg], p')
          _ -> return (Atom n, 0)
    TPunct p -> failP ("unexpected " ++ show p)
    TEnd -> failP "unexpected end of clause"

argList :: P [Term]
argList = do
  (x, _) <- term 999
  mt <- peek
  if mt == Just (TPunct ",")
    then advance >> (x :) <$> argList
    else return [x]

-- | Read one clause term; returns Nothing at end of input.
readClauseTerm :: P (Maybe (Term, M.Map String Int, Int))
readClauseTerm = do
  mt <- peek
  case mt of
    Nothing -> return Nothing
    Just _ -> do
      P $ \s -> Right ((), s { psVars = M.empty, psNext = 0 })
      (t, _) <- term 1200
      expect TEnd
      P $ \s -> Right (Just (t, psVars s, psNext s), s)

readAll :: P [(Term, M.Map String Int, Int)]
readAll = do
  m <- readClauseTerm
  case m of
    Nothing -> return []
    Just x -> (x :) <$> readAll

parseTerms :: String -> Either String [(Term, M.Map String Int, Int)]
parseTerms src = do
  toks <- lexer 1 src
  fst <$> runP readAll (PS toks M.empty 0)

-- | Parse a whole program.  Directives are kept separately and ignored by
-- the engines.
parseProgram :: String -> Either String Program
parseProgram src = do
  ts <- parseTerms src
  let step (cls, dirs) (t, _, n) = case t of
        Comp ":-" [d] -> (cls, dirs ++ [d])
        Comp "?-" [d] -> (cls, dirs ++ [d])
        Comp ":-" [h, b] -> (cls ++ [Clause h (bodyVarsToCall b) n], dirs)
        Comp "-->" _ -> (cls, dirs ++ [t])
        h -> (cls ++ [Clause h (Atom "true") n], dirs)
      (clauses, directives) = foldl step ([], []) ts
  mapM_ checkHead clauses
  let p = programFromClauses clauses
  return p { progDirectives = directives }
  where
    checkHead c
      | isCallable (clHead c) = Right ()
      | otherwise = Left ("clause head is not callable: " ++ show (clHead c))

-- | A variable used as a goal means call/1.
bodyVarsToCall :: Term -> Term
bodyVarsToCall t = case t of
  Var _ _ -> Comp "call" [t]
  Comp op [a, b] | op `elem` [",", ";", "->", "*->"] ->
    Comp op [bodyVarsToCall a, bodyVarsToCall b]
  Comp "\\+" [a] -> Comp "\\+" [bodyVarsToCall a]
  _ -> t

-- | Parse a single term (no final full stop needed).  Returns the term,
-- the named variables and the number of variables used.
parseTermString :: String -> Either String (Term, [(String, Term)], Int)
parseTermString src = do
  let src' = dropWhileEnd' isSpace src
      withDot = if not (null src') && last src' == '.' then src' ++ "\n" else src' ++ " .\n"
  ts <- parseTerms withDot
  case ts of
    [(t, vm, n)] -> Right (t, [ (k, Var i k) | (k, i) <- sortOnSnd (M.toList vm) ], n)
    _ -> Left "expected exactly one term"
  where
    sortOnSnd = map snd . M.toList . M.fromList . map (\(k, i) -> (i, (k, i)))
    dropWhileEnd' p = reverse . dropWhile p . reverse

-- | Parse a query; a variable goal becomes call/1.
parseQuery :: String -> Either String (Term, [(String, Term)], Int)
parseQuery src = do
  (t, vs, n) <- parseTermString src
  return (bodyVarsToCall t, vs, n)
