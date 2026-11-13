-- | Built-in predicates shared by both engines, and the Detlog runtime
-- (member_cp/2, splice/2, splice_extend/4, ...).
--
-- A built-in returns an answer stream: a lazy list of events.  A
-- deterministic built-in returns at most one answer; generators such as
-- between/3 return several.  Streams are data, never choicepoints.
module Detlog2.Builtins
  ( Ev(..)
  , Stream
  , builtin
  , isBuiltinKey
  , controlKeys
  , detlogRuntimeKeys
  , evalArith
  , NumV(..)
  , numTerm
  , answers
  , typeErr
  , instErr
  , formatString
  , effectKeys
  , varSensitiveKeys
  , nondetBuiltinKeys
  ) where

import Data.Bits
import Data.Char
import Data.List (sortBy, isPrefixOf)
import qualified Data.Map.Strict as M
import Detlog2.Term
import Detlog2.Pretty

-- | One event of an answer stream.
data Ev
  = Out String        -- text written by write/1 and friends
  | Ans State         -- an answer
  | Err String        -- an error; the stream stops here

type Stream = [Ev]

answers :: Stream -> [State]
answers s = [ st | Ans st <- s ]

ok :: State -> Stream
ok st = [Ans st]

fromMaybeU :: Maybe State -> Stream
fromMaybeU = maybe [] ok

instErr :: String -> Stream
instErr ctx = [Err ("instantiation error in " ++ ctx)]

typeErr :: String -> Term -> Stream
typeErr ty t = [Err ("type error: expected " ++ ty ++ ", got " ++ showTermQ t)]

-- | Control constructs are handled by the engines, not here.
controlKeys :: [(String, Int)]
controlKeys =
  [ (",", 2), (";", 2), ("->", 2), ("*->", 2), ("\\+", 1), ("call", 1)
  , ("true", 0), ("fail", 0), ("false", 0), ("!", 0), ("once", 1)
  , ("ignore", 1), ("findall", 3), ("findall", 4), ("forall", 2)
  , ("if_commit", 3), ("once_det", 1), ("decision", 2), ("not", 1)
  , ("aggregate_all", 3), ("bagof", 3), ("setof", 3)
  ] ++ [ ("call", n) | n <- [2 .. 8] ]

-- | The Detlog runtime constructs available to converted code.
detlogRuntimeKeys :: [(String, Int)]
detlogRuntimeKeys =
  [ ("member_cp", 2), ("between_cp", 3), ("cp_rows", 2), ("splice", 2)
  , ("splice_first", 2), ("splice_extend", 4), ("rows_concat", 2)
  , ("cp_filter", 3), ("splice_safe", 1), ("memo_lookup", 3), ("memo_miss", 2)
  ]

-- | Built-ins with side effects (output).
effectKeys :: [(String, Int)]
effectKeys =
  [ ("write", 1), ("print", 1), ("writeln", 1), ("writeq", 1)
  , ("write_canonical", 1), ("nl", 0), ("tab", 1), ("format", 1), ("format", 2)
  , ("put_char", 1)
  ]

-- | Built-ins whose result depends on whether arguments are bound.
varSensitiveKeys :: [(String, Int)]
varSensitiveKeys =
  [ ("var", 1), ("nonvar", 1), ("==", 2), ("\\==", 2), ("@<", 2), ("@>", 2)
  , ("@=<", 2), ("@>=", 2), ("compare", 3), ("copy_term", 2), ("\\=", 2)
  , ("ground", 1), ("=@=", 2), ("\\=@=", 2), ("msort", 2), ("sort", 2)
  , ("atom", 1), ("number", 1), ("integer", 1), ("float", 1), ("atomic", 1)
  , ("compound", 1), ("callable", 1), ("is_list", 1)
  ]

-- | Built-ins that may produce more than one answer.
nondetBuiltinKeys :: [(String, Int)]
nondetBuiltinKeys =
  [ ("between", 3), ("length", 2), ("sub_atom", 5), ("arg", 3)
  , ("atomic_list_concat", 3), ("clause", 2) ]

builtinTable :: M.Map (String, Int) ([Term] -> State -> Stream)
builtinTable = M.fromList
  [ (("=", 2), \[a, b] st -> fromMaybeU (unify a b st))
  , (("\\=", 2), \[a, b] st -> maybe (ok st) (const []) (unify a b st))
  , (("==", 2), \[a, b] st -> if compareStd st a b == EQ && sameVars st a b then ok st else [])
  , (("\\==", 2), \[a, b] st -> if compareStd st a b == EQ && sameVars st a b then [] else ok st)
  , (("@<", 2), cmpStd (== LT))
  , (("@>", 2), cmpStd (== GT))
  , (("@=<", 2), cmpStd (/= GT))
  , (("@>=", 2), cmpStd (/= LT))
  , (("=@=", 2), \[a, b] st -> if variant st a b then ok st else [])
  , (("\\=@=", 2), \[a, b] st -> if variant st a b then [] else ok st)
  , (("compare", 3), \[o, a, b] st ->
        let r = case compareStd st a b of
                  LT -> "<"
                  EQ -> if sameVars st a b then "=" else "<"
                  GT -> ">"
        in fromMaybeU (unify o (Atom r) st))
  , (("is", 2), \[r, e] st -> withNum st e (\v -> fromMaybeU (unify r (numTerm v) st)))
  , (("=:=", 2), arithCmp (== EQ))
  , (("=\\=", 2), arithCmp (/= EQ))
  , (("<", 2), arithCmp (== LT))
  , ((">", 2), arithCmp (== GT))
  , (("=<", 2), arithCmp (/= GT))
  , ((">=", 2), arithCmp (/= LT))
  , (("succ", 2), succB)
  , (("plus", 3), plusB)
  , (("var", 1), typeTest isVar)
  , (("nonvar", 1), typeTest (not . isVar))
  , (("atom", 1), typeTest (\t -> case t of Atom _ -> True; _ -> False))
  , (("number", 1), typeTest (\t -> case t of Int _ -> True; Flt _ -> True; _ -> False))
  , (("integer", 1), typeTest (\t -> case t of Int _ -> True; _ -> False))
  , (("float", 1), typeTest (\t -> case t of Flt _ -> True; _ -> False))
  , (("atomic", 1), typeTest (\t -> case t of Atom _ -> True; Int _ -> True; Flt _ -> True; _ -> False))
  , (("compound", 1), typeTest (\t -> case t of Comp _ _ -> True; _ -> False))
  , (("callable", 1), typeTest isCallable)
  , (("is_list", 1), \[a] st -> maybe [] (const (ok st)) (termToList st a))
  , (("ground", 1), \[a] st -> if null (termVarsOrdered (resolve st a)) then ok st else [])
  , (("functor", 3), functorB)
  , (("arg", 3), argB)
  , (("=..", 2), univB)
  , (("copy_term", 2), \[a, b] st -> let (c, st') = copyTerm st a in fromMaybeU (unify b c st'))
  , (("atom_chars", 2), textB "atom_chars" (map (\c -> Atom [c])) fromChar)
  , (("atom_codes", 2), textB "atom_codes" (map (Int . fromIntegral . ord)) fromCode)
  , (("char_code", 2), charCodeB)
  , (("atom_length", 2), atomLengthB)
  , (("number_codes", 2), numberTextB (map (Int . fromIntegral . ord)) fromCode)
  , (("number_chars", 2), numberTextB (map (\c -> Atom [c])) fromChar)
  , (("atom_number", 2), atomNumberB)
  , (("atom_string", 2), \[a, s] st -> textB "atom_string" (map (\c -> Atom [c])) fromChar [a, s] st)
  , (("string_chars", 2), \[s, cs] st -> fromMaybeU (unify s cs st))
  , (("string_concat", 3), \[a, b, c] st -> appendText st a b c)
  , (("atom_concat", 3), \[a, b, c] st -> atomConcatB st a b c)
  , (("upcase_atom", 2), caseB toUpper)
  , (("downcase_atom", 2), caseB toLower)
  , (("sub_atom", 5), subAtomB)
  , (("atomic_list_concat", 2), \[l, a] st -> atomicListConcat st l (Atom "") a)
  , (("atomic_list_concat", 3), \[l, sep, a] st -> atomicListConcat st l sep a)
  , (("term_to_atom", 2), \[t, a] st -> fromMaybeU (unify a (Atom (showTermQ (resolve st t))) st))
  , (("length", 2), lengthB)
  , (("between", 3), betweenB)
  , (("msort", 2), \[l, s] st -> sortB False st l s)
  , (("sort", 2), \[l, s] st -> sortB True st l s)
  , (("write", 1), \[a] st -> [Out (showTerm (resolve st a)), Ans st])
  , (("print", 1), \[a] st -> [Out (showTermQ (resolve st a)), Ans st])
  , (("writeq", 1), \[a] st -> [Out (showTermQ (resolve st a)), Ans st])
  , (("write_canonical", 1), \[a] st -> [Out (showTermQ (resolve st a)), Ans st])
  , (("writeln", 1), \[a] st -> [Out (showTerm (resolve st a) ++ "\n"), Ans st])
  , (("nl", 0), \_ st -> [Out "\n", Ans st])
  , (("tab", 1), \[n] st -> withNum st n (\v -> case v of
                                 NI k -> [Out (replicate (fromIntegral k) ' '), Ans st]
                                 _ -> typeErr "integer" n))
  , (("put_char", 1), \[c] st -> case walk st c of
                                   Atom [ch] -> [Out [ch], Ans st]
                                   t -> typeErr "character" t)
  , (("format", 1), \[f] st -> formatB st f (Atom "[]"))
  , (("format", 2), \[f, as] st -> formatB st f as)
  , (("format", 3), formatToB)
  -- Detlog runtime ---------------------------------------------------------
  , (("member_cp", 2), \[x, l] st -> case termToList st l of
                                       Just _ -> fromMaybeU (unify x (Comp "cp" [l]) st)
                                       Nothing -> [Err ("member_cp/2: not a proper list: " ++ showTermQ (resolve st l))])
  , (("between_cp", 3), betweenCpB)
  , (("cp_rows", 2), cpRowsB)
  , (("splice", 2), spliceB)
  , (("splice_first", 2), \[ts, row] st -> case spliceRows st ts of
                                             Left e -> [Err e]
                                             Right (r:_) -> fromMaybeU (unify row r st)
                                             Right [] -> [])
  , (("splice_extend", 4), spliceExtendB)
  , (("rows_concat", 2), rowsConcatB)
  , (("cp_filter", 3), \[p, pat, out] st -> case walk st p of
                                              Comp "cp" [rows] -> spliceExtendB [rows, pat, pat, out] st
                                              t -> typeErr "choice packet cp/1" t)
  , (("splice_safe", 1), spliceSafeB)
  , (("memo_lookup", 3), memoLookupB)
  , (("memo_miss", 2), \[k, a] st -> [Err ("memo_miss: " ++ showTermQ (resolve st k)
                                           ++ " was memoised as complete, but has no entry for "
                                           ++ showTermQ (resolve st a))])
  ]

isBuiltinKey :: (String, Int) -> Bool
isBuiltinKey k = M.member k builtinTable

builtin :: String -> [Term] -> State -> Maybe Stream
builtin f as st = case M.lookup (f, length as) builtinTable of
  Just impl -> Just (impl as st)
  Nothing -> Nothing

-- ---------------------------------------------------------------------------
-- Helpers

sameVars :: State -> Term -> Term -> Bool
sameVars st a b = resolve st a == resolve st b

cmpStd :: (Ordering -> Bool) -> [Term] -> State -> Stream
cmpStd p [a, b] st = if p (compareStd st a b) then ok st else []
cmpStd _ _ _ = []

typeTest :: (Term -> Bool) -> [Term] -> State -> Stream
typeTest p [a] st = if p (walk st a) then ok st else []
typeTest _ _ _ = []

-- ---------------------------------------------------------------------------
-- Arithmetic

data NumV = NI Integer | NF Double

numTerm :: NumV -> Term
numTerm (NI i) = Int i
numTerm (NF d) = Flt d

toD :: NumV -> Double
toD (NI i) = fromIntegral i
toD (NF d) = d

withNum :: State -> Term -> (NumV -> Stream) -> Stream
withNum st e k = case evalArith st e of
  Left err -> [Err err]
  Right v -> k v

arithCmp :: (Ordering -> Bool) -> [Term] -> State -> Stream
arithCmp p [a, b] st =
  withNum st a $ \x -> withNum st b $ \y -> if p (cmpNum x y) then ok st else []
arithCmp _ _ _ = []

cmpNum :: NumV -> NumV -> Ordering
cmpNum (NI a) (NI b) = compare a b
cmpNum a b = compare (toD a) (toD b)

evalArith :: State -> Term -> Either String NumV
evalArith st t0 = case walk st t0 of
  Int i -> Right (NI i)
  Flt d -> Right (NF d)
  Var _ _ -> Left "instantiation error in arithmetic"
  Atom "pi" -> Right (NF pi)
  Atom "e" -> Right (NF (exp 1))
  Atom "inf" -> Right (NF (1 / 0))
  Atom "max_tagged_integer" -> Right (NI ((2 :: Integer) ^ (60 :: Int) - 1))
  Atom [c] -> Right (NI (fromIntegral (ord c)))
  Atom a -> Left ("type error: evaluable " ++ a ++ "/0")
  Comp "." [x, Atom "[]"] -> evalArith st x
  Comp f [x] -> evalArith st x >>= un f
  Comp f [x, y] -> do
    a <- evalArith st x
    b <- evalArith st y
    bin f a b
  t -> Left ("type error: evaluable " ++ showTermQ t)
  where
    un f v = case (f, v) of
      ("-", NI a) -> Right (NI (negate a))
      ("-", NF a) -> Right (NF (negate a))
      ("+", _) -> Right v
      ("abs", NI a) -> Right (NI (abs a))
      ("abs", NF a) -> Right (NF (abs a))
      ("sign", NI a) -> Right (NI (signum a))
      ("sign", NF a) -> Right (NF (signum a))
      ("min", _) -> Left "min/1"
      ("float", _) -> Right (NF (toD v))
      ("integer", NI a) -> Right (NI a)
      ("integer", NF a) -> Right (NI (round a))
      ("float_integer_part", _) -> Right (NF (fromIntegral (truncate (toD v) :: Integer)))
      ("truncate", _) -> Right (NI (truncate (toD v)))
      ("floor", _) -> Right (NI (floor (toD v)))
      ("ceiling", _) -> Right (NI (ceiling (toD v)))
      ("round", _) -> Right (NI (round (toD v)))
      ("sqrt", _) -> Right (NF (sqrt (toD v)))
      ("exp", _) -> Right (NF (exp (toD v)))
      ("log", _) -> Right (NF (log (toD v)))
      ("log2", _) -> Right (NF (logBase 2 (toD v)))
      ("sin", _) -> Right (NF (sin (toD v)))
      ("cos", _) -> Right (NF (cos (toD v)))
      ("tan", _) -> Right (NF (tan (toD v)))
      ("atan", _) -> Right (NF (atan (toD v)))
      ("\\", NI a) -> Right (NI (complement a))
      ("msb", NI a) | a > 0 -> Right (NI (fromIntegral (integerLog2 a)))
      ("succ", NI a) -> Right (NI (a + 1))
      _ -> Left ("type error: evaluable " ++ f ++ "/1")
    bin f a b = case (f, a, b) of
      ("+", NI x, NI y) -> Right (NI (x + y))
      ("-", NI x, NI y) -> Right (NI (x - y))
      ("*", NI x, NI y) -> Right (NI (x * y))
      ("+", _, _) -> Right (NF (toD a + toD b))
      ("-", _, _) -> Right (NF (toD a - toD b))
      ("*", _, _) -> Right (NF (toD a * toD b))
      ("/", NI _, NI 0) -> Left "evaluation error: zero_divisor"
      ("/", NI x, NI y) | x `mod` y == 0 -> Right (NI (x `div` y))
      ("/", _, _) -> Right (NF (toD a / toD b))
      ("//", NI _, NI 0) -> Left "evaluation error: zero_divisor"
      ("//", NI x, NI y) -> Right (NI (x `quot` y))
      ("div", NI _, NI 0) -> Left "evaluation error: zero_divisor"
      ("div", NI x, NI y) -> Right (NI (x `div` y))
      ("mod", NI _, NI 0) -> Left "evaluation error: zero_divisor"
      ("mod", NI x, NI y) -> Right (NI (x `mod` y))
      ("rem", NI _, NI 0) -> Left "evaluation error: zero_divisor"
      ("rem", NI x, NI y) -> Right (NI (x `rem` y))
      ("min", _, _) -> Right (if cmpNum a b == GT then b else a)
      ("max", _, _) -> Right (if cmpNum a b == LT then b else a)
      ("**", NI x, NI y) | y >= 0 -> Right (NI (x ^ y))
      ("**", _, _) -> Right (NF (toD a ** toD b))
      ("^", NI x, NI y)
        | y >= 0 -> Right (NI (x ^ y))
        | x == 1 -> Right (NI 1)
        | x == -1 -> Right (NI (if even y then 1 else -1))
        | otherwise -> Left "^/2: negative exponent"
      ("^", _, _) -> Right (NF (toD a ** toD b))
      (">>", NI x, NI y) -> Right (NI (shiftR x (fromIntegral y)))
      ("<<", NI x, NI y) -> Right (NI (shiftL x (fromIntegral y)))
      ("/\\", NI x, NI y) -> Right (NI (x .&. y))
      ("\\/", NI x, NI y) -> Right (NI (x .|. y))
      ("xor", NI x, NI y) -> Right (NI (xor x y))
      ("gcd", NI x, NI y) -> Right (NI (gcd x y))
      ("atan2", _, _) -> Right (NF (atan2 (toD a) (toD b)))
      ("atan", _, _) -> Right (NF (atan2 (toD a) (toD b)))
      ("log", _, _) -> Right (NF (logBase (toD a) (toD b)))
      ("truncate", _, _) -> Left "truncate/2"
      _ -> Left ("type error: evaluable " ++ f ++ "/2")

integerLog2 :: Integer -> Int
integerLog2 n = go 0 n
  where go k m = if m <= 1 then k else go (k + 1) (m `div` 2)

succB :: [Term] -> State -> Stream
succB [a, b] st = case (walk st a, walk st b) of
  (Int x, _) | x >= 0 -> fromMaybeU (unify b (Int (x + 1)) st)
  (Var _ _, Int y) | y > 0 -> fromMaybeU (unify a (Int (y - 1)) st)
                   | otherwise -> []
  (Var _ _, Var _ _) -> instErr "succ/2"
  (x, _) -> typeErr "not_less_than_zero" x
succB _ _ = []

plusB :: [Term] -> State -> Stream
plusB [a, b, c] st = case (walk st a, walk st b, walk st c) of
  (Int x, Int y, _) -> fromMaybeU (unify c (Int (x + y)) st)
  (Int x, _, Int z) -> fromMaybeU (unify b (Int (z - x)) st)
  (_, Int y, Int z) -> fromMaybeU (unify a (Int (z - y)) st)
  _ -> instErr "plus/3"
plusB _ _ = []

-- ---------------------------------------------------------------------------
-- Term construction

functorB :: [Term] -> State -> Stream
functorB [t, n, a] st = case walk st t of
  Var _ _ -> case (walk st n, walk st a) of
    (name, Int 0) | not (isVar name) -> fromMaybeU (unify t name st)
    (Atom name, Int k) | k > 0 ->
      let (vs, st') = freshN (fromIntegral k) st
      in fromMaybeU (unify t (Comp name vs) st')
    _ -> instErr "functor/3"
  Comp f as -> fromMaybeU (unify n (Atom f) st >>= unify a (Int (fromIntegral (length as))))
  x -> fromMaybeU (unify n x st >>= unify a (Int 0))
functorB _ _ = []

freshN :: Int -> State -> ([Term], State)
freshN 0 st = ([], st)
freshN k st = let (v, st1) = freshVar "_" st
                  (vs, st2) = freshN (k - 1) st1
              in (v : vs, st2)

argB :: [Term] -> State -> Stream
argB [n, t, a] st = case walk st t of
  Comp _ as -> case walk st n of
    Int k | k >= 1 && fromIntegral k <= length as -> fromMaybeU (unify a (as !! (fromIntegral k - 1)) st)
          | otherwise -> []
    Var _ _ -> concat [ fromMaybeU (unify n (Int i) st >>= unify a x) | (i, x) <- zip [1 ..] as ]
    x -> typeErr "integer" x
  x -> typeErr "compound" x
argB _ _ = []

univB :: [Term] -> State -> Stream
univB [t, l] st = case walk st t of
  Comp f as -> fromMaybeU (unify l (mkList (Atom f : as) (Atom "[]")) st)
  Var _ _ -> case termToList st l of
    Just [x] -> fromMaybeU (unify t x st)
    Just (Atom f : as) -> fromMaybeU (unify t (Comp f as) st)
    _ -> instErr "=../2"
  x -> fromMaybeU (unify l (mkList [x] (Atom "[]")) st)
univB _ _ = []

-- ---------------------------------------------------------------------------
-- Text

-- | The text of an atomic term.
textOf :: State -> Term -> Maybe String
textOf st t = case walk st t of
  Atom a -> Just a
  Int i -> Just (show i)
  Flt d -> Just (showTerm (Flt d))
  x -> case termToList st x of
    Just items -> mapM charOf items
    Nothing -> Nothing
  where
    charOf (Atom [c]) = Just c
    charOf (Int c) = Just (chr (fromIntegral c))
    charOf _ = Nothing

fromChar :: State -> Term -> Maybe Char
fromChar st t = case walk st t of
  Atom [c] -> Just c
  _ -> Nothing

fromCode :: State -> Term -> Maybe Char
fromCode st t = case walk st t of
  Int c -> Just (chr (fromIntegral c))
  _ -> Nothing

textB :: String -> (String -> [Term]) -> (State -> Term -> Maybe Char)
      -> [Term] -> State -> Stream
textB name enc dec [a, l] st = case walk st a of
  Var _ _ -> case termToList st l of
    Just items -> case mapM (dec st) items of
      Just s -> fromMaybeU (unify a (Atom s) st)
      Nothing -> instErr name
    Nothing -> instErr name
  _ -> case textOf st a of
    Just s -> fromMaybeU (unify l (mkList (enc s) (Atom "[]")) st)
    Nothing -> typeErr "atomic" (resolve st a)
textB _ _ _ _ _ = []

numberTextB :: (String -> [Term]) -> (State -> Term -> Maybe Char) -> [Term] -> State -> Stream
numberTextB enc dec [n, l] st = case walk st n of
  Var _ _ -> case termToList st l >>= mapM (dec st) of
    Just s -> case parseNumber s of
      Just v -> fromMaybeU (unify n v st)
      Nothing -> [Err ("syntax error: illegal number " ++ show s)]
    Nothing -> instErr "number_codes/2"
  Int i -> fromMaybeU (unify l (mkList (enc (show i)) (Atom "[]")) st)
  Flt d -> fromMaybeU (unify l (mkList (enc (showTerm (Flt d))) (Atom "[]")) st)
  x -> typeErr "number" x
numberTextB _ _ _ _ = []

parseNumber :: String -> Maybe Term
parseNumber s0 =
  let s = dropWhile isSpace s0
  in case s of
       ('-':rest) -> neg <$> parseNumber rest
       _ | not (null s) && all isDigit s -> Just (Int (read s))
         | otherwise -> case break (== '.') s of
             (a, '.':b) | not (null a) && all isDigit a && not (null b) && all isDigit b ->
               Just (Flt (read (a ++ "." ++ b)))
             _ -> Nothing
  where
    neg (Int i) = Int (negate i)
    neg (Flt d) = Flt (negate d)
    neg t = t

atomNumberB :: [Term] -> State -> Stream
atomNumberB [a, n] st = case walk st a of
  Atom s -> case parseNumber s of
    Just v -> fromMaybeU (unify n v st)
    Nothing -> []
  Var _ _ -> case walk st n of
    Int i -> fromMaybeU (unify a (Atom (show i)) st)
    Flt d -> fromMaybeU (unify a (Atom (showTerm (Flt d))) st)
    _ -> instErr "atom_number/2"
  x -> typeErr "atom" x
atomNumberB _ _ = []

charCodeB :: [Term] -> State -> Stream
charCodeB [c, k] st = case (walk st c, walk st k) of
  (Atom [ch], _) -> fromMaybeU (unify k (Int (fromIntegral (ord ch))) st)
  (Var _ _, Int i) -> fromMaybeU (unify c (Atom [chr (fromIntegral i)]) st)
  _ -> instErr "char_code/2"
charCodeB _ _ = []

atomLengthB :: [Term] -> State -> Stream
atomLengthB [a, n] st = case textOf st a of
  Just s | not (isVar (walk st a)) -> fromMaybeU (unify n (Int (fromIntegral (length s))) st)
  _ -> instErr "atom_length/2"
atomLengthB _ _ = []

appendText :: State -> Term -> Term -> Term -> Stream
appendText st a b c = case (textOf st a, textOf st b) of
  (Just x, Just y) | not (isVar (walk st a)) && not (isVar (walk st b)) ->
    fromMaybeU (unify c (charList (x ++ y)) st)
  _ -> instErr "string_concat/3"

atomConcatB :: State -> Term -> Term -> Term -> Stream
atomConcatB st a b c = case (walk st a, walk st b) of
  (x, y) | not (isVar x) && not (isVar y) -> case (textOf st x, textOf st y) of
    (Just s1, Just s2) -> fromMaybeU (unify c (Atom (s1 ++ s2)) st)
    _ -> typeErr "atomic" x
  _ -> case textOf st c of
    Just s | not (isVar (walk st c)) ->
      concat [ fromMaybeU (unify a (Atom (take i s)) st >>= unify b (Atom (drop i s)))
             | i <- [0 .. length s] ]
    _ -> instErr "atom_concat/3"

caseB :: (Char -> Char) -> [Term] -> State -> Stream
caseB f [a, b] st = case textOf st a of
  Just s | not (isVar (walk st a)) -> fromMaybeU (unify b (Atom (map f s)) st)
  _ -> instErr "upcase_atom/2"
caseB _ _ _ = []

subAtomB :: [Term] -> State -> Stream
subAtomB [a, b, l, af, sub] st = case textOf st a of
  Just s | not (isVar (walk st a)) ->
    let n = length s
        cands = case textOf st sub of
          Just t | not (isVar (walk st sub)) ->
            [ (i, length t) | i <- [0 .. n - length t], t `isPrefixOf` drop i s ]
          _ -> [ (i, k) | i <- [0 .. n], k <- [0 .. n - i] ]
    in concat
         [ fromMaybeU (unify b (Int (fromIntegral i)) st
                       >>= unify l (Int (fromIntegral k))
                       >>= unify af (Int (fromIntegral (n - i - k)))
                       >>= unify sub (Atom (take k (drop i s))))
         | (i, k) <- cands ]
  _ -> instErr "sub_atom/5"
subAtomB _ _ = []

atomicListConcat :: State -> Term -> Term -> Term -> Stream
atomicListConcat st l sep a = case termToList st l >>= mapM (\x -> if isVar (walk st x) then Nothing else textOf st x) of
  Just parts -> case textOf st sep of
    Just s -> fromMaybeU (unify a (Atom (joinWith s parts)) st)
    Nothing -> instErr "atomic_list_concat/3"
  Nothing -> case (textOf st sep, textOf st a) of
    (Just s, Just whole) | not (null s) && not (isVar (walk st a)) ->
      fromMaybeU (unify l (mkList (map Atom (splitOn s whole)) (Atom "[]")) st)
    _ -> instErr "atomic_list_concat/3"
  where
    joinWith _ [] = ""
    joinWith _ [x] = x
    joinWith s (x:xs) = x ++ s ++ joinWith s xs

splitOn :: String -> String -> [String]
splitOn sep s = go s ""
  where
    go [] acc = [reverse acc]
    go str@(c:cs) acc
      | sep `isPrefixOf` str = reverse acc : go (drop (length sep) str) ""
      | otherwise = go cs (c : acc)

-- ---------------------------------------------------------------------------
-- Lists and generators

lengthB :: [Term] -> State -> Stream
lengthB [l, n] st =
  let (items, end) = partialList st l
  in case end of
       Atom "[]" -> fromMaybeU (unify n (Int (fromIntegral (length items))) st)
       Var _ _ -> case walk st n of
         Int k | k >= fromIntegral (length items) ->
           let (vs, st') = freshN (fromIntegral k - length items) st
           in fromMaybeU (unify end (mkList vs (Atom "[]")) st')
               | otherwise -> []
         Var _ _ ->
           [ Ans s'
           | k <- [length items ..]
           , let (vs, s1) = freshN (k - length items) st
           , Just s' <- [unify end (mkList vs (Atom "[]")) s1
                         >>= unify n (Int (fromIntegral k))] ]
         x -> typeErr "integer" x
       x -> typeErr "list" x
lengthB _ _ = []

betweenB :: [Term] -> State -> Stream
betweenB [lo, hi, x] st = case (evalArith st lo, walk st hi) of
  (Right (NI l), Atom "inf") -> gen l Nothing
  (Right (NI l), Atom "infinite") -> gen l Nothing
  (Right (NI l), _) -> case evalArith st hi of
    Right (NI h) -> case walk st x of
      Int v -> if l <= v && v <= h then ok st else []
      Var _ _ -> gen l (Just h)
      t -> typeErr "integer" t
    _ -> instErr "between/3"
  _ -> instErr "between/3"
  where
    gen l mh = case walk st x of
      Int v -> if l <= v && maybe True (v <=) mh then ok st else []
      _ -> [ Ans st' | v <- maybe [l ..] (\h -> [l .. h]) mh
                     , Just st' <- [unify x (Int v) st] ]
betweenB _ _ = []

sortB :: Bool -> State -> Term -> Term -> Stream
sortB dedup st l s = case termToList st l of
  Just items ->
    let sorted = sortBy (compareStd st) items
        out = if dedup then dd sorted else sorted
        dd (a:b:rest) | compareStd st a b == EQ = dd (a : rest)
                      | otherwise = a : dd (b : rest)
        dd xs = xs
    in fromMaybeU (unify s (mkList out (Atom "[]")) st)
  Nothing -> instErr "sort/2"

-- ---------------------------------------------------------------------------
-- format/2

formatB :: State -> Term -> Term -> Stream
formatB st f as = case formatString st f as of
  Left e -> [Err e]
  Right s -> [Out s, Ans st]

formatToB :: [Term] -> State -> Stream
formatToB [sink, f, as] st = case formatString st f as of
  Left e -> [Err e]
  Right s -> case walk st sink of
    Comp "atom" [a] -> fromMaybeU (unify a (Atom s) st)
    Comp "string" [a] -> fromMaybeU (unify a (charList s) st)
    Comp "chars" [a] -> fromMaybeU (unify a (charList s) st)
    Comp "codes" [a] -> fromMaybeU (unify a (mkList [Int (fromIntegral (ord c)) | c <- s] (Atom "[]")) st)
    t -> typeErr "format sink" t
formatToB _ _ = []

formatString :: State -> Term -> Term -> Either String String
formatString st f as = do
  fmt <- maybe (Left "format/2: bad format") Right (textOf st f)
  let args = case termToList st as of
        Just xs -> xs
        Nothing -> [as]
  go fmt args
  where
    go [] _ = Right ""
    go ('~':c:rest) args = case c of
      'w' -> arg args (\x r -> (showTerm (resolve st x) ++) <$> go rest r)
      'p' -> arg args (\x r -> (showTermQ (resolve st x) ++) <$> go rest r)
      'q' -> arg args (\x r -> (showTermQ (resolve st x) ++) <$> go rest r)
      'a' -> arg args (\x r -> (showTerm (resolve st x) ++) <$> go rest r)
      'd' -> arg args (\x r -> (showTerm (resolve st x) ++) <$> go rest r)
      's' -> arg args (\x r -> (maybe "" id (textOf st x) ++) <$> go rest r)
      'n' -> ("\n" ++) <$> go rest args
      '~' -> ("~" ++) <$> go rest args
      _ -> Left ("format/2: unsupported directive ~" ++ [c])
    go (ch:rest) args = (ch :) <$> go rest args
    arg (x:xs) k = k x xs
    arg [] _ = Left "format/2: not enough arguments"

-- ---------------------------------------------------------------------------
-- Detlog runtime

betweenCpB :: [Term] -> State -> Stream
betweenCpB [lo, hi, p] st = case (evalArith st lo, evalArith st hi) of
  (Right (NI l), Right (NI h)) ->
    fromMaybeU (unify p (Comp "cp" [mkList (map Int [l .. h]) (Atom "[]")]) st)
  _ -> [Err "between_cp/3: needs integer bounds (an infinite packet cannot be spliced)"]
betweenCpB _ _ = []

-- | cp(L) -> [[E1], [E2], ...]: a packet as one-column rows.
cpRowsB :: [Term] -> State -> Stream
cpRowsB [p, rows] st = case walk st p of
  Comp "cp" [l] -> case termToList st l of
    Just xs -> fromMaybeU (unify rows (mkList [mkList [x] (Atom "[]") | x <- flatten st xs] (Atom "[]")) st)
    Nothing -> typeErr "list" (resolve st l)
  t -> typeErr "choice packet cp/1" t
cpRowsB _ _ = []

-- | Nested packets are spliced inline: cp([1, cp([2,3])]) offers 1, 2, 3.
flatten :: State -> [Term] -> [Term]
flatten st = concatMap one
  where
    one x = case walk st x of
      Comp "cp" [l] | Just ys <- termToList st l -> flatten st ys
      y -> [y]

-- | The choices offered by one splice position.
choicesOf :: State -> Term -> Either String [Term]
choicesOf st t = case walk st t of
  Comp "cp" [l] -> case termToList st l of
    Just xs -> Right (flatten st xs)
    Nothing -> Left ("splice/2: packet is not a proper list: " ++ showTermQ (resolve st l))
  x -> Right [x]

-- | Deterministic Cartesian product in left-to-right Prolog order.
spliceRows :: State -> Term -> Either String [Term]
spliceRows st ts = case termToList st ts of
  Nothing -> Left "splice/2: first argument must be a proper list"
  Just positions -> do
    cs <- mapM (choicesOf st) positions
    return [ mkList row (Atom "[]") | row <- product' cs ]
  where
    product' [] = [[]]
    product' (c:cs) = let rest = product' cs in [ x : r | x <- c, r <- rest ]

spliceB :: [Term] -> State -> Stream
spliceB [ts, rows] st = case spliceRows st ts of
  Left e -> [Err e]
  Right rs -> fromMaybeU (unify rows (mkList rs (Atom "[]")) st)
spliceB _ _ = []

-- | splice_extend(+Rows, +Env, +Pattern, -Out): for every row, take a fresh
-- copy of Env-Pattern, unify the Pattern copy with the row, and keep the
-- Env copy when that succeeds.  This is how an answer packet is spliced
-- into the environment of the goal that asked for it.
spliceExtendB :: [Term] -> State -> Stream
spliceExtendB [rows, env, pat, out] st = case termToList st rows of
  Nothing -> [Err ("splice_extend/4: rows are not a proper list: " ++ showTermQ (resolve st rows))]
  Just rs ->
    let pair = Comp "-" [env, pat]
        step (acc, s) r =
          let (c, s1) = copyTerm s pair
          in case c of
               Comp "-" [e', p'] -> case unify p' r s1 of
                 Just s2 -> (resolve s2 e' : acc, s2 { stSub = stSub s1 })
                 Nothing -> (acc, s1)
               _ -> (acc, s1)
        (outs, st') = foldl step ([], st) rs
    in fromMaybeU (unify out (mkList (reverse outs) (Atom "[]")) st')
spliceExtendB _ _ = []

rowsConcatB :: [Term] -> State -> Stream
rowsConcatB [ls, out] st = case termToList st ls >>= mapM (termToList st) of
  Just parts -> fromMaybeU (unify out (mkList (concat parts) (Atom "[]")) st)
  Nothing -> [Err ("rows_concat/2: expected a list of proper lists: " ++ showTermQ (resolve st ls))]
rowsConcatB _ _ = []

-- | True when the argument groups share no unbound variables, so that
-- their packets can be computed independently and spliced.
spliceSafeB :: [Term] -> State -> Stream
spliceSafeB [gs] st = case termToList st gs of
  Just groups ->
    let sets = map (\g -> [ i | Var i _ <- termVarsOrdered (resolve st g) ]) groups
        disjoint [] = True
        disjoint (s:ss) = all (\t -> all (`notElem` t) s) ss && disjoint ss
    in if disjoint sets then ok st else []
  Nothing -> []
spliceSafeB _ _ = []

-- | memo_lookup(+Args, +Table, -Rows): Table is [[Pattern, Rows], ...];
-- the first entry whose pattern is a variant of Args gives a copy of its rows.
memoLookupB :: [Term] -> State -> Stream
memoLookupB [args, table, rows] st = case termToList st table of
  Just entries -> go entries
  Nothing -> typeErr "memo table" (resolve st table)
  where
    go [] = []
    go (e:es) = case termToList st e of
      Just [pat, rs] | variant st pat args ->
        let (c, st') = copyTerm st rs in fromMaybeU (unify rows c st')
      _ -> go es
memoLookupB _ _ = []
