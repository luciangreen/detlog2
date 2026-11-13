-- | Printing terms and clauses as re-readable Prolog text.
module Detlog2.Pretty
  ( showTerm
  , showTermQ
  , showTermWith
  , showClause
  , showClauses
  , showProgram
  , quoteAtom
  , showAnswerTerm
  , clauseTerm
  , showSourceTerm
  ) where

import Data.Char
import Data.List (intercalate)
import qualified Data.IntMap.Strict as IM
import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Term
import Detlog2.Parser

-- | Variable naming function.
type Namer = Int -> String -> String

defaultNamer :: Namer
defaultNamer i _ = "_G" ++ show i

-- | Print with quoting (writeq style).
showTermQ :: Term -> String
showTermQ = showTermWith True defaultNamer

-- | Print without quoting (write style).
showTerm :: Term -> String
showTerm = showTermWith False defaultNamer

showTermWith :: Bool -> Namer -> Term -> String
showTermWith q nm t = pr 1200 t ""
  where
    pr :: Int -> Term -> ShowS
    pr _ (Var i n) = showString (nm i n)
    pr _ (Int i) = shows i
    pr _ (Flt d) = showString (showFloat d)
    pr p (Atom a)
      | M.member a infixOps || M.member a prefixOps =
          if p < 1200 && q then showString "(" . atomS a . showString ")" else atomS a
      | otherwise = atomS a
    pr _ t'@(Comp "." [_, _]) = showList' t'
    pr _ (Comp "{}" [x]) = showString "{" . pr 1200 x . showString "}"
    pr p (Comp f [l, r])
      | Just (op, a) <- M.lookup f infixOps =
          let (la, ra) = case a of
                XFX -> (op - 1, op - 1)
                XFY -> (op - 1, op)
                YFX -> (op, op - 1)
              sep = case f of
                "," -> showString ", "
                _ | all isAlpha f -> showString (" " ++ f ++ " ")
                  | otherwise -> showString (" " ++ atomQ f ++ " ")
              body = prArg la l . sep . prArg ra r
          in if op > p then showString "(" . body . showString ")" else body
    pr p (Comp "\\+" [x]) =
      let body = showString "\\+ " . prArg 900 x
      in if 900 > p then showString "(" . body . showString ")" else body
    pr _ (Comp f as) =
      atomS f . showString "(" . commaSep (map (prArg 999) as) . showString ")"
    -- arguments that are negative numbers need care after operators
    prArg p x@(Int i) | i < 0 && p < 999 = showString "(" . pr p x . showString ")"
    prArg p x@(Flt d) | d < 0 && p < 999 = showString "(" . pr p x . showString ")"
    prArg p x = pr p x
    commaSep [] = id
    commaSep [x] = x
    commaSep (x:xs) = x . showString ", " . commaSep xs
    atomS a = showString (if q then quoteAtom a else a)
    atomQ a = if q then quoteAtom a else a
    showList' l =
      let (items, tl) = collect l
      in showString "[" . commaSep (map (prArg 999) items)
         . (case tl of
              Atom "[]" -> id
              _ -> showString "|" . prArg 999 tl)
         . showString "]"
    collect (Comp "." [h, tl]) = let (xs, e) = collect tl in (h : xs, e)
    collect e = ([], e)

showFloat :: Double -> String
showFloat d =
  let s = show d
  in if 'e' `elem` s && not ('.' `elem` takeWhile (/= 'e') s)
       then let (m, e) = break (== 'e') s in m ++ ".0" ++ e
       else s

-- | Quote an atom when needed so that it reads back as the same atom.
quoteAtom :: String -> String
quoteAtom a
  | a `elem` ["[]", "{}", "!", ";", ","] = if a == "," then "','" else a
  | not (null a) && isLower (head a) && all (\c -> isAlphaNum c || c == '_') a = a
  | not (null a) && all (`elem` "+-*/\\^<>=~:.?@#&$") a = a
  | otherwise = "'" ++ concatMap esc a ++ "'"
  where
    esc '\'' = "\\'"
    esc '\\' = "\\\\"
    esc '\n' = "\\n"
    esc '\t' = "\\t"
    esc c = [c]

-- | Print an answer term: variables are shown as _A, _B, ... in order of
-- first occurrence so that answers compare up to renaming.
showAnswerTerm :: Term -> String
showAnswerTerm t =
  let vs = [ i | Var i _ <- termVarsOrdered t ]
      table = IM.fromList (zip vs [0 :: Int ..])
      nm i _ = "_" ++ letterName (IM.findWithDefault 0 i table)
  in showTermWith True nm t

letterName :: Int -> String
letterName k
  | k < 26 = [chr (ord 'A' + k)]
  | otherwise = chr (ord 'A' + k `mod` 26) : show (k `div` 26)

-- | Choose clause variable names: source names when unique, singletons as _.
clauseNamer :: Term -> Namer
clauseNamer t =
  let occs = countVars t IM.empty
      ordered = termVarsOrdered t
      assign (used, m) (Var i n)
        | IM.findWithDefault 0 i occs == 1 = (used, IM.insert i "_" m)
        | validName n && not (Set.member n used) = (Set.insert n used, IM.insert i n m)
        | otherwise =
            let base = if validName n then n else "V"
                cand = head [ c | k <- [1 :: Int ..], let c = base ++ show k
                                , not (Set.member c used) ]
            in (Set.insert cand used, IM.insert i cand m)
      assign acc _ = acc
      (_, names) = foldl assign (Set.empty, IM.empty) ordered
  in \i _ -> IM.findWithDefault ("_G" ++ show i) i names
  where
    validName n = not (null n) && (isUpper (head n)) && all (\c -> isAlphaNum c || c == '_') n
    countVars (Var i _) m = IM.insertWith (+) i (1 :: Int) m
    countVars (Comp _ as) m = foldl (flip countVars) m as
    countVars _ m = m

clauseTerm :: Clause -> Term
clauseTerm (Clause h (Atom "true") _) = h
clauseTerm (Clause h b _) = Comp ":-" [h, b]

-- | Pretty-print one clause with an indented body.
showClause :: Clause -> String
showClause c =
  let nm = clauseNamer (clauseTerm c)
      st = showTermWith True nm
  in case clBody c of
       Atom "true" -> st (clHead c) ++ "."
       b -> st (clHead c) ++ " :-\n" ++ body nm 1 b ++ "."

body :: Namer -> Int -> Term -> String
body nm ind g = intercalate ",\n" (map (goal nm ind) (conjList' g))
  where
    conjList' (Comp "," [a, b]) = conjList' a ++ conjList' b
    conjList' x = [x]

goal :: Namer -> Int -> Term -> String
goal nm ind g = case g of
  Comp ";" [Comp "->" [c, t], e] ->
    pad ind ++ "(   " ++ inner c ++ "\n" ++ pad ind ++ "->  " ++ inner t
      ++ elseChain e ++ "\n" ++ pad ind ++ ")"
  Comp ";" [a, b] ->
    pad ind ++ "(   " ++ inner a ++ "\n" ++ pad ind ++ ";   " ++ inner b
      ++ "\n" ++ pad ind ++ ")"
  Comp "if_commit" [c, t, e] ->
    pad ind ++ "if_commit(\n" ++ block c ++ ",\n"
      ++ block t ++ ",\n" ++ block e ++ "\n"
      ++ pad ind ++ ")"
  _ -> pad ind ++ showTermWith True nm g
  where
    pad k = replicate (4 * k) ' '
    -- a conjunction argument must stay one argument when read back
    block x = case x of
      Comp "," _ -> pad (ind + 1) ++ "(   " ++ dropWhile (== ' ') (body nm (ind + 2) x)
                      ++ "\n" ++ pad (ind + 1) ++ ")"
      _ -> body nm (ind + 1) x
    inner x = dropWhile (== ' ') (body nm (ind + 1) x)
    elseChain e = case e of
      Comp ";" [Comp "->" [c2, t2], e2] ->
        "\n" ++ pad ind ++ ";   " ++ inner c2 ++ "\n" ++ pad ind ++ "->  " ++ inner t2
          ++ elseChain e2
      _ -> "\n" ++ pad ind ++ ";   " ++ inner e

showClauses :: [Clause] -> String
showClauses = concatMap (\c -> showClause c ++ "\n")

showProgram :: Program -> String
showProgram p =
  intercalate "\n" [ showClauses cs | (_, cs) <- programClauses p ]

-- | Print with the variables' source names (for reports).
showSourceTerm :: Term -> String
showSourceTerm = showTermWith True (\i n -> if null n || n == "_" then "_G" ++ show i else n)
