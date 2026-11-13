-- | Terms, substitutions and unification for detlog2.
--
-- Substitutions are immutable maps.  Nothing is ever undone: a failed
-- unification simply produces no new state, so the interpreter needs no
-- trail and no choicepoint stack.
module Detlog2.Term
  ( Term(..)
  , State(..)
  , emptyState
  , walk
  , resolve
  , unify
  , mkList
  , termToList
  , partialList
  , charList
  , termVarIds
  , termVarsOrdered
  , renameTerm
  , maxVarId
  , copyTerm
  , freshVar
  , isCallable
  , goalKey
  , goalArgs
  , addArgs
  , conjList
  , mkConj
  , isVar
  , variant
  , compareStd
  ) where

import qualified Data.IntMap.Strict as IM
import qualified Data.IntSet as IS
import Data.List (foldl')

-- | A Prolog term.  Variables carry an id and a display name.
data Term
  = Var !Int String
  | Atom String
  | Int !Integer
  | Flt !Double
  | Comp String [Term]
  deriving (Show)

instance Eq Term where
  Var a _ == Var b _ = a == b
  Atom a == Atom b = a == b
  Int a == Int b = a == b
  Flt a == Flt b = a == b
  Comp f as == Comp g bs = f == g && as == bs
  _ == _ = False

-- | An answer state: the bindings made so far and the next fresh variable id.
data State = State
  { stSub  :: !(IM.IntMap Term)
  , stNext :: !Int
  }

emptyState :: Int -> State
emptyState n = State IM.empty n

walk :: State -> Term -> Term
walk st t@(Var i _) = case IM.lookup i (stSub st) of
  Just t' -> walk st t'
  Nothing -> t
walk _ t = t

-- | Fully dereference a term.
resolve :: State -> Term -> Term
resolve st t = case walk st t of
  Comp f as -> Comp f (map (resolve st) as)
  t' -> t'

-- | Unification without occurs check (as in standard Prolog).
unify :: Term -> Term -> State -> Maybe State
unify a b st = go (walk st a) (walk st b)
  where
    go (Var i _) (Var j _) | i == j = Just st
    go (Var i _) t = Just (bind i t)
    go t (Var j _) = Just (bind j t)
    go (Atom x) (Atom y) | x == y = Just st
    go (Int x) (Int y) | x == y = Just st
    go (Flt x) (Flt y) | x == y = Just st
    go (Comp f as) (Comp g bs)
      | f == g && length as == length bs = unifyArgs as bs st
    go _ _ = Nothing
    bind i t = st { stSub = IM.insert i t (stSub st) }

unifyArgs :: [Term] -> [Term] -> State -> Maybe State
unifyArgs [] [] st = Just st
unifyArgs (x:xs) (y:ys) st = unify x y st >>= unifyArgs xs ys
unifyArgs _ _ _ = Nothing

mkList :: [Term] -> Term -> Term
mkList xs tl = foldr (\h t -> Comp "." [h, t]) tl xs

-- | A proper list (after dereferencing), or Nothing.
termToList :: State -> Term -> Maybe [Term]
termToList st t = case walk st t of
  Atom "[]" -> Just []
  Comp "." [h, tl] -> (walk st h :) <$> termToList st tl
  _ -> Nothing

-- | Elements of a (possibly partial) list plus its dereferenced tail.
partialList :: State -> Term -> ([Term], Term)
partialList st t = case walk st t of
  Comp "." [h, tl] -> let (xs, end) = partialList st tl in (walk st h : xs, end)
  end -> ([], end)

-- | A string as a list of one-character atoms (double_quotes = chars).
charList :: String -> Term
charList s = mkList [Atom [c] | c <- s] (Atom "[]")

termVarIds :: Term -> IS.IntSet
termVarIds (Var i _) = IS.singleton i
termVarIds (Comp _ as) = IS.unions (map termVarIds as)
termVarIds _ = IS.empty

-- | Variables in order of first occurrence (left to right, depth first).
termVarsOrdered :: Term -> [Term]
termVarsOrdered t = reverse (snd (go t (IS.empty, [])))
  where
    go v@(Var i _) acc@(seen, out)
      | IS.member i seen = acc
      | otherwise = (IS.insert i seen, v : out)
    go (Comp _ as) acc = foldl' (flip go) acc as
    go _ acc = acc

renameTerm :: Int -> Term -> Term
renameTerm off (Var i n) = Var (i + off) n
renameTerm off (Comp f as) = Comp f (map (renameTerm off) as)
renameTerm _ t = t

maxVarId :: Term -> Int
maxVarId (Var i _) = i
maxVarId (Comp _ as) = foldl' max (-1) (map maxVarId as)
maxVarId _ = -1

freshVar :: String -> State -> (Term, State)
freshVar n st = (Var (stNext st) n, st { stNext = stNext st + 1 })

-- | copy_term/2: resolve, then rename every unbound variable freshly.
copyTerm :: State -> Term -> (Term, State)
copyTerm st t0 =
  let t = resolve st t0
      vs = IS.toList (termVarIds t)
      base = stNext st
      table = IM.fromList (zip vs [base ..])
      ren (Var i n) = Var (IM.findWithDefault i i table) n
      ren (Comp f as) = Comp f (map ren as)
      ren x = x
  in (ren t, st { stNext = base + length vs })

isVar :: Term -> Bool
isVar (Var _ _) = True
isVar _ = False

isCallable :: Term -> Bool
isCallable (Atom _) = True
isCallable (Comp _ _) = True
isCallable _ = False

goalKey :: Term -> Maybe (String, Int)
goalKey (Atom a) = Just (a, 0)
goalKey (Comp f as) = Just (f, length as)
goalKey _ = Nothing

goalArgs :: Term -> [Term]
goalArgs (Comp _ as) = as
goalArgs _ = []

addArgs :: Term -> [Term] -> Maybe Term
addArgs g [] = Just g
addArgs (Atom a) xs = Just (Comp a xs)
addArgs (Comp f as) xs = Just (Comp f (as ++ xs))
addArgs _ _ = Nothing

conjList :: Term -> [Term]
conjList (Comp "," [a, b]) = conjList a ++ conjList b
conjList (Atom "true") = []
conjList t = [t]

mkConj :: [Term] -> Term
mkConj [] = Atom "true"
mkConj [g] = g
mkConj (g:gs) = Comp "," [g, mkConj gs]

-- | Structural equivalence up to consistent variable renaming (=@=).
variant :: State -> Term -> Term -> Bool
variant st a b = go (resolve st a) (resolve st b) IM.empty IM.empty /= Nothing
  where
    go (Var i _) (Var j _) m1 m2 =
      case (IM.lookup i m1, IM.lookup j m2) of
        (Nothing, Nothing) -> Just (IM.insert i j m1, IM.insert j i m2)
        (Just j', Just i') | j' == j && i' == i -> Just (m1, m2)
        _ -> Nothing
    go (Comp f as) (Comp g bs) m1 m2
      | f == g && length as == length bs = goArgs as bs m1 m2
    go x y m1 m2
      | isVar x || isVar y = Nothing
      | x == y = Just (m1, m2)
      | otherwise = Nothing
    goArgs [] [] m1 m2 = Just (m1, m2)
    goArgs (x:xs) (y:ys) m1 m2 = go x y m1 m2 >>= \(n1, n2) -> goArgs xs ys n1 n2
    goArgs _ _ _ _ = Nothing

-- | Standard order of terms: Var < Number < Atom < Compound.
compareStd :: State -> Term -> Term -> Ordering
compareStd st a b = cmp (walk st a) (walk st b)
  where
    rank (Var _ _) = 0 :: Int
    rank (Flt _) = 1
    rank (Int _) = 1
    rank (Atom _) = 3
    rank (Comp _ _) = 4
    cmp (Var i _) (Var j _) = compare i j
    cmp (Int x) (Int y) = compare x y
    cmp (Flt x) (Flt y) = compare x y
    cmp (Int x) (Flt y) = case compare (fromIntegral x) y of
      EQ -> GT
      o -> o
    cmp (Flt x) (Int y) = case compare x (fromIntegral y) of
      EQ -> LT
      o -> o
    cmp (Atom x) (Atom y) = compare x y
    cmp (Comp f as) (Comp g bs) =
      compare (length as) (length bs)
        <> compare f g
        <> mconcat (zipWith (\x y -> compareStd st x y) as bs)
    cmp x y = compare (rank x) (rank y)
