-- | The detlog2 interpreter: a choicepointless, cutless interpreter of
-- Prolog.
--
-- Every goal denotes an /answer packet/: a lazy list of answers (and the
-- output they write).  Conjunction splices the packet of the second goal
-- into every answer of the first; a disjunction or a predicate with several
-- clauses concatenates the packets of its alternatives.  Alternatives are
-- therefore ordinary data that is spliced deterministically:
--
--   * there is no choicepoint stack and no backtracking - failure is the
--     empty packet;
--   * there is no trail - substitutions are immutable, so nothing has to be
--     undone;
--   * there is no cut - '!' is rejected with an error.  Commitment is
--     expressed with if_commit/3 (or the equivalent (C -> T ; E)), once/1
--     and \+/1, which take the head of the condition's packet and never
--     demand the rest.
--
-- Because packets are lazy, only the answers that are actually needed are
-- ever computed, so a query can take the first answer of an infinite
-- generator.
module Detlog2.Interp
  ( Options(..)
  , defaultOptions
  , solveGoal
  , runGoal
  , cutMessage
  , appendS
  , bindS
  ) where

import qualified Data.IntSet as IS
import qualified Data.Map.Strict as M
import Detlog2.Builtins
import Detlog2.Parser
import Detlog2.Term

data Options = Options
  { optMaxDepth :: Int      -- ^ maximum call depth before an error is raised
  , optDetCheck :: Bool     -- ^ every predicate call must give at most one answer
  , optWatch :: [Int]       -- ^ symbolic inputs: variables that stand for unknown values
  }

defaultOptions :: Options
defaultOptions = Options { optMaxDepth = 100000, optDetCheck = False, optWatch = [] }

cutMessage :: String
cutMessage =
  "cut (!) is not supported by the detlog2 interpreter; convert the program \
  \first with `detlog2 convert`, which turns cuts into if_commit/3 decisions"

data Ctx = Ctx
  { cxProg :: Program
  , cxOpts :: Options
  }

-- | Splice the packet of a continuation into every answer of a packet.
bindS :: Stream -> (State -> Stream) -> Stream
bindS [] _ = []
bindS (Out o : r) k = Out o : bindS r k
bindS (Err e : _) _ = [Err e]
bindS (Ans s : r) k = appendS (k s) (bindS r k)

-- | Concatenate two packets; an error ends the packet.
appendS :: Stream -> Stream -> Stream
appendS [] ys = ys
appendS (Err e : _) _ = [Err e]
appendS (x : xs) ys = x : appendS xs ys

runGoal :: Options -> Program -> Term -> Int -> Stream
runGoal opts prog goal nvars = solveGoal opts prog goal (emptyState nvars)

solveGoal :: Options -> Program -> Term -> State -> Stream
solveGoal opts prog goal st = solve (Ctx prog opts) 0 goal st

solve :: Ctx -> Int -> Term -> State -> Stream
solve cx depth g0 st = case walk st g0 of
  Var _ _ -> instErr "call/1"
  Atom "true" -> [Ans st]
  Atom "fail" -> []
  Atom "false" -> []
  Atom "!" -> [Err cutMessage]
  Comp "," [a, b] -> bindS (go a st) (go b)
  Comp ";" [Comp "->" [c, t], e] -> commit c t e
  Comp ";" [Comp "*->" [c, t], e] -> softCommit c t e
  Comp ";" [a, b] -> appendS (go a st) (go b st)
  Comp "->" [c, t] -> commit c t (Atom "fail")
  Comp "*->" [c, t] -> bindS (go c st) (go t)
  Comp "if_commit" [c, t, e] -> commit c t e
  Comp "once" [x] -> commit x (Atom "true") (Atom "fail")
  Comp "once_det" [x] -> commit x (Atom "true") (Atom "fail")
  Comp "ignore" [x] -> commit x (Atom "true") (Atom "true")
  Comp "\\+" [x] -> negation x
  Comp "not" [x] -> negation x
  Comp "decision" [cases, def] -> case termToList st cases of
    Just cs -> go (decisionGoal cs def) st
    Nothing -> instErr "decision/2"
  Comp "call" (x : extra) -> case addArgs (walk st x) extra of
    Just g' -> go g' st
    Nothing -> typeErr "callable" (resolve st x)
  Comp "findall" [t, x, l] -> findallS t x l (Atom "[]")
  Comp "findall" [t, x, l, tl] -> findallS t x l tl
  Comp "forall" [c, a] -> negation (Comp "," [c, Comp "\\+" [a]])
  Comp "aggregate_all" [spec, x, r] -> aggregate spec x r
  Comp "bagof" [t, x, l] -> collect False t x l
  Comp "setof" [t, x, l] -> collect True t x l
  g@(Atom f) -> call g f []
  g@(Comp f as) -> call g f as
  t -> typeErr "callable" t
  where
    go = solve cx depth

    -- Commitment: the head of the condition's packet, the rest is never
    -- demanded.  No choicepoint is created or removed.
    commit c t e = scan (go c st)
      where
        scan [] = go e st
        scan (Out o : r) = Out o : scan r
        scan (Err x : _) = [Err x]
        scan (Ans s : _) = go t s

    softCommit c t e = scan (go c st)
      where
        scan [] = go e st
        scan (Out o : r) = Out o : scan r
        scan (Err x : _) = [Err x]
        scan s@(Ans _ : _) = bindS s (go t)

    negation x = scan (go x st)
      where
        scan [] = [Ans st]
        scan (Out o : r) = Out o : scan r
        scan (Err e : _) = [Err e]
        scan (Ans _ : _) = []

    -- Collect a packet into a list term.
    gather t x k = loop [] (go x st)
      where
        loop acc [] = k (reverse acc)
        loop acc (Out o : r) = Out o : loop acc r
        loop _ (Err e : _) = [Err e]
        loop acc (Ans s : r) = loop ((resolve s t, stNext s) : acc) r

    finishList items st0 =
      let st1 = st0 { stNext = maximum (stNext st0 : map snd items) }
          copyAll s [] = ([], s)
          copyAll s (y : ys) = let (c, s1) = copyTerm s y
                                   (cs, s2) = copyAll s1 ys
                               in (c : cs, s2)
      in copyAll st1 (map fst items)

    findallS t x l tl = gather t x $ \items ->
      let (copies, st1) = finishList items st
      in maybe [] (\s -> [Ans s]) (unify l (mkList copies tl) st1)

    collect sorted t x l =
      let inner = stripCaret x
      in gather t inner $ \items ->
           if null items then [] else
             let (copies, st1) = finishList items st
                 out = if sorted then sortDedup st1 copies else copies
             in maybe [] (\s -> [Ans s]) (unify l (mkList out (Atom "[]")) st1)

    aggregate spec x r = case walk st spec of
      Atom "count" -> gather (Atom "x") x $ \items ->
        maybe [] (\s -> [Ans s]) (unify r (Int (fromIntegral (length items))) st)
      Comp "count" [t] -> gather t x $ \items ->
        maybe [] (\s -> [Ans s]) (unify r (Int (fromIntegral (length items))) st)
      Comp "sum" [e] -> gather e x $ \items ->
        case mapM (evalArith st . fst) items of
          Left err -> [Err err]
          Right vs -> let total = foldl addN (NI 0) vs
                      in maybe [] (\s -> [Ans s]) (unify r (numTerm total) st)
      Comp "max" [e] -> gather e x $ \items ->
        case mapM (evalArith st . fst) items of
          Left err -> [Err err]
          Right [] -> []
          Right (v : vs) -> maybe [] (\s -> [Ans s]) (unify r (numTerm (foldl maxN v vs)) st)
      Comp "min" [e] -> gather e x $ \items ->
        case mapM (evalArith st . fst) items of
          Left err -> [Err err]
          Right [] -> []
          Right (v : vs) -> maybe [] (\s -> [Ans s]) (unify r (numTerm (foldl minN v vs)) st)
      Comp "bag" [t] -> findallS t x r (Atom "[]")
      Comp "set" [t] -> gather t x $ \items ->
        let (copies, st1) = finishList items st
        in maybe [] (\s -> [Ans s]) (unify r (mkList (sortDedup st1 copies) (Atom "[]")) st1)
      s -> typeErr "aggregate_all/3 specification" s

    call g f as
      | not (null (optWatch (cxOpts cx))) && watchedUse f as =
          [Err ("symbolic run: " ++ f ++ "/" ++ show (length as)
                ++ " inspects an input variable, so its result could differ for actual values")]
      | otherwise = case builtin f as st of
          Just s -> s
          Nothing -> callUser g (f, length as)

    -- In a symbolic run, a built-in whose result depends on whether an
    -- input variable is bound (or on its value) would decide for every
    -- input what it decided for the unbound variable.  Type tests are
    -- unsafe on a watched variable itself; comparisons on any term that
    -- contains one.
    watchedUse f as =
      let watched = IS.fromList [ i | v <- optWatch (cxOpts cx), Var i _ <- [walk st (Var v "")] ]
          isWatched t = case walk st t of
            Var i _ -> IS.member i watched
            _ -> False
          contains t = any (`IS.member` watched) (IS.toList (termVarIds (resolve st t)))
          key = (f, length as)
      in if key `elem` typeTests then any isWatched as
         else key `elem` varSensitiveKeys && any contains as
    typeTests = [ ("var", 1), ("nonvar", 1), ("atom", 1), ("number", 1), ("integer", 1), ("float", 1)
                , ("atomic", 1), ("compound", 1), ("callable", 1), ("is_list", 1) ]

    callUser g key
      | depth >= optMaxDepth (cxOpts cx) =
          [Err ("call depth limit (" ++ show (optMaxDepth (cxOpts cx)) ++ ") exceeded in "
                ++ fst key ++ "/" ++ show (snd key))]
      | otherwise = case M.lookup key (progPreds (cxProg cx)) of
          Nothing -> [Err ("unknown procedure " ++ fst key ++ "/" ++ show (snd key))]
          Just cls ->
            let packets = foldr (\c rest -> appendS (tryClause g c) rest) [] cls
            in if optDetCheck (cxOpts cx) then detOnly key packets else packets

    tryClause g (Clause h b nv) =
      let off = stNext st
          st1 = st { stNext = off + nv }
      in case unify (renameTerm off h) g st1 of
           Nothing -> []
           Just st2 -> solve cx (depth + 1) (renameTerm off b) st2

detOnly :: (String, Int) -> Stream -> Stream
detOnly (f, n) = loop False
  where
    loop _ [] = []
    loop seen (Ans s : r)
      | seen = [Err ("determinism check: " ++ f ++ "/" ++ show n
                     ++ " gave a second answer, so it would need a choicepoint")]
      | otherwise = Ans s : loop True r
    loop seen (e : r) = e : loop seen r

decisionGoal :: [Term] -> Term -> Term
decisionGoal [] def = def
decisionGoal (Comp "-" [c, b] : rest) def = Comp "if_commit" [c, b, decisionGoal rest def]
decisionGoal (other : _) _ = Comp "throw_decision" [other]

stripCaret :: Term -> Term
stripCaret (Comp "^" [_, g]) = stripCaret g
stripCaret g = g

sortDedup :: State -> [Term] -> [Term]
sortDedup st xs = dd (msortBy xs)
  where
    msortBy = foldr insert []
    insert x [] = [x]
    insert x (y : ys) = case compareStd st x y of
      GT -> y : insert x ys
      _ -> x : y : ys
    dd (a : b : rest) | compareStd st a b == EQ && resolve st a == resolve st b = dd (a : rest)
                      | otherwise = a : dd (b : rest)
    dd ys = ys

addN, maxN, minN :: NumV -> NumV -> NumV
addN (NI a) (NI b) = NI (a + b)
addN a b = NF (dbl a + dbl b)
maxN a b = if dbl a >= dbl b then a else b
minN a b = if dbl a <= dbl b then a else b

dbl :: NumV -> Double
dbl (NI i) = fromIntegral i
dbl (NF d) = d
