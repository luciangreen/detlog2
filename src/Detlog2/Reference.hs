-- | A reference engine with ordinary Prolog cut semantics.
--
-- detlog2's own interpreter ("Detlog2.Interp") has no cut.  This engine is
-- used only as an oracle: to check that converted code gives the same
-- answers, in the same order, as the source program (which may contain
-- cuts), and to compute memo tables for "Detlog2.Memo".
--
-- An answer carries a flag saying whether a cut was executed on the way to
-- it; once such an answer has been seen, the remaining alternatives of the
-- clause (and of the predicate) are dropped.
module Detlog2.Reference (refRun, refSolve) where

import qualified Data.Map.Strict as M
import Detlog2.Builtins
import Detlog2.Interp (Options(..))
import Detlog2.Parser
import Detlog2.Term

data R = RAns Bool State | ROut String | RErr String

refRun :: Options -> Program -> Term -> Int -> Stream
refRun opts prog g nv = refSolve opts prog g (emptyState nv)

refSolve :: Options -> Program -> Term -> State -> Stream
refSolve opts prog g st = map toEv (solveR prog opts 0 g st)
  where
    toEv (RAns _ s) = Ans s
    toEv (ROut o) = Out o
    toEv (RErr e) = Err e

-- | Run a goal opaque to cut (call/1, \+, findall, conditions).
opaque :: [R] -> [R]
opaque = map strip
  where
    strip (RAns _ s) = RAns False s
    strip x = x

bindR :: [R] -> (State -> [R]) -> [R]
bindR [] _ = []
bindR (ROut o : r) k = ROut o : bindR r k
bindR (RErr e : _) _ = [RErr e]
bindR (RAns c s : r) k
  | c = markCut (k s)                     -- a cut was passed: no alternatives of the left goal
  | otherwise = appendStop (k s) (bindR r k)
  where
    markCut = map (\x -> case x of
                           RAns _ s' -> RAns True s'
                           y -> y)

-- | Append, unless the first packet passed a cut.
appendStop :: [R] -> [R] -> [R]
appendStop [] ys = ys
appendStop (RErr e : _) _ = [RErr e]
appendStop (x@(RAns True _) : xs) _ = x : dropAfterCut xs
appendStop (x : xs) ys = x : appendStop xs ys

dropAfterCut :: [R] -> [R]
dropAfterCut [] = []
dropAfterCut (RErr e : _) = [RErr e]
dropAfterCut (x : xs) = x : dropAfterCut xs

fromStream :: Stream -> [R]
fromStream = map f
  where
    f (Ans s) = RAns False s
    f (Out o) = ROut o
    f (Err e) = RErr e

solveR :: Program -> Options -> Int -> Term -> State -> [R]
solveR prog opts depth g0 st = case walk st g0 of
  Var _ _ -> [RErr "instantiation error in call/1"]
  Atom "true" -> [RAns False st]
  Atom "fail" -> []
  Atom "false" -> []
  Atom "!" -> [RAns True st]
  Comp "," [a, b] -> bindR (go a st) (go b)
  Comp ";" [Comp "->" [c, t], e] -> commit c t e
  Comp ";" [Comp "*->" [c, t], e] -> case opaque (go c st) of
    [] -> go e st
    s -> bindR s (go t)
  Comp ";" [a, b] -> appendStop (go a st) (go b st)
  Comp "->" [c, t] -> commit c t (Atom "fail")
  Comp "*->" [c, t] -> bindR (opaque (go c st)) (go t)
  Comp "if_commit" [c, t, e] -> commit c t e
  Comp "once" [x] -> commit x (Atom "true") (Atom "fail")
  Comp "once_det" [x] -> commit x (Atom "true") (Atom "fail")
  Comp "ignore" [x] -> commit x (Atom "true") (Atom "true")
  Comp "\\+" [x] -> neg x
  Comp "not" [x] -> neg x
  Comp "call" (x : extra) -> case addArgs (walk st x) extra of
    Just g' -> opaque (go g' st)
    Nothing -> [RErr "type error: callable"]
  Comp "decision" _ -> viaInterp
  Comp "findall" _ -> viaInterp
  Comp "forall" [c, a] -> neg (Comp "," [c, Comp "\\+" [a]])
  Comp "aggregate_all" _ -> viaInterp
  Comp "bagof" _ -> viaInterp
  Comp "setof" _ -> viaInterp
  g@(Atom f) -> call g f []
  g@(Comp f as) -> call g f as
  _ -> [RErr "type error: callable"]
  where
    go = solveR prog opts depth

    -- Meta built-ins whose inner goals are opaque to cut: rewrite the inner
    -- goal through this engine by temporarily treating it as a call.
    viaInterp = case walk st g0 of
      Comp "findall" (t : x : rest) -> collectWith t x (\items st1 ->
        let tl = case rest of
                   [l, tl'] -> Just (l, tl')
                   [l] -> Just (l, Atom "[]")
                   _ -> Nothing
        in case tl of
             Just (l, tl') -> maybe [] (\s -> [RAns False s]) (unify l (mkList items tl') st1)
             Nothing -> [RErr "findall arity"])
      Comp "decision" [cases, def] -> case termToList st cases of
        Just cs -> go (decisionGoal cs def) st
        Nothing -> [RErr "instantiation error in decision/2"]
      Comp "aggregate_all" [spec, x, r] -> case walk st spec of
        Atom "count" -> collectWith (Atom "x") x (\items st1 ->
          maybe [] (\s -> [RAns False s]) (unify r (Int (fromIntegral (length items))) st1))
        Comp "bag" [t] -> collectWith t x (\items st1 ->
          maybe [] (\s -> [RAns False s]) (unify r (mkList items (Atom "[]")) st1))
        _ -> [RErr "aggregate_all/3: only count and bag(T) are supported by the reference engine"]
      Comp f [t, x, l] | f == "bagof" || f == "setof" -> collectWith t (stripCaret x) (\items st1 ->
        if null items then [] else
          let out = if f == "setof" then sortDedup st1 items else items
          in maybe [] (\s -> [RAns False s]) (unify l (mkList out (Atom "[]")) st1))
      _ -> [RErr "unsupported meta call"]

    collectWith t x k = loop [] (opaque (go x st))
      where
        loop acc [] =
          let next' = maximum (stNext st : map snd acc)
              st0 = st { stNext = next' }
              (items, st1) = copyAll st0 (reverse (map fst acc))
          in k items st1
        loop acc (ROut o : r) = ROut o : loop acc r
        loop _ (RErr e : _) = [RErr e]
        loop acc (RAns _ s : r) = loop ((resolve s t, stNext s) : acc) r
        copyAll s [] = ([], s)
        copyAll s (y : ys) = let (c, s1) = copyTerm s y
                                 (cs, s2) = copyAll s1 ys
                             in (c : cs, s2)

    commit c t e = scan (go c st)
      where
        scan [] = go e st
        scan (ROut o : r) = ROut o : scan r
        scan (RErr x : _) = [RErr x]
        scan (RAns _ s : _) = go t s

    neg x = scan (go x st)
      where
        scan [] = [RAns False st]
        scan (ROut o : r) = ROut o : scan r
        scan (RErr e : _) = [RErr e]
        scan (RAns _ _ : _) = []

    call g f as = case builtin f as st of
      Just s -> fromStream s
      Nothing -> callUser g (f, length as)

    callUser g key
      | depth >= optMaxDepth opts =
          [RErr ("call depth limit exceeded in " ++ fst key ++ "/" ++ show (snd key))]
      | otherwise = case M.lookup key (progPreds prog) of
          Nothing -> [RErr ("unknown procedure " ++ fst key ++ "/" ++ show (snd key))]
          Just cls -> opaque (foldr (\c rest -> appendStop (tryClause g c) rest) [] cls)

    tryClause g (Clause h b nv) =
      let off = stNext st
          st1 = st { stNext = off + nv }
      in case unify (renameTerm off h) g st1 of
           Nothing -> []
           Just st2 -> solveR prog opts (depth + 1) (renameTerm off b) st2

decisionGoal :: [Term] -> Term -> Term
decisionGoal [] def = def
decisionGoal (Comp "-" [c, b] : rest) def = Comp "if_commit" [c, b, decisionGoal rest def]
decisionGoal (other : _) _ = Comp "throw_decision" [other]

stripCaret :: Term -> Term
stripCaret (Comp "^" [_, g]) = stripCaret g
stripCaret g = g

sortDedup :: State -> [Term] -> [Term]
sortDedup st xs = dd (foldr insert [] xs)
  where
    insert x [] = [x]
    insert x (y : ys) = case compareStd st x y of
      GT -> y : insert x ys
      _ -> x : y : ys
    dd (a : b : rest) | compareStd st a b == EQ && resolve st a == resolve st b = dd (a : rest)
                      | otherwise = a : dd (b : rest)
    dd ys = ys
