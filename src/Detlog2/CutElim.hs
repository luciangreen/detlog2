-- | Cut elimination: every cut becomes an explicit decision.
--
-- A predicate whose clauses contain top-level cuts is rewritten into one
-- clause whose body is a chain of decisions:
--
-- > a :- b, !, c.          a(...) :- if_commit(match1, b), c, (match2, d))
-- > a :- d.
--
-- precisely: the clause @H :- G, !, B@ followed by clauses @Rest@ becomes
-- @if_commit((Args = HArgs, G), B', Rest')@, where @B'@ is @B@ with its own
-- later cuts converted (after the first cut the remaining clauses are already
-- gone, so the "else" of a later cut is fail).  Clauses without a cut become
-- disjunction alternatives @(Args = HArgs, Body ; Rest')@.
--
-- Cuts inside opaque contexts (\+, call/N, findall/3, once/1, the condition
-- of an if-then-else) are local to that context and are converted in place
-- with "else = fail".  A cut inside a disjunction or if-then-else branch at
-- the clause level would cut the clause; that placement is reported as
-- unsupported rather than guessed (memoise such predicates instead).
module Detlog2.CutElim
  ( CutEvent(..)
  , eliminateCuts
  , hasCut
  , showCutEvent
  ) where

import qualified Data.Map.Strict as M
import Detlog2.Parser
import Detlog2.Term

data CutEvent
  = CutToIfCommit PredKey Int        -- ^ clause number whose cut became if_commit/3
  | LocalCutRemoved PredKey Int      -- ^ a cut local to an opaque goal
  | UnsupportedCut PredKey Int String
  deriving (Show)

showCutEvent :: CutEvent -> String
showCutEvent e = case e of
  CutToIfCommit (f, n) i -> "cut_to_if_commit(" ++ f ++ "/" ++ show n ++ ", clause " ++ show i ++ ")"
  LocalCutRemoved (f, n) i -> "local_cut_to_if_commit(" ++ f ++ "/" ++ show n ++ ", clause " ++ show i ++ ")"
  UnsupportedCut (f, n) i why -> "unsupported_cut(" ++ f ++ "/" ++ show n ++ ", clause " ++ show i ++ "): " ++ why

hasCut :: Term -> Bool
hasCut (Atom "!") = True
hasCut (Comp _ as) = any hasCut as
hasCut _ = False

-- | Remove every cut from a program.  Returns the cut-free program and the
-- events; Left lists unsupported placements.
eliminateCuts :: Program -> Either [CutEvent] (Program, [CutEvent])
eliminateCuts p =
  let results = [ (k, elimPred k cs) | (k, cs) <- programClauses p ]
      bad = concat [ es | (_, Left es) <- results ]
  in if null bad
       then Right ( p { progPreds = foldl (\m (k, r) -> case r of
                                              Right (cs', _) -> M.insert k cs' m
                                              Left _ -> m) (progPreds p) results }
                  , concat [ evs | (_, Right (_, evs)) <- results ] )
       else Left bad

elimPred :: PredKey -> [Clause] -> Either [CutEvent] ([Clause], [CutEvent])
elimPred key@(_, arity) cls
  | not (any (hasCut . clBody) cls) = Right (cls, [])
  | otherwise = do
      -- Convert local cuts first, then check what is left at clause level.
      let local = [ (i, localCuts (clBody c)) | (i, c) <- zip [1 :: Int ..] cls ]
          localEvents = [ LocalCutRemoved key i | (i, (_, True)) <- local ]
          cls1 = [ c { clBody = b } | (c, (_, (b, _))) <- zip cls local ]
          problems = concat [ [ UnsupportedCut key i why | Just why <- [badPlacement (clBody c)] ]
                            | (i, c) <- zip [1 ..] cls1 ]
      if not (null problems) then Left problems else
        if not (any (topCut . clBody) cls1)
          then Right (cls1, localEvents)
          else do
            -- Merge the predicate into one clause of decisions.
            let base = 0
                args = [ Var (base + i) ("A" ++ show (i + 1)) | i <- [0 .. arity - 1] ]
                (alts, next, evs) = foldr (alt args) (Atom "fail", arity, []) (zip [1 ..] cls1)
                _ = next
                headT = case fst key of
                  f | arity == 0 -> Atom f
                    | otherwise -> Comp f args
                maxv = maxVarId (Comp "x" [headT, alts]) + 1
            return ([Clause headT alts maxv], localEvents ++ evs)
  where
    -- Fold from the last clause: build "this clause, else the rest".
    alt args (i, c) (rest, off, evs) =
      let nv = clNVars c
          h = renameTerm off (clHead c)
          b = renameTerm off (clBody c)
          off' = off + nv
          match = case h of
            Comp _ hargs -> mkConj (zipWith (\a x -> Comp "=" [a, x]) args hargs)
            _ -> Atom "true"
      in case splitAtCut (conjList b) of
           Just (guardGs, after) ->
             ( Comp "if_commit" [ mkConj (conjList match ++ guardGs)
                                , afterCuts after
                                , rest ]
             , off', CutToIfCommit key i : evs )
           Nothing ->
             ( disj (mkConj (conjList match ++ conjList b)) rest, off', evs )
    disj x (Atom "fail") = x
    disj x r = Comp ";" [x, r]

-- | Goals after the first cut: later cuts commit with "else fail".
afterCuts :: [Term] -> Term
afterCuts gs = case splitAtCut gs of
  Just (g, rest) -> Comp "if_commit" [mkConj g, afterCuts rest, Atom "fail"]
  Nothing -> mkConj gs

splitAtCut :: [Term] -> Maybe ([Term], [Term])
splitAtCut gs = case break (== Atom "!") gs of
  (before, _ : after) -> Just (before, after)
  _ -> Nothing

topCut :: Term -> Bool
topCut b = Atom "!" `elem` conjList b

-- | A cut not at the top level of the clause body, and not local.
badPlacement :: Term -> Maybe String
badPlacement b = case filter nested (conjList b) of
  [] -> Nothing
  (g : _) -> Just ("cut inside " ++ describe g ++ " cuts the clause; memoise this predicate instead")
  where
    nested g = g /= Atom "!" && hasCut g
    describe g = case g of
      Comp ";" [Comp "->" _, _] -> "an if-then-else branch"
      Comp ";" _ -> "a disjunction"
      Comp "->" _ -> "an if-then branch"
      _ -> "a goal"

-- | Convert cuts that are local to opaque goals.  Returns the new body and
-- whether anything changed.
localCuts :: Term -> (Term, Bool)
localCuts t = case t of
  Comp "," [a, b] -> pair "," a b
  Comp ";" [Comp "->" [c, x], e] ->
    let (c', ch1) = opaqueBody c
        (x', ch2) = localCuts x
        (e', ch3) = localCuts e
    in (Comp ";" [Comp "->" [c', x'], e'], ch1 || ch2 || ch3)
  Comp ";" [a, b] -> pair ";" a b
  Comp "->" [c, x] -> let (c', ch1) = opaqueBody c
                          (x', ch2) = localCuts x
                      in (Comp "->" [c', x'], ch1 || ch2)
  Comp "\\+" [g] -> wrap1 "\\+" g
  Comp "not" [g] -> wrap1 "not" g
  Comp "once" [g] -> wrap1 "once" g
  Comp "ignore" [g] -> wrap1 "ignore" g
  Comp "call" [g] -> wrap1 "call" g
  Comp "findall" [x, g, l] -> let (g', ch) = opaqueBody g in (Comp "findall" [x, g', l], ch)
  Comp "forall" [c, a] -> let (c', ch1) = opaqueBody c
                              (a', ch2) = opaqueBody a
                          in (Comp "forall" [c', a'], ch1 || ch2)
  Comp "aggregate_all" [s, g, r] -> let (g', ch) = opaqueBody g in (Comp "aggregate_all" [s, g', r], ch)
  _ -> (t, False)
  where
    pair op a b = let (a', c1) = localCuts a
                      (b', c2) = localCuts b
                  in (Comp op [a', b'], c1 || c2)
    wrap1 f g = let (g', ch) = opaqueBody g in (Comp f [g'], ch)

-- | A goal run as its own cut barrier: G1, !, G2 means if_commit(G1, G2, fail).
opaqueBody :: Term -> (Term, Bool)
opaqueBody g =
  let (g1, ch1) = localCuts g
  in if topCut g1
       then (afterCutsBarrier (conjList g1), True)
       else (g1, ch1)
  where
    afterCutsBarrier gs = case splitAtCut gs of
      Just (before, after) -> Comp "if_commit" [mkConj before, afterCutsBarrier after, Atom "fail"]
      Nothing -> mkConj gs
