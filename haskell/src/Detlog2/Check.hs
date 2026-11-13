-- | Static check that a converted program is choicepoint-free.
--
-- The check enforces a small, sufficient discipline:
--
--   * no cut, no disjunction, no (C -> T), no soft cut, no call/N, no
--     findall/3 and no nondeterministic built-in anywhere;
--   * the condition of every if_commit/3 is a conjunction of deterministic
--     built-ins;
--   * every predicate has exactly one clause, or exactly two clauses whose
--     first arguments are [] and [_|_] (row iteration over a proper list of
--     rows, which the generated code always passes).
--
-- Under this discipline at most one clause can match any call that the
-- generated code makes, so no call ever has an alternative left: there is
-- nothing a choicepoint could record.  The interpreter's --det mode checks
-- the same property at run time.
module Detlog2.Check (checkDeterministic) where

import qualified Data.Map.Strict as M
import qualified Data.Set as Set
import Detlog2.Builtins
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Term

checkDeterministic :: Program -> [String]
checkDeterministic p = concatMap checkPred (programClauses p)
  where
    defined = Set.fromList (progOrder p)
    checkPred ((f, n), cls) =
      shape ++ concatMap (checkBody . clBody) cls
      where
        name = f ++ "/" ++ show n
        shape = case cls of
          [_] -> []
          [a, b] | firstArg a == Just Nil && firstArg b == Just Cons -> []
          _ -> [name ++ ": " ++ show (length cls) ++ " clauses that are not a [] / [_|_] row iteration"]
        checkBody t = case t of
          Comp "," [a, b] -> checkBody a ++ checkBody b
          Atom "true" -> []
          Comp "if_commit" [c, x, e] ->
            [ name ++ ": if_commit/3 condition is not a deterministic built-in: " ++ showTermQ g
            | g <- conjList c, not (detGoal g) ] ++ checkBody x ++ checkBody e
          Atom "!" -> [name ++ ": contains a cut"]
          _ -> case goalKey t of
            Just k
              | k `elem` forbidden -> [name ++ ": uses " ++ fst k ++ "/" ++ show (snd k)]
              | Set.member k defined -> []
              | isBuiltinKey k && k `notElem` nondetBuiltinKeys && k /= ("atom_concat", 3) -> []
              | isBuiltinKey k -> [name ++ ": nondeterministic built-in " ++ fst k ++ "/" ++ show (snd k)]
              | otherwise -> [name ++ ": calls undefined " ++ fst k ++ "/" ++ show (snd k)]
            Nothing -> [name ++ ": goal is not callable: " ++ showTermQ t]
    detGoal g = case goalKey g of
      Just k -> isBuiltinKey k && not (Set.member k defined)
                && k `notElem` nondetBuiltinKeys && k /= ("atom_concat", 3)
      Nothing -> False
    forbidden =
      [ (";", 2), ("->", 2), ("*->", 2), ("\\+", 1), ("not", 1), ("call", 1)
      , ("findall", 3), ("findall", 4), ("forall", 2), ("once", 1), ("ignore", 1)
      , ("bagof", 3), ("setof", 3), ("aggregate_all", 3) ]
      ++ [ ("call", k) | k <- [2 .. 8] ]
    _unused = M.empty :: M.Map () ()

data Shape = Nil | Cons deriving (Eq)

firstArg :: Clause -> Maybe Shape
firstArg c = case goalArgs (clHead c) of
  (Atom "[]" : _) -> Just Nil
  (Comp "." [_, _] : _) -> Just Cons
  _ -> Nothing
