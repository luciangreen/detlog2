-- | Memoisation: expand calls into answer tables.
--
-- For each memoised call, the source program (cuts and choicepoints
-- included) is run once with the reference engine, and the complete answer
-- packet is written into the converted program as data:
--
-- > p__cp(A1, A2, Rows) :-
-- >     if_commit(memo_lookup([A1, A2], [[[10, _], [[10, 55]]]], Rows),
-- >               true,
-- >               p__cp__compute(A1, A2, Rows)).
--
-- With @complete@, the table is declared to cover every call that will be
-- made, the computing code is dropped, and a call outside the table is an
-- error (memo_miss/2).  This expands predicates whose cuts cannot be
-- converted syntactically into code with no choicepoints and no cuts.
module Detlog2.Memo
  ( MemoTable
  , memoCall
  , addMemoTables
  ) where

import qualified Data.Map.Strict as M
import Detlog2.Builtins
import Detlog2.Convert (cpName)
import Detlog2.Interp (Options(..))
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference
import Detlog2.Term

-- | Entries per predicate: (call pattern, answer rows).
type MemoTable = M.Map PredKey [(Term, [Term])]

-- | Run one call with the reference engine and record its answer packet.
memoCall :: Options -> Int -> Program -> Term -> Int -> MemoTable -> Either String MemoTable
memoCall opts maxAnswers src goal nv table = case goalKey goal of
  Nothing -> Left "memoise: goal is not callable"
  Just key
    | not (M.member key (progPreds src)) ->
        Left ("memoise: " ++ fst key ++ "/" ++ show (snd key) ++ " is not defined by the program")
    | otherwise -> do
        let args = mkList (goalArgs goal) (Atom "[]")
            stream = refRun opts (withPrelude src) goal nv
        rows <- collect (maxAnswers + 1) stream args
        if length rows > maxAnswers
          then Left ("memoise: " ++ showTermQ goal ++ " has more than " ++ show maxAnswers
                     ++ " answers; raise --max-answers if the packet is finite")
          else Right (M.insertWith (flip (++)) key [(args, rows)] table)
  where
    collect 0 _ _ = Right []
    collect _ [] _ = Right []
    collect k (Ans s : r) args = (resolve s args :) <$> collect (k - (1 :: Int)) r args
    collect k (Out _ : r) args = collect k r args
    collect _ (Err e : _) _ = Left ("memoise: " ++ showTermQ goal ++ " raised: " ++ e)

-- | Put the tables into a converted program.  With complete = True the
-- predicate is answered from its table alone.
addMemoTables :: Bool -> MemoTable -> Program -> Program
addMemoTables complete table conv = foldl add conv (M.toList table)
  where
    add p ((f, n), entries) =
      let key = (cpName f, n + 1)
          computeKey = (cpName f ++ "__compute", n + 1)
          args = [ Var i ("A" ++ show (i + 1)) | i <- [0 .. n - 1] ]
          rowsV = Var n "Rows"
          (tableT, _) = renameEntries (n + 1) entries
          fallback
            | complete = Comp "memo_miss" [Comp "/" [Atom f, Int (fromIntegral n)], mkList args (Atom "[]")]
            | otherwise = Comp computeKeyName (args ++ [rowsV])
          computeKeyName = fst computeKey
          memoClause = Clause (Comp (fst key) (args ++ [rowsV]))
                              (Comp "if_commit" [ Comp "memo_lookup" [mkList args (Atom "[]"), tableT, rowsV]
                                                , Atom "true", fallback ])
                              (maxVarId tableT + n + 2)
          renamed = [ c { clHead = rename (clHead c) } | c <- M.findWithDefault [] key (progPreds p) ]
          rename (Comp _ as) = Comp computeKeyName as
          rename t = t
          preds1 = M.insert key [memoClause] (progPreds p)
          preds2 = if complete || null renamed then preds1 else M.insert computeKey renamed preds1
          order1 = if M.member key (progPreds p) then progOrder p else progOrder p ++ [key]
          order2 = if complete || null renamed then order1
                   else concatMap (\k -> if k == key then [key, computeKey] else [k]) order1
      in p { progPreds = preds2, progOrder = order2 }

-- | Give every entry its own variables, numbered from 'start'.
renameEntries :: Int -> [(Term, [Term])] -> (Term, Int)
renameEntries start entries =
  let st0 = emptyState start
      step (acc, st) (pat, rows) =
        let (c, st') = copyTerm st (mkList [pat, mkList rows (Atom "[]")] (Atom "[]"))
        in (acc ++ [c], st')
      (items, stEnd) = foldl step ([], st0) entries
  in (mkList items (Atom "[]"), stNext stEnd)
