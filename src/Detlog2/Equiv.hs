-- | Answer-sequence comparison between a source program (run with ordinary
-- cut semantics) and its converted Detlog form (run choicepoint-free, with
-- the determinism check on).
module Detlog2.Equiv
  ( Outcome(..)
  , sourceOutcome
  , convertedOutcome
  , showOutcome
  ) where

import Detlog2.Builtins
import Detlog2.Convert (cpName)
import Detlog2.Interp
import Detlog2.Parser
import Detlog2.Pretty
import Detlog2.Prelude
import Detlog2.Reference
import Detlog2.Term

data Outcome = Outcome
  { ocAnswers :: [String]     -- ^ query-variable values, canonical variable names
  , ocOutput :: String
  , ocError :: Maybe String
  , ocTruncated :: Bool       -- ^ more answers than the limit
  } deriving (Eq)

showOutcome :: Outcome -> String
showOutcome o =
  unlines ([ "  answer: " ++ a | a <- ocAnswers o ]
           ++ [ "  (no answers)" | null (ocAnswers o) ]
           ++ [ "  output: " ++ show (ocOutput o) | not (null (ocOutput o)) ]
           ++ [ "  error: " ++ e | Just e <- [ocError o] ]
           ++ [ "  (answer limit reached)" | ocTruncated o ])

-- | Run the source with the reference engine.
sourceOutcome :: Options -> Int -> Program -> Term -> [Term] -> Int -> Outcome
sourceOutcome opts maxAns src goal vars nv =
  fold (refRun opts (withPrelude src) goal nv) (Outcome [] "" Nothing False) maxAns
  where
    fold [] o _ = finish o
    fold _ o 0 = finish o { ocTruncated = True }
    fold (Ans s : r) o k = fold r o { ocAnswers = showAnswerTerm (resolve s (mkList vars (Atom "[]"))) : ocAnswers o } (k - 1)
    fold (Out t : r) o k = fold r o { ocOutput = ocOutput o ++ t } k
    fold (Err e : _) o _ = finish o { ocError = Just e }
    finish o = o { ocAnswers = reverse (ocAnswers o) }

-- | Run the converted query packet '$query__cp'(V1, ..., Vk, Rows) once and
-- enumerate its rows.
convertedOutcome :: Options -> Int -> Program -> Int -> Outcome
convertedOutcome opts maxAns conv k =
  let vars = [ Var i ("V" ++ show i) | i <- [0 .. k - 1] ]
      rowsV = Var k "Rows"
      goal = Comp (cpName "$query") (vars ++ [rowsV])
      stream = runGoal opts { optDetCheck = True } conv goal (k + 1)
      outText = concat [ t | Out t <- stream ]
      errs = [ e | Err e <- stream ]
  in case (errs, [ s | Ans s <- stream ]) of
       (e : _, _) -> Outcome [] outText (Just e) False
       ([], [s]) -> case termToList s rowsV of
         Just rows ->
           let shown = map (showAnswerTerm . resolve s) rows
           in Outcome (take maxAns shown) outText Nothing (length shown > maxAns)
         Nothing -> Outcome [] outText (Just "query packet is not a proper list") False
       ([], []) -> Outcome [] outText (Just "the converted query packet failed (it must succeed exactly once)") False
       ([], _) -> Outcome [] outText (Just "the converted query packet succeeded more than once") False
