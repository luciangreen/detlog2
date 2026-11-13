-- | Bridge to the mnns repository (github.com/luciangreen/mnns).
--
-- mnns's @optimise.pl@ runs its proof-checked stages on a Prolog file:
-- PLOp (findall/3 over finite generators to deterministic loops), AIOC
-- simplification, and its own Detlog stage (once/1 and terminal-cut
-- lowering).  Every rewrite it keeps has a proof accepted by its independent
-- checker.  detlog2 runs that pass first and then converts the result, so
-- whatever mnns could prove is rewritten its way, and detlog2 removes the
-- remaining cuts and choicepoints.
module Detlog2.Mnns
  ( findMnnsDir
  , runMnnsOptimise
  ) where

import Control.Exception (IOException, try)
import System.Directory (doesFileExist)
import System.Environment (lookupEnv)
import System.Exit (ExitCode(..))
import System.Process (readProcessWithExitCode)

-- | --mnns DIR, else $MNNS_DIR, else ../mnns, else ./mnns.
findMnnsDir :: Maybe FilePath -> IO (Either String FilePath)
findMnnsDir given = do
  env <- lookupEnv "MNNS_DIR"
  let candidates = maybe [] (: []) given ++ maybe [] (: []) env ++ ["../mnns", "mnns"]
  found <- firstExisting candidates
  return $ case found of
    Just d -> Right d
    Nothing -> Left ("mnns not found (tried " ++ show candidates
                     ++ "); clone https://github.com/luciangreen/mnns and pass --mnns DIR")
  where
    firstExisting [] = return Nothing
    firstExisting (d : ds) = do
      ok <- doesFileExist (d ++ "/optimise.pl")
      if ok then return (Just d) else firstExisting ds

-- | Run @swipl optimise.pl -- IN OUT@.  Returns mnns's report line.
runMnnsOptimise :: FilePath -> FilePath -> FilePath -> IO (Either String String)
runMnnsOptimise dir input output = do
  r <- try (readProcessWithExitCode "swipl" [dir ++ "/optimise.pl", "--", input, output] "")
         :: IO (Either IOException (ExitCode, String, String))
  return $ case r of
    Left e -> Left ("could not run swipl (SWI-Prolog is needed for the mnns pass): " ++ show e)
    Right (ExitSuccess, out, _) -> Right (trim out)
    Right (ExitFailure _, out, err) -> Left (trim (out ++ err))
  where
    trim = reverse . dropWhile (`elem` " \n\r\t") . reverse
