-- | Build and test detlog2 with plain GHC.
--
--   runghc Build.hs          build build/detlog2
--   runghc Build.hs test     build, then run the end-to-end tests
--   runghc Build.hs ci       as test, fetching mnns first if MNNS_DIR is not set
module Main (main) where

import Control.Monad (unless, when)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist)
import System.Environment (getArgs, lookupEnv, setEnv)
import System.Exit (ExitCode(..), exitWith)
import System.Process (rawSystem)

main :: IO ()
main = do
  args <- getArgs
  createDirectoryIfMissing True "build"
  run "ghc" (["-O1", "-Wall", "-Wno-incomplete-uni-patterns", "-Wno-name-shadowing", "-Wno-unused-do-bind"]
             ++ ["-isrc", "-outputdir", "build", "-o", "build/detlog2", "app/Main.hs"])
  case args of
    ("ci" : _) -> fetchMnns >> tests
    ("test" : _) -> tests
    _ -> return ()
  where
    tests = do
      run "ghc" ["-O0", "-isrc", "-outputdir", "build/t", "-o", "build/cli-tests", "tests/Cli.hs"]
      run "./build/cli-tests" []

-- | CI: use $MNNS_DIR, or clone mnns next to the build.
fetchMnns :: IO ()
fetchMnns = do
  m <- lookupEnv "MNNS_DIR"
  case m of
    Just _ -> return ()
    Nothing -> do
      let dir = "build/mnns"
      have <- doesDirectoryExist dir
      unless have $ run "git" ["clone", "--depth", "1", "https://github.com/luciangreen/mnns", dir]
      setEnv "MNNS_DIR" dir

run :: String -> [String] -> IO ()
run cmd as = do
  code <- rawSystem cmd as
  when (code /= ExitSuccess) $ exitWith code
