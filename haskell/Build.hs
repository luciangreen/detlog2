-- | Build and test the Haskell version of detlog2 with plain GHC.  Run it
-- from the repository root (the Prolog version is the main one).
--
--   runghc haskell/Build.hs          build build/hs/detlog2
--   runghc haskell/Build.hs test     build, then run the end-to-end tests
--   runghc haskell/Build.hs ci       as test, fetching mnns first if MNNS_DIR is not set,
--                                    then check the 200 recorded inputs and outputs
--   runghc haskell/Build.hs ios        run the 200 inputs and write haskell/io/ios.txt
--   runghc haskell/Build.hs check-ios  run them again and fail if any output changed
module Main (main) where

import Control.Monad (unless, when)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist)
import System.Environment (getArgs, lookupEnv, setEnv)
import System.Exit (ExitCode(..), exitWith)
import System.Process (rawSystem)

main :: IO ()
main = do
  args <- getArgs
  createDirectoryIfMissing True "build/hs"
  run "ghc" (["-O1", "-Wall", "-Wno-incomplete-uni-patterns", "-Wno-name-shadowing", "-Wno-unused-do-bind"]
             ++ ["-ihaskell/src", "-outputdir", "build/hs", "-o", "build/hs/detlog2", "haskell/app/Main.hs"])
  case args of
    ("ci" : _) -> do
      fetchMnns >> tests
      have <- doesFileExist "haskell/io/ios.txt"
      when have (ios "check")
    ("test" : _) -> tests
    ("ios" : _) -> ios "make"
    ("check-ios" : _) -> ios "check"
    _ -> return ()
  where
    ios mode = do
      run "ghc" ["-O0", "-outputdir", "build/hs/io", "-o", "build/hs/ios", "haskell/io/Ios.hs"]
      run "./build/hs/ios" [mode]
    tests = do
      run "ghc" ["-O0", "-ihaskell/src", "-outputdir", "build/hs/t", "-o", "build/hs/cli-tests", "haskell/tests/Cli.hs"]
      run "./build/hs/cli-tests" []

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
