-- | Build and test detlog2 with plain GHC.
--
--   runghc Build.hs          build build/detlog2
--   runghc Build.hs test     build, then run the end-to-end tests
--   runghc Build.hs ci       as test, fetching mnns first if MNNS_DIR is not set,
--                            then check the 200 recorded inputs and outputs
--   runghc Build.hs ios        run the 200 inputs and write io/ios.txt
--   runghc Build.hs check-ios  run them again and fail if any output changed
module Main (main) where

import Control.Monad (unless, when)
import System.Directory (createDirectoryIfMissing, doesDirectoryExist, doesFileExist)
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
    ("ci" : _) -> do
      fetchMnns >> tests
      have <- doesFileExist "io/ios.txt"
      when have (ios "check")
    ("test" : _) -> tests
    ("ios" : _) -> ios "make"
    ("check-ios" : _) -> ios "check"
    _ -> return ()
  where
    ios mode = do
      run "ghc" ["-O0", "-outputdir", "build/io", "-o", "build/ios", "io/Ios.hs"]
      run "./build/ios" [mode]
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
