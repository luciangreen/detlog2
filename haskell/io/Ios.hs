-- | 200 inputs and the outputs they give, from real runs of detlog2.
--
--   runghc Build.hs ios        runs the 200 inputs and writes io/ios.txt
--   runghc Build.hs check-ios  runs them again and fails if any output changed
--
-- The inputs are made the same way every time (see 'cases').  Each output is
-- everything the command printed, with its exit code when that is not 0.
module Main (main) where

import Data.Char (isAlphaNum)
import Data.List (intercalate)
import System.Environment (getArgs, getEnvironment)
import System.Exit
import System.Process

title :: String
title = "detlog2"

binary :: FilePath
binary = "./build/hs/detlog2"

-- | Choose element i (from the case number k and a salt) of a list.
pick :: Int -> Int -> [a] -> a
pick k salt xs = xs !! ((k * (2 * salt + 1) + salt * 7) `mod` length xs)

-- | A list of length n from a pool, starting at a place set by k.
pickN :: Int -> Int -> Int -> [a] -> [a]
pickN k salt n xs = take n (drop ((k * (salt + 3)) `mod` length xs) (cycle xs))

showList' :: [Int] -> String
showList' xs = "[" ++ intercalate "," (map show xs) ++ "]"

pool :: [Int]
pool = [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]

-- | The 200 inputs: (command arguments).
cases :: [[String]]
cases = [ caseFor k | k <- [1 .. 200] ]

caseFor :: Int -> [String]
caseFor k = case k `mod` 10 of
  0 -> ["run", "examples/sample_program.pl", "det_sum(" ++ showList' (pickN k 1 (k `mod` 6) pool) ++ ", S)"]
  1 -> ["ref", "examples/cuts.pl", "max(" ++ show (k `mod` 7) ++ ", " ++ show ((k * 3) `mod` 7) ++ ", Z)"]
  2 -> ["check", "examples/cuts.pl", "classify(" ++ show ((k `mod` 9) - 4) ++ ", C)"]
  3 -> ["packets", "examples/splice.pl", pick k 1 ["c(A, B)", "q(X, Y)", "triple(X, Y, Z)", "c(1, B)", "c(A, A)", "p(X)"]]
  4 -> ["check", "examples/sample_program.pl", "if_then_else(" ++ show ((k `mod` 7) - 3) ++ ", Y)"]
  5 -> ["run", "examples/sample_program.pl"
       , "findall(Y, (member(X, " ++ showList' (pickN k 2 (1 + k `mod` 5) pool) ++ "), Y is X * " ++ show (k `mod` 4 + 1) ++ "), R)"]
  6 -> ["check", "examples/output.pl", pick k 2 ["show", "pairs", "first_big(X)", "count_out(N)", "logged(L)"]]
  7 -> ["check", "examples/memo.pl", "fib(" ++ show (k `mod` 13) ++ ", F)"]
  8 -> ["check", "examples/cuts.pl"
       , pick k 3 [ "a(X)", "two(X, Y)", "firsts(" ++ showList' (pickN k 3 3 pool) ++ ", F)"
                  , "no_big(" ++ showList' (pickN k 4 3 pool) ++ ")", "bang(O)" ]]
  _ -> ["check", "examples/sample_program.pl"
       , pick k 4 [ "append(X, Y, " ++ showList' (pickN k 5 (k `mod` 4) pool) ++ ")"
                  , "select(X, " ++ showList' (pickN k 6 3 pool) ++ ", R)"
                  , "nth0(I, " ++ showList' (pickN k 7 3 pool) ++ ", E)"
                  , "msort(" ++ showList' (pickN k 8 4 pool) ++ ", S)"
                  , "maplist(succ, " ++ showList' (pickN k 9 3 pool) ++ ", L)" ]]

quoteArg :: String -> String
quoteArg a
  | all (\c -> isAlphaNum c || c `elem` "/._-") a && not (null a) = a
  | otherwise = "'" ++ concatMap (\c -> if c == '\'' then "'\\''" else [c]) a ++ "'"

runCase :: [(String, String)] -> [String] -> IO String
runCase env args = do
  (code, out, err) <- readCreateProcessWithExitCode ((proc binary args) { env = Just env }) ""
  let text = trimEnd (out ++ err)
      codeLine = case code of
        ExitSuccess -> ""
        ExitFailure n -> "\n(exit code " ++ show n ++ ")"
  return (text ++ codeLine)
  where
    trimEnd = reverse . dropWhile (`elem` " \n") . reverse

render :: [([String], String)] -> String
render results = unlines $
  (title ++ ": 200 inputs and outputs, from real runs (runghc Build.hs ios writes this file; "
     ++ "runghc Build.hs check-ios checks it).")
  : concat [ [ "", show i ++ ". " ++ unwords (title : map quoteArg args) ]
             ++ case lines out of
                  [] -> ["   => (no output)"]
                  (l : ls) -> ("   => " ++ l) : map ("      " ++) ls
           | (i, (args, out)) <- zip [1 :: Int ..] results ]

main :: IO ()
main = do
  mode <- getArgs
  env0 <- getEnvironment
  -- the same runs everywhere: no optional tools from the environment
  let env = filter ((`notElem` ["MNNS_DIR"]) . fst) env0
  outs <- mapM (runCase env) cases
  let text = render (zip cases outs)
  case mode of
    ["make"] -> writeFile "haskell/io/ios.txt" text >> putStrLn "wrote haskell/io/ios.txt (200 inputs and outputs)"
    ["check"] -> do
      old <- readFile "haskell/io/ios.txt"
      if length old == length text && old == text
        then putStrLn "All 200 inputs give the outputs in io/ios.txt."
        else do
          let diffs = [ (n, a, b) | (n, a, b) <- zip3 [1 :: Int ..] (lines old) (lines text), a /= b ]
          mapM_ (\(n, a, b) -> putStrLn ("line " ++ show n ++ ":\n  recorded: " ++ a ++ "\n  now:      " ++ b)) (take 20 diffs)
          putStrLn "Outputs differ from io/ios.txt. If the change is meant, run runghc Build.hs ios and commit io/ios.txt."
          exitWith (ExitFailure 1)
    _ -> putStrLn "usage: ios make | ios check" >> exitWith (ExitFailure 2)
