-- | End-to-end tests of the detlog2 command line.  Run by Build.hs.
module Main (main) where

import Control.Monad (unless, when)
import Data.IORef
import Data.List (isInfixOf)
import System.Directory (doesFileExist, findExecutable)
import System.Environment (lookupEnv)
import System.Exit
import System.Process (readProcessWithExitCode)

detlog2 :: FilePath
detlog2 = "./build/detlog2"

main :: IO ()
main = do
  fails <- newIORef (0 :: Int)
  let report name ok detail = if ok
        then putStrLn ("PASS " ++ name)
        else do
          putStrLn ("FAIL " ++ name)
          putStrLn (unlines (map ("    " ++) (lines detail)))
          modifyIORef fails (+ 1)
      out args = do
        (_, o, e) <- readProcessWithExitCode detlog2 args ""
        return (o ++ e)
      -- the output contains a string
      expect name want args = do
        o <- out args
        report name (want `isInfixOf` o) o
      -- the output is exactly a string
      expectExact name want args = do
        o <- out args
        let o' = reverse (dropWhile (== '\n') (reverse o))
        report name (o' == want) ("wanted:\n" ++ want ++ "\ngot:\n" ++ o')
      expectNot name bad args = do
        o <- out args
        report name (not (bad `isInfixOf` o)) o
      fileHas name want path = do
        s <- readFile path
        report name (want `isInfixOf` s) s
      fileLacks name bad path = do
        s <- readFile path
        report name (not (bad `isInfixOf` s)) s

  -- the cutless interpreter ---------------------------------------------------
  expectExact "run: member order" "X = 1.\nX = 2.\nX = 3." ["run", "examples/sample_program.pl", "member(X, [1,2,3])"]
  expectExact "run: det_sum" "S = 6." ["run", "examples/sample_program.pl", "det_sum([1,2,3], S)"]
  expectExact "run: duplicate facts kept" "X = a.\nX = b.\nX = b." ["run", "examples/sample_program.pl", "multi_fact(X)"]
  expect "run: cut rejected" "cut (!) is not supported" ["run", "examples/sample_program.pl", "safe_cut(1)"]
  expectExact "run: first answer of an infinite generator" "X = 1." ["run", "examples/sample_program.pl", "once(between(1, inf, X))"]
  expectExact "run: if-then-else" "Y = nonpos." ["run", "examples/sample_program.pl", "if_then_else(-1, Y)"]
  expectExact "run: findall" "L = [2, 4, 6]." ["run", "examples/sample_program.pl", "findall(Y, (member(X, [1,2,3]), Y is X * 2), L)"]
  expectExact "run: output" "hello\ntrue." ["run", "examples/sample_program.pl", "side_effect(hello)"]
  expectExact "run: a \"!\" string is data, not a cut" "O = ['H', i, !]." ["run", "examples/cuts.pl", "bang(O)"]
  expectExact "ref: cut semantics" "true." ["ref", "examples/sample_program.pl", "safe_cut(1)"]
  expectExact "ref: red cut max" "Z = 5." ["ref", "examples/cuts.pl", "max(5, 3, Z)"]

  -- conversion, with proofs ---------------------------------------------------
  _ <- out ["convert", "examples/sample_program.pl", "-o", "build/sample_det.pl"]
  fileHas "convert: packets" "det_sum__cp" "build/sample_det.pl"
  fileHas "convert: proof accepted while converting" "proof accepted" "build/sample_det.pl"
  fileHas "convert: proof file written" "clause_packet(" "build/sample_det.pl.proof"
  converted <- readFile "build/sample_det.pl"
  let code = unlines (filter (\l -> take 1 l /= "%") (lines converted))
  report "convert: no cut in output" (not ("!" `isInfixOf` code)) code
  report "convert: no ; or -> in output" (not (";" `isInfixOf` code) && not ("->" `isInfixOf` code)) code
  fileHas "convert: cut event for safe_cut" "cut_to_if_commit(safe_cut/1, clause 1)" "build/sample_det.pl"
  fileHas "convert: facts to member_cp" "facts_to_member_cp(multi_fact/1, 3 facts)" "build/sample_det.pl"
  fileHas "convert: output as data" "effect_text(" "build/sample_det.pl"
  expect "converted: det_sum packet" "Rows = [[[1, 2, 3], 6]]." ["run", "--det", "build/sample_det.pl", "det_sum__cp([1,2,3], S, Rows)"]
  expectExact "converted: safe_cut packet" "Rows = [[1]]." ["run", "--det", "build/sample_det.pl", "safe_cut__cp(1, Rows)"]
  expect "converted: if_then_else packet" "Rows = [[-1, nonpos]]." ["run", "--det", "build/sample_det.pl", "if_then_else__cp(-1, Y, Rows)"]
  expect "converted: output is a packet item" "Rows = [out('hi\\n'), [hi]]." ["run", "--det", "build/sample_det.pl", "side_effect__cp(hi, Rows)"]

  -- the proof is checked independently, and tampering is caught
  expect "proof-check: accepted from files" "proof accepted"
    ["proof-check", "examples/sample_program.pl", "build/sample_det.pl", "build/sample_det.pl.proof"]
  writeFile "build/tampered.pl" (replaceFirst "H + Rest" "H - Rest" converted)
  expect "proof-check: tampered code rejected" "proof rejected"
    ["proof-check", "examples/sample_program.pl", "build/tampered.pl", "build/sample_det.pl.proof"]
  src <- readFile "examples/sample_program.pl"
  writeFile "build/other_source.pl" (replaceFirst "S is H + Rest" "S is H * Rest" src)
  expect "proof-check: wrong source rejected" "proof rejected"
    ["proof-check", "build/other_source.pl", "build/sample_det.pl", "build/sample_det.pl.proof"]
  proof <- readFile "build/sample_det.pl.proof"
  writeFile "build/tampered.proof" (replaceFirst "d(det," "d(effect," proof)
  expect "proof-check: tampered proof rejected" "proof rejected"
    ["proof-check", "examples/sample_program.pl", "build/sample_det.pl", "build/tampered.proof"]

  -- the splice example
  expect "packets: splice early" "packet: cp([[1, 3], [1, 4], [2, 3], [2, 4]])" ["packets", "examples/splice.pl", "c(A, B)"]
  expect "packets: enumerate late" "A = 2, B = 4." ["packets", "examples/splice.pl", "c(A, B)"]
  _ <- out ["convert", "examples/splice.pl", "-o", "build/splice_det.pl"]
  fileHas "convert: splice/2 used" "splice([cp(" "build/splice_det.pl"
  fileHas "convert: splice event" "splice_early(a(A), b(B))" "build/splice_det.pl"
  expect "proof-check: splice" "proof accepted"
    ["proof-check", "examples/splice.pl", "build/splice_det.pl", "build/splice_det.pl.proof"]

  -- equivalence: answers and output, identical and in order ------------------
  expect "check: sample" "all checks passed"
    ["check", "examples/sample_program.pl", "det_sum([1,2,3], S)", "nondet_member(X, [a,b,a])", "multi_fact(X)"
    , "if_then_else(3, Y)", "if_then_else(0, Y)", "safe_cut(1)", "safe_cut(-1)", "side_effect(hi)"]
  expect "check: cuts" "all checks passed"
    ["check", "examples/cuts.pl", "a(X)", "max(5, 3, Z)", "max(2, 3, Z)", "max(5, 3, 3)", "classify(-4, C)"
    , "classify(0, C)", "classify(7, C)", "firsts([1,2,3], F)", "two(X, Y)", "no_big([1,2])", "no_big([1,9])", "bang(O)"]
  expect "check: splice" "all checks passed"
    ["check", "examples/splice.pl", "c(A, B)", "c(1, B)", "c(A, A)", "triple(X, Y, Z)", "q(X, Y)", "c(A, B), A < B"]
  expect "check: library" "all checks passed"
    ["check", "examples/sample_program.pl", "append(X, Y, [1,2,3])", "select(X, [a,b,c], R)", "maplist(succ, [1,2,3], L)"
    , "permutation([1,2,3], P)", "nth0(I, [a,b,c], E)", "msort([c,a,b], S)", "length(L, 2)"
    , "between(1, 4, X), X mod 2 =:= 0", "(X = 1 ; X = 2), \\+ X = 1", "aggregate_all(count, member(_, [a,b]), N)"]
  -- the output-order bug: output from inside a generator, interleaved
  expect "check: output order" "all checks passed"
    ["check", "examples/output.pl", "show", "pairs", "first_big(X)", "count_out(N)", "logged(L)"]
  expect "check: output order (no splice)" "all checks passed"
    ["check", "--no-splice", "examples/output.pl", "show", "pairs", "first_big(X)"]
  expect "check: memo example fib" "all checks passed" ["check", "examples/memo.pl", "fib(10, F)"]
  expect "convert: unsupported cut is reported" "unsupported_cut(pick/2, clause 1)" ["convert", "examples/memo.pl"]

  -- memoisation ----------------------------------------------------------------
  expect "memoise: complete table" "ok   pick(5, X)"
    ["memoise", "examples/memo.pl", "--goal", "pick(2, X)", "--goal", "pick(5, X)", "--complete"
    , "-o", "build/memo_det.pl", "--check", "pick(2, X)", "--check", "pick(5, X)"]
  fileHas "memoise: table in output" "memo_lookup(" "build/memo_det.pl"
  fileHas "memoise: table checked by re-running it" "proof accepted" "build/memo_det.pl"
  expect "memoise: answers" "Rows = [[5, big]]." ["run", "--det", "build/memo_det.pl", "pick__cp(5, X, Rows)"]
  expect "memoise: miss is an error" "memo_miss" ["run", "--det", "build/memo_det.pl", "pick__cp(9, X, Rows)"]
  expect "memoise: proof-check from files" "proof accepted"
    ["proof-check", "examples/memo.pl", "build/memo_det.pl", "build/memo_det.pl.proof"]
  memoProof <- readFile "build/memo_det.pl.proof"
  writeFile "build/memo_bad.proof" (replaceFirst "big" "small" memoProof)
  memoCode <- readFile "build/memo_det.pl"
  writeFile "build/memo_bad.pl" (replaceFirst "big" "small" memoCode)
  expect "memoise: a wrong table is rejected" "proof rejected"
    ["proof-check", "examples/memo.pl", "build/memo_bad.pl", "build/memo_bad.proof"]
  expect "memoise: fib table with fallback" "ok   fib(20, F)"
    ["memoise", "examples/memo.pl", "--goal", "fib(20, F)", "-o", "build/fib_det.pl", "--check", "fib(20, F)", "--check", "fib(7, F)"]

  -- mnns bridge (needs SWI-Prolog and mnns) ---------------------------------------
  swipl <- findExecutable "swipl"
  mnns <- lookupEnv "MNNS_DIR"
  haveMnns <- maybe (return False) (\d -> doesFileExist (d ++ "/optimise.pl")) mnns
  case (swipl, mnns) of
    (Just _, Just dir) | haveMnns -> do
      writeFile "build/mnns_in.pl" (unlines
        [ "num(1). num(2). num(3)."
        , "big(R) :- findall(X, (num(X), X > 1), R)."
        , "pos(X) :- X > 0, !." ])
      expect "mnns: report line" "MNN_OPTIMISE ok"
        ["mnns", "build/mnns_in.pl", "--mnns", dir, "-o", "build/mnns_det.pl", "--check", "big(R)", "--check", "pos(3)", "--check", "pos(-3)"]
      expect "mnns: checks pass" "ok   big(R)"
        ["mnns", "build/mnns_in.pl", "--mnns", dir, "-o", "build/mnns_det.pl", "--check", "big(R)"]
      fileHas "mnns: proof accepted" "proof accepted" "build/mnns_det.pl"
    _ -> putStrLn "SKIP mnns bridge (swipl or MNNS_DIR missing)"

  n <- readIORef fails
  putStrLn ""
  if n == 0 then putStrLn "all CLI tests passed" else do
    putStrLn (show n ++ " CLI test(s) failed")
    exitWith (ExitFailure 1)
  where
    _unused = (unless, when, expectNotUnused)
    expectNotUnused = ()

replaceFirst :: String -> String -> String -> String
replaceFirst old new = go
  where
    go [] = []
    go s@(c : cs)
      | take (length old) s == old = new ++ drop (length old) s
      | otherwise = c : go cs
