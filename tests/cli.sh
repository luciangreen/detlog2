#!/usr/bin/env bash
# End-to-end tests of the detlog2 command line.
set -uo pipefail
cd "$(dirname "$0")/.."
D=./build/detlog2
fails=0
pass() { echo "PASS $1"; }
fail() { echo "FAIL $1"; echo "$2" | sed 's/^/    /'; fails=$((fails + 1)); }

# expect NAME EXPECTED-SUBSTRING COMMAND...
expect() {
  local name=$1 want=$2; shift 2
  local out
  out=$("$@" 2>&1)
  if grep -qF -- "$want" <<<"$out"; then pass "$name"; else fail "$name" "$out"; fi
}
# expect_exact NAME EXPECTED-OUTPUT COMMAND...
expect_exact() {
  local name=$1 want=$2; shift 2
  local out
  out=$("$@" 2>&1)
  if [ "$out" == "$want" ]; then pass "$name"; else fail "$name" "$(printf 'wanted:\n%s\ngot:\n%s' "$want" "$out")"; fi
}

# --- the cutless interpreter -------------------------------------------------
expect_exact "run: member order" "$(printf 'X = 1.\nX = 2.\nX = 3.')" \
  $D run examples/sample_program.pl 'member(X, [1,2,3])'
expect_exact "run: det_sum" "S = 6." $D run examples/sample_program.pl 'det_sum([1,2,3], S)'
expect_exact "run: duplicate facts kept" "$(printf 'X = a.\nX = b.\nX = b.')" \
  $D run examples/sample_program.pl 'multi_fact(X)'
expect "run: cut rejected" "cut (!) is not supported" $D run examples/sample_program.pl 'safe_cut(1)'
expect_exact "run: first answer of an infinite generator" "X = 1." $D run examples/sample_program.pl 'once(between(1, inf, X))'
expect_exact "run: if-then-else" "Y = nonpos." $D run examples/sample_program.pl 'if_then_else(-1, Y)'
expect_exact "run: findall" "L = [2, 4, 6]." $D run examples/sample_program.pl 'findall(Y, (member(X, [1,2,3]), Y is X * 2), L)'
expect_exact "run: output" "$(printf 'hello\ntrue.')" $D run examples/sample_program.pl 'side_effect(hello)'
expect_exact "ref: cut semantics" "true." $D ref examples/sample_program.pl 'safe_cut(1)'
expect_exact "ref: red cut max" "Z = 5." $D ref examples/cuts.pl 'max(5, 3, Z)'

# --- conversion --------------------------------------------------------------
$D convert examples/sample_program.pl -o build/sample_det.pl >/dev/null 2>&1
expect "convert: no cut in output" "det_sum__cp" cat build/sample_det.pl
if grep -q '!' build/sample_det.pl; then fail "convert: output has a cut" "$(cat build/sample_det.pl)"; else pass "convert: output has no cut"; fi
if grep -qE '(;|->)' <(grep -v '^%' build/sample_det.pl); then fail "convert: output has ; or ->" "$(cat build/sample_det.pl)"; else pass "convert: output has no ; or ->"; fi
expect "convert: cut event for safe_cut" "cut_to_if_commit(safe_cut/1, clause 1)" cat build/sample_det.pl
expect "convert: facts to member_cp" "facts_to_member_cp(multi_fact/1, 3 facts)" cat build/sample_det.pl
expect "converted: det_sum packet" "Rows = [[[1, 2, 3], 6]]." \
  $D run --det build/sample_det.pl 'det_sum__cp([1,2,3], S, Rows)'
expect_exact "converted: safe_cut packet" "Rows = [[1]]." $D run --det build/sample_det.pl 'safe_cut__cp(1, Rows)'
expect "converted: if_then_else packet" "Rows = [[-1, nonpos]]." $D run --det build/sample_det.pl 'if_then_else__cp(-1, Y, Rows)'
expect "converted file runs without cut" "Rows = [[a], [b], [b]]." $D run --det build/sample_det.pl 'multi_fact__cp(X, Rows)'

# --- the splice example ------------------------------------------------------
expect "packets: splice early" "packet: cp([[1, 3], [1, 4], [2, 3], [2, 4]])" $D packets examples/splice.pl 'c(A, B)'
expect "packets: enumerate late" "A = 2, B = 4." $D packets examples/splice.pl 'c(A, B)'
$D convert examples/splice.pl -o build/splice_det.pl >/dev/null 2>&1
expect "convert: splice/2 used" "splice([cp(" cat build/splice_det.pl
expect "convert: splice event" "splice_early(a(A), b(B))" cat build/splice_det.pl

# --- equivalence checks (source with cuts vs converted, choicepoint-free) ----
expect "check: sample" "all checks passed" $D check examples/sample_program.pl \
  'det_sum([1,2,3], S)' 'nondet_member(X, [a,b,a])' 'multi_fact(X)' 'if_then_else(3, Y)' \
  'if_then_else(0, Y)' 'safe_cut(1)' 'safe_cut(-1)' 'side_effect(hi)'
expect "check: cuts" "all checks passed" $D check examples/cuts.pl \
  'a(X)' 'max(5, 3, Z)' 'max(2, 3, Z)' 'max(5, 3, 3)' 'classify(-4, C)' 'classify(0, C)' 'classify(7, C)' \
  'firsts([1,2,3], F)' 'two(X, Y)' 'no_big([1,2])' 'no_big([1,9])'
expect "check: splice" "all checks passed" $D check examples/splice.pl \
  'c(A, B)' 'c(1, B)' 'c(A, A)' 'triple(X, Y, Z)' 'q(X, Y)' 'c(A, B), A < B'
expect "check: library" "all checks passed" $D check examples/sample_program.pl \
  'append(X, Y, [1,2,3])' 'select(X, [a,b,c], R)' 'maplist(succ, [1,2,3], L)' \
  'permutation([1,2,3], P)' 'nth0(I, [a,b,c], E)' 'msort([c,a,b], S)' 'length(L, 2)' \
  'between(1, 4, X), X mod 2 =:= 0' '(X = 1 ; X = 2), \+ X = 1' 'aggregate_all(count, member(_, [a,b]), N)'
expect "check: memo example fib" "all checks passed" $D check examples/memo.pl 'fib(10, F)'
expect "convert: unsupported cut is reported" "unsupported_cut(pick/2, clause 1)" $D convert examples/memo.pl

# --- memoisation --------------------------------------------------------------
expect "memoise: complete table" "ok   pick(5, X)" $D memoise examples/memo.pl --goal 'pick(2, X)' --goal 'pick(5, X)' \
  --complete -o build/memo_det.pl --check 'pick(2, X)' --check 'pick(5, X)'
expect "memoise: table in output" "memo_lookup(" cat build/memo_det.pl
expect "memoise: answers" "Rows = [[5, big]]." $D run --det build/memo_det.pl 'pick__cp(5, X, Rows)'
expect "memoise: miss is an error" "memo_miss" $D run --det build/memo_det.pl 'pick__cp(9, X, Rows)'
expect "memoise: fib table with fallback" "ok   fib(20, F)" $D memoise examples/memo.pl --goal 'fib(20, F)' \
  -o build/fib_det.pl --check 'fib(20, F)' --check 'fib(7, F)'

# --- mnns bridge (needs SWI-Prolog and a clone of mnns) -------------------------
if command -v swipl >/dev/null 2>&1 && [ -n "${MNNS_DIR:-}" ] && [ -f "$MNNS_DIR/optimise.pl" ]; then
  cat > build/mnns_in.pl <<'EOF'
num(1). num(2). num(3).
big(R) :- findall(X, (num(X), X > 1), R).
pos(X) :- X > 0, !.
EOF
  expect "mnns: report line" "MNNS_OPTIMISE ok" $D mnns build/mnns_in.pl --mnns "$MNNS_DIR" -o build/mnns_det.pl \
    --check 'big(R)' --check 'pos(3)' --check 'pos(-3)'
  expect "mnns: checks pass" "ok   big(R)" $D mnns build/mnns_in.pl --mnns "$MNNS_DIR" -o build/mnns_det.pl --check 'big(R)'
else
  echo "SKIP mnns bridge (swipl or MNNS_DIR missing)"
fi

echo
if [ "$fails" -eq 0 ]; then echo "all CLI tests passed"; else echo "$fails CLI test(s) failed"; exit 1; fi
