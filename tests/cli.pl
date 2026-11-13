/*  cli.pl - end-to-end tests of the detlog2 command line.

    swipl tests/cli.pl          (after building build/detlog2)

    Each test runs build/detlog2 and looks at what it printed (standard
    output, then standard error) or at a file it wrote.
*/

:- use_module('../src/detlog_runtime').
:- use_module(library(process)).

:- initialization(main, main).

binary('./build/detlog2').

main :-
    actions(As),
    foldl(run_action, As, 0, Fails),
    format("~n"),
    compare(O, Fails, 0),
    finish(O, Fails).

finish(=, _) :-
    format("all CLI tests passed~n").
finish(>, N) :-
    format("~d CLI test(s) failed~n", [N]),
    halt(1).

out(Args, Text) :-
    binary(Bin),
    process_create(Bin, Args, [stdout(pipe(O)), stderr(pipe(E)), process(Pid)]),
    read_string(O, _, OS),
    read_string(E, _, ES),
    close(O),
    close(E),
    process_wait(Pid, _),
    string_concat(OS, ES, Text).

report(true, Name, _, F, F) :-
    format("PASS ~w~n", [Name]).
report(false, Name, Detail, F0, F) :-
    format("FAIL ~w~n", [Name]),
    split_string(Detail, "\n", "", Ls),
    forall_detail(Ls),
    F is F0 + 1.

forall_detail([]).
forall_detail([L|Ls]) :-
    format("    ~s~n", [L]),
    forall_detail(Ls).

contains(S, Sub, B) :-
    test_b(sub_string(S, _, _, _, Sub), B).

test_b(G, B) :-
    if_commit(G, B = true, B = false).

run_action(A, F0, F) :-
    action_kind(A, K),
    run_kind(K, A, F0, F).

action_kind(A, K) :-
    functor(A, K, _).

run_kind(expect, expect(Name, Want, Args), F0, F) :-
    out(Args, O),
    contains(O, Want, B),
    report(B, Name, O, F0, F).
run_kind(exact, exact(Name, Want, Args), F0, F) :-
    out(Args, O0),
    string_codes(O0, Cs),
    reverse(Cs, R),
    drop_newlines(R, R1),
    reverse(R1, Cs1),
    string_codes(O, Cs1),
    test_b(O == Want, B),
    format(string(D), "wanted:~n~s~ngot:~n~s", [Want, O]),
    report(B, Name, D, F0, F).
run_kind(file_has, file_has(Name, Want, Path), F0, F) :-
    read_file_to_string(Path, S, []),
    contains(S, Want, B),
    report(B, Name, S, F0, F).
run_kind(run, run(Args), F, F) :-
    out(Args, _).
run_kind(code_free, code_free(Name, Path, Banned), F0, F) :-
    read_file_to_string(Path, S, []),
    split_string(S, "\n", "", Ls),
    findall(L, ( member(L, Ls), if_commit(sub_string(L, 0, 1, _, "%"), fail, true) ), Code),
    atomic_list_concat(Code, '\n', CA),
    atom_string(CA, CS),
    test_b(( member(X, Banned), sub_string(CS, _, _, _, X) ), Found),
    neg_bool(Found, B),
    report(B, Name, CS, F0, F).
run_kind(replace, replace(Src, Dst, Old, New), F, F) :-
    read_file_to_string(Src, S, []),
    replace_first(S, Old, New, S1),
    setup_call_cleanup(open(Dst, write, W), write(W, S1), close(W)).
run_kind(mnns, mnns, F0, F) :-
    if_commit(( getenv('MNNS_DIR', Dir), format(atom(Opt), "~w/optimise.pl", [Dir]), exists_file(Opt),
                absolute_file_name(path(swipl), _, [access(execute), file_errors(fail)]) ),
              ( mnns_actions(Dir, As), foldl(run_action, As, F0, F) ),
              ( format("SKIP mnns bridge (swipl or MNNS_DIR missing)~n"), F = F0 )).

run_kind(write_file, write_file(Path, Text), F, F) :-
    run_kind_write(Path, Text).

neg_bool(true, false).
neg_bool(false, true).

drop_newlines([], []).
drop_newlines([C|Cs], Out) :-
    if_commit(C =:= 0'\n, drop_newlines(Cs, Out), Out = [C|Cs]).

replace_first(S, Old, New, S1) :-
    string_codes(S, Cs),
    string_codes(Old, OCs),
    string_codes(New, NCs),
    if_commit(( append(Before, Rest, Cs), append(OCs, After, Rest) ),
              ( conc(Before, NCs, P1), conc(P1, After, R), string_codes(S1, R) ),
              S1 = S).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

mnns_actions(Dir, [
    write_file("build/mnns_in.pl", "num(1). num(2). num(3).\nbig(R) :- findall(X, (num(X), X > 1), R).\npos(X) :- X > 0, !.\n"),
    expect('mnns: report line', "MNN_OPTIMISE ok",
           [mnns, 'build/mnns_in.pl', '--mnns', Dir, '-o', 'build/mnns_det.pl',
            '--check', 'big(R)', '--check', 'pos(3)', '--check', 'pos(-3)']),
    expect('mnns: checks pass', "ok   big(R)",
           [mnns, 'build/mnns_in.pl', '--mnns', Dir, '-o', 'build/mnns_det.pl', '--check', 'big(R)']),
    file_has('mnns: proof accepted', "proof accepted", 'build/mnns_det.pl')
  ]).

run_kind_write(Path, Text) :-
    setup_call_cleanup(open(Path, write, W), write(W, Text), close(W)).

actions([
  % the cutless interpreter
  exact('run: member order', "X = 1.\nX = 2.\nX = 3.", [run, 'examples/sample_program.pl', 'member(X, [1,2,3])']),
  exact('run: det_sum', "S = 6.", [run, 'examples/sample_program.pl', 'det_sum([1,2,3], S)']),
  exact('run: duplicate facts kept', "X = a.\nX = b.\nX = b.", [run, 'examples/sample_program.pl', 'multi_fact(X)']),
  expect('run: cut rejected', "cut (!) is not supported", [run, 'examples/sample_program.pl', 'safe_cut(1)']),
  exact('run: first answer of an infinite generator', "X = 1.", [run, 'examples/sample_program.pl', 'once(between(1, inf, X))']),
  exact('run: if-then-else', "Y = nonpos.", [run, 'examples/sample_program.pl', 'if_then_else(-1, Y)']),
  exact('run: findall', "L = [2, 4, 6].", [run, 'examples/sample_program.pl', 'findall(Y, (member(X, [1,2,3]), Y is X * 2), L)']),
  exact('run: output', "hello\ntrue.", [run, 'examples/sample_program.pl', 'side_effect(hello)']),
  exact('run: a "!" string is data, not a cut', "O = ['H', i, !].", [run, 'examples/cuts.pl', 'bang(O)']),
  exact('ref: cut semantics', "true.", [ref, 'examples/sample_program.pl', 'safe_cut(1)']),
  exact('ref: red cut max', "Z = 5.", [ref, 'examples/cuts.pl', 'max(5, 3, Z)']),
  % conversion, with proofs
  run([convert, 'examples/sample_program.pl', '-o', 'build/sample_det.pl']),
  file_has('convert: packets', "det_sum__cp", 'build/sample_det.pl'),
  file_has('convert: proof accepted while converting', "proof accepted", 'build/sample_det.pl'),
  file_has('convert: proof file written', "clause_packet(", 'build/sample_det.pl.proof'),
  code_free('convert: no cut in output', 'build/sample_det.pl', ["!"]),
  code_free('convert: no ; or -> in output', 'build/sample_det.pl', [";", "->"]),
  file_has('convert: cut event for safe_cut', "cut_to_if_commit(safe_cut/1, clause 1)", 'build/sample_det.pl'),
  file_has('convert: facts to member_cp', "facts_to_member_cp(multi_fact/1, 3 facts)", 'build/sample_det.pl'),
  file_has('convert: output as data', "effect_text(", 'build/sample_det.pl'),
  expect('converted: det_sum packet', "Rows = [[[1, 2, 3], 6]].", [run, '--det', 'build/sample_det.pl', 'det_sum__cp([1,2,3], S, Rows)']),
  exact('converted: safe_cut packet', "Rows = [[1]].", [run, '--det', 'build/sample_det.pl', 'safe_cut__cp(1, Rows)']),
  expect('converted: if_then_else packet', "Rows = [[-1, nonpos]].", [run, '--det', 'build/sample_det.pl', 'if_then_else__cp(-1, Y, Rows)']),
  expect('converted: output is a packet item', "Rows = [out('hi\\n'), [hi]].", [run, '--det', 'build/sample_det.pl', 'side_effect__cp(hi, Rows)']),
  % the proof is checked independently, and tampering is caught
  expect('proof-check: accepted from files', "proof accepted",
         ['proof-check', 'examples/sample_program.pl', 'build/sample_det.pl', 'build/sample_det.pl.proof']),
  replace('build/sample_det.pl', 'build/tampered.pl', "H + Rest", "H - Rest"),
  expect('proof-check: tampered code rejected', "proof rejected",
         ['proof-check', 'examples/sample_program.pl', 'build/tampered.pl', 'build/sample_det.pl.proof']),
  replace('examples/sample_program.pl', 'build/other_source.pl', "S is H + Rest", "S is H * Rest"),
  expect('proof-check: wrong source rejected', "proof rejected",
         ['proof-check', 'build/other_source.pl', 'build/sample_det.pl', 'build/sample_det.pl.proof']),
  replace('build/sample_det.pl.proof', 'build/tampered.proof', "d(det,", "d(effect,"),
  expect('proof-check: tampered proof rejected', "proof rejected",
         ['proof-check', 'examples/sample_program.pl', 'build/sample_det.pl', 'build/tampered.proof']),
  % the splice example
  expect('packets: splice early', "packet: cp([[1, 3], [1, 4], [2, 3], [2, 4]])", [packets, 'examples/splice.pl', 'c(A, B)']),
  expect('packets: enumerate late', "A = 2, B = 4.", [packets, 'examples/splice.pl', 'c(A, B)']),
  run([convert, 'examples/splice.pl', '-o', 'build/splice_det.pl']),
  file_has('convert: splice/2 used', "splice([cp(", 'build/splice_det.pl'),
  file_has('convert: splice event', "splice_early(a(A), b(B))", 'build/splice_det.pl'),
  expect('proof-check: splice', "proof accepted",
         ['proof-check', 'examples/splice.pl', 'build/splice_det.pl', 'build/splice_det.pl.proof']),
  % equivalence: answers and output, identical and in order
  expect('check: sample', "all checks passed",
         [check, 'examples/sample_program.pl', 'det_sum([1,2,3], S)', 'nondet_member(X, [a,b,a])', 'multi_fact(X)',
          'if_then_else(3, Y)', 'if_then_else(0, Y)', 'safe_cut(1)', 'safe_cut(-1)', 'side_effect(hi)']),
  expect('check: cuts', "all checks passed",
         [check, 'examples/cuts.pl', 'a(X)', 'max(5, 3, Z)', 'max(2, 3, Z)', 'max(5, 3, 3)', 'classify(-4, C)',
          'classify(0, C)', 'classify(7, C)', 'firsts([1,2,3], F)', 'two(X, Y)', 'no_big([1,2])', 'no_big([1,9])', 'bang(O)']),
  expect('check: splice', "all checks passed",
         [check, 'examples/splice.pl', 'c(A, B)', 'c(1, B)', 'c(A, A)', 'triple(X, Y, Z)', 'q(X, Y)', 'c(A, B), A < B']),
  expect('check: library', "all checks passed",
         [check, 'examples/sample_program.pl', 'append(X, Y, [1,2,3])', 'select(X, [a,b,c], R)', 'maplist(succ, [1,2,3], L)',
          'permutation([1,2,3], P)', 'nth0(I, [a,b,c], E)', 'msort([c,a,b], S)', 'length(L, 2)',
          'between(1, 4, X), X mod 2 =:= 0', '(X = 1 ; X = 2), \\+ X = 1', 'aggregate_all(count, member(_, [a,b]), N)']),
  expect('check: output order', "all checks passed",
         [check, 'examples/output.pl', show, pairs, 'first_big(X)', 'count_out(N)', 'logged(L)']),
  expect('check: output order (no splice)', "all checks passed",
         [check, '--no-splice', 'examples/output.pl', show, pairs, 'first_big(X)']),
  expect('check: memo example fib', "all checks passed", [check, 'examples/memo.pl', 'fib(10, F)']),
  expect('convert: unsupported cut is reported', "unsupported_cut(pick/2, clause 1)", [convert, 'examples/memo.pl']),
  % memoisation
  expect('memoise: complete table', "ok   pick(5, X)",
         [memoise, 'examples/memo.pl', '--goal', 'pick(2, X)', '--goal', 'pick(5, X)', '--complete',
          '-o', 'build/memo_det.pl', '--check', 'pick(2, X)', '--check', 'pick(5, X)']),
  file_has('memoise: table in output', "memo_lookup(", 'build/memo_det.pl'),
  file_has('memoise: table checked by re-running it', "proof accepted", 'build/memo_det.pl'),
  expect('memoise: answers', "Rows = [[5, big]].", [run, '--det', 'build/memo_det.pl', 'pick__cp(5, X, Rows)']),
  expect('memoise: miss is an error', "memo_miss", [run, '--det', 'build/memo_det.pl', 'pick__cp(9, X, Rows)']),
  expect('memoise: proof-check from files', "proof accepted",
         ['proof-check', 'examples/memo.pl', 'build/memo_det.pl', 'build/memo_det.pl.proof']),
  replace('build/memo_det.pl.proof', 'build/memo_bad.proof', "big", "small"),
  replace('build/memo_det.pl', 'build/memo_bad.pl', "big", "small"),
  expect('memoise: a wrong table is rejected', "proof rejected",
         ['proof-check', 'examples/memo.pl', 'build/memo_bad.pl', 'build/memo_bad.proof']),
  expect('memoise: fib table with fallback', "ok   fib(20, F)",
         [memoise, 'examples/memo.pl', '--goal', 'fib(20, F)', '-o', 'build/fib_det.pl',
          '--check', 'fib(20, F)', '--check', 'fib(7, F)']),
  % mnns bridge (needs SWI-Prolog and mnns)
  mnns
]).
