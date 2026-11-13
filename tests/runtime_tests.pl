/*  runtime_tests.pl - tests of the Detlog runtime in plain SWI-Prolog.

    swipl tests/runtime_tests.pl

    Every test goal is run once and must leave no choicepoint:
      t(Name, Goal, Result, Expected)   succeeds, Result is a variant of Expected
      f(Name, Goal)                     fails
      e(Name, Goal)                     throws detlog_error(_)
*/

:- use_module('../src/detlog_runtime').

:- initialization(main, main).

main :-
    tests(Ts),
    run_all(Ts, 0, 0, Pass, Fail),
    format("~d passed, ~d failed~n", [Pass, Fail]),
    compare(O, Fail, 0),
    finish(O).

finish(=).
finish(>) :-
    halt(1).

run_all([], P, F, P, F).
run_all([T0|Ts], P0, F0, P, F) :-
    copy_term(T0, T),                   % each test has its own variables
    run_one(T, Verdict),
    name_of(T, Name),
    show(Verdict, Name, P0, F0, P1, F1),
    run_all(Ts, P1, F1, P, F).

name_of(T, Name) :-
    arg(1, T, Name).

show(ok, Name, P0, F, P, F) :-
    P is P0 + 1,
    format("PASS ~w~n", [Name]).
show(bad(Why), Name, P, F0, P, F) :-
    F is F0 + 1,
    format("FAIL ~w: ~q~n", [Name, Why]).

%  Run a goal once: Outcome is det, choicepoint, failed or threw(E).
outcome(G, Outcome) :-
    if_commit(catch(call_cleanup(G, Det = true), E, Det = threw(E)),
              det_outcome(Det, Outcome),
              Outcome = failed).

det_outcome(Det, O) :-
    if_commit(var(Det), O = choicepoint, det_known(Det, O)).

det_known(true, det).
det_known(threw(E), threw(E)).

run_one(t(_, G, R, E), V) :-
    outcome(G, O),
    expect_success(O, R, E, V).
run_one(f(_, G), V) :-
    outcome(G, O),
    expect_failure(O, V).
run_one(e(_, G), V) :-
    outcome(G, O),
    expect_error(O, V).

expect_success(det, R, E, V) :-
    if_commit(R =@= E, V = ok, V = bad(got(R))).
expect_success(choicepoint, _, _, bad(left_a_choicepoint)).
expect_success(failed, _, _, bad(failed)).
expect_success(threw(X), _, _, bad(threw(X))).

expect_failure(failed, ok).
expect_failure(det, bad(succeeded)).
expect_failure(choicepoint, bad(succeeded_with_choicepoint)).
expect_failure(threw(X), bad(threw(X))).

expect_error(threw(X), V) :-
    if_commit(X = detlog_error(_), V = ok, V = bad(threw(X))).
expect_error(det, bad(succeeded)).
expect_error(choicepoint, bad(succeeded_with_choicepoint)).
expect_error(failed, bad(failed)).

% ---------------------------------------------------------------------------
% if_commit/3 and once_det/1

% ---------------------------------------------------------------------------
% Choice packets

% ---------------------------------------------------------------------------
% Splicing

% ---------------------------------------------------------------------------
% Deterministic modes, effects, packets, memo tables

% ---------------------------------------------------------------------------
% Converted programs, run natively: the Detlog form of examples/splice.pl
% and examples/cuts.pl, in the style the converter writes (docs/examples.md has its real output).

ex_a__cp(A, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [A], Rows).
ex_b__cp(B, Rows) :-
    member_cp(P, [[3], [4]]),
    cp_filter(P, [B], Rows).
ex_c__cp(A, B, Rows) :-
    if_commit(splice_safe([[A], [B]]),
              ( ex_a__cp(A, RA), ex_b__cp(B, RB),
                splice_extend(RA, [A], [A], PA),
                splice_extend(RB, [B], [B], PB),
                splice([cp(PA), cp(PB)], Combos),
                splice_extend(Combos, [A, B], [[A], [B]], Rows) ),
              Rows = []).

ex_max(X, Y, Z) :-
    if_commit(X >= Y, Z = X, Z = Y).

ex_classify(N, C) :-
    if_commit(N < 0, C = neg, if_commit(N = 0, C = zero, C = pos)).

% ---------------------------------------------------------------------------

tests([
    t(if_commit_else, if_commit(member(X, []), Y = X, Y = none), Y, none),
    t(if_commit_repeat, if_commit(repeat, Y = yes, Y = no), Y, yes),
    t(once_det_first, once_det(member(X, [a, b])), X, a),
    e(member_cp_partial, member_cp(_, [1|_])),
    t(between_cp_empty, between_cp(3, 1, P), P, cp([])),
    e(between_cp_infinite, between_cp(1, inf, _)),
    t(cp_rows_nested, cp_rows(cp([1, cp([2, 3])]), R), R, [[1], [2], [3]]),
    t(cp_filter_facts,
       ( member_cp(P, [[a], [b], [b]]), cp_filter(P, [_], R) ), R, [[a], [b], [b]]),
    t(splice_fixed, splice([fixed, cp([1, 2]), x], R), R,
       [[fixed, 1, x], [fixed, 2, x]]),
    t(splice_no_positions, splice([], R), R, [[]]),
    f(splice_first_none, splice_first([cp([])], _)),
    t(splice_extend_filters,
       splice_extend([[1, a], [2, b]], X, [X, a], R), R, [1]),
    t(rows_concat, rows_concat([[[1]], [], [[2], [3]]], R), R, [[1], [2], [3]]),
    t(splice_safe_disjoint, splice_safe([[A], [B]]), A-B, _-_),
    t(splice_safe_ground, splice_safe([[1], [1]]), x, x),
    t(length_det_make, length_det(L, 2), L, [_, _]),
    t(builtin_rows, builtin_rows(between(1, 3, X), R), R,
       [[between(1, 3, 1)], [between(1, 3, 2)], [between(1, 3, 3)]]),
    t(effect_text, effect_text(write(g(1)), T), T, 'g(1)'),
    t(packet_first, packet_first([out(a), [1], out(b), [2]], Pre, Res), Pre-Res,
       [out(a)]-first([1])),
    t(packet_split, packet_split([out(a), [1], out(b), [2]], O, R), O-R,
       [out(a), out(b)]-[[1], [2]]),
    f(memo_lookup_none, memo_lookup([3, _], [[[2, _], []]], _)),
    t(write_packet, with_output_to(atom(A), write_packet([out(x), [1], out(y)], R)),
       A-R, xy-[[1]]),
    t(converted_max, ex_max(3, 7, Z), Z, 7),
    t(if_commit_first, if_commit(member(X, [1, 2, 3]), Y = X, Y = none), Y, 1),
    t(if_commit_infinite_condition,
       if_commit(( between(1, inf, X), X > 3 ), Y = X, Y = none), Y, 4),
    t(if_commit_binds_condition, if_commit(append(A, B, [1, 2]), true, true), A-B, []-[1, 2]),
    f(once_det_none, once_det(member(_, []))),
    t(member_cp, member_cp(P, [1, 2]), P, cp([1, 2])),
    t(between_cp, between_cp(1, 4, P), P, cp([1, 2, 3, 4])),
    t(between_cp_expression, between_cp(1, 1 + 1, P), P, cp([1, 2])),
    t(cp_rows, cp_rows(cp([a, b]), R), R, [[a], [b]]),
    e(cp_rows_not_packet, cp_rows([a], _)),
    t(cp_filter_bound,
       ( member_cp(P, [[1, x], [2, y], [1, z]]), cp_filter(P, [1, _], R) ),
       R, [[1, x], [1, z]]),
    t(splice_independent, splice([cp([1, 2]), cp([3, 4])], R), R,
       [[1, 3], [1, 4], [2, 3], [2, 4]]),
    t(splice_empty_position, splice([cp([1, 2]), cp([])], R), R, []),
    t(splice_first, splice_first([cp([1, 2]), cp([3, 4])], R), R, [1, 3]),
    t(splice_extend,
       splice_extend([[1], [2], [3]], X-Y, [X], R), R, [1-_, 2-_, 3-_]),
    t(splice_extend_keeps_output,
       splice_extend([out('g(1)'), [1], out('g(2)'), [2]], X, [X], R), R,
       [out('g(1)'), 1, out('g(2)'), 2]),
    e(rows_concat_partial, rows_concat([[[1]]|_], _)),
    f(splice_safe_shared, splice_safe([[A, _], [A]])),
    t(length_det_list, length_det([a, b, c], N), N, 3),
    e(length_det_both_unbound, length_det(_, _)),
    t(builtin_rows_none, builtin_rows(atom(1), R), R, []),
    t(effect_text_format, effect_text(format("~w-~w~n", [a, b]), T), T, 'a-b\n'),
    t(packet_first_none, packet_first([out(a)], Pre, Res), Pre-Res, [out(a)]-none),
    t(memo_lookup,
       memo_lookup([2, _], [[[2, _], [[2, small], [2, other]]], [[5, _], [[5, big]]]], R),
       R, [[2, small], [2, other]]),
    e(memo_miss, memo_miss(pick/2, [3, _])),
    t(converted_splice, ex_c__cp(_, _, R), R, [[1, 3], [1, 4], [2, 3], [2, 4]]),
    t(converted_classify, findall(C, ( member(N, [-1, 0, 5]), ex_classify(N, C) ), Cs), Cs,
       [neg, zero, pos])
]).
