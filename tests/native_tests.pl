/*  native_tests.pl - run converted (Detlog) programs on plain SWI-Prolog.

    swipl tests/native_tests.pl -- CONVERTED_DIR

    CONVERTED_DIR holds the converter's output for the examples
    (splice.pl, cuts.pl, output.pl, sample_program.pl and memo.pl).  For
    every query, the original program runs on SWI-Prolog itself (with its
    cuts), the converted program runs with src/detlog_runtime.pl only, and
    the two must give the same answers, in the same order, with the same
    output written between them.  Every converted call must leave no
    choicepoint.
*/

:- use_module('../src/detlog_runtime').

:- initialization(main, main).

main :-
    current_prolog_flag(argv, Args),
    last_arg(Args, Dir),
    cases(Cases),
    run_cases(Cases, Dir, 0, 0, Pass, Fail),
    format("~d passed, ~d failed~n", [Pass, Fail]),
    compare(O, Fail, 0),
    finish(O).

finish(=).
finish(>) :-
    halt(1).

last_arg([A|As], Last) :-
    last_of(As, A, Last).

last_of([], A, A).
last_of([B|Bs], _, Last) :-
    last_of(Bs, B, Last).

%  case(Example, ConvertedFile, Query): Query's converted form is the
%  predicate Name__cp with the packet as an extra last argument.
cases([ case(splice, splice, c(_, _)),
        case(splice, splice, triple(_, _, _)),
        case(splice, splice, p(_)),
        case(splice, splice, q(_, _)),
        case(cuts, cuts, a(_)),
        case(cuts, cuts, max(3, 7, _)),
        case(cuts, cuts, max(7, 3, _)),
        case(cuts, cuts, classify(-1, _)),
        case(cuts, cuts, classify(0, _)),
        case(cuts, cuts, classify(5, _)),
        case(cuts, cuts, firsts([1, 2, 3], _)),
        case(cuts, cuts, two(_, _)),
        case(cuts, cuts, no_big([1, 2])),
        case(cuts, cuts, no_big([1, 9])),
        case(cuts, cuts, bang(_)),
        case(output, output, show),
        case(output, output, pairs),
        case(output, output, first_big(_)),
        case(output, output, count_out(_)),
        case(output, output, logged(_)),
        case(sample_program, sample_program, det_sum([1, 2, 3], _)),
        case(sample_program, sample_program, nondet_member(_, [a, b, c])),
        case(sample_program, sample_program, multi_fact(_)),
        case(sample_program, sample_program, if_then_else(5, _)),
        case(sample_program, sample_program, if_then_else(-1, _)),
        case(sample_program, sample_program, safe_cut(1)),
        case(sample_program, sample_program, safe_cut(0)),
        case(sample_program, sample_program, side_effect(hello)),
        case(memo, memo, pick(2, _)),
        case(memo, memo, pick(5, _))
      ]).

run_cases([], _, P, F, P, F).
run_cases([C0|Cs], Dir, P0, F0, P, F) :-
    copy_term(C0, C),
    run_case(C, Dir, Verdict),
    C = case(_, _, Q),
    show(Verdict, Q, P0, F0, P1, F1),
    run_cases(Cs, Dir, P1, F1, P, F).

show(ok(Desc), Q, P0, F, P, F) :-
    P is P0 + 1,
    format("PASS ~q: ~w~n", [Q, Desc]).
show(bad(Why), Q, P, F0, P, F) :-
    F is F0 + 1,
    format("FAIL ~q: ~q~n", [Q, Why]).

run_case(case(Example, Conv, Q), Dir, Verdict) :-
    format(atom(OrigFile), "examples/~w.pl", [Example]),
    format(atom(ConvFile), "~w/~w.pl", [Dir, Conv]),
    format(atom(OM), "orig_~w", [Example]),
    format(atom(CM), "conv_~w", [Conv]),
    load_once(OM, OrigFile, plain),
    load_once(CM, ConvFile, runtime),
    original_items(OM, Q, Orig),
    converted_items(CM, Q, Conv1),
    compare_items(Orig, Conv1, Verdict).

load_once(M, File, Kind) :-
    if_commit(current_module(M), true, load_into(Kind, M, File)).

%  Strings are character lists, as in detlog2.
load_into(plain, M, File) :-
    setup_call_cleanup(open(File, read, S),
                       assert_terms(S, M),
                       close(S)).
load_into(runtime, M, File) :-
    M:set_prolog_flag(double_quotes, chars),
    add_import_module(M, detlog_runtime, start),
    load_files(M:File, [silent(true)]).

assert_terms(S, M) :-
    read_term(S, T, [double_quotes(chars)]),
    if_commit(T == end_of_file,
              true,
              ( assert_term(T, M), assert_terms(S, M) )).

assert_term(T, M) :-
    if_commit(T = (:- _), true, assertz(M:T)).

%  The original: answers of Q (as argument lists) with the output written
%  before each one, as a list of out(Text) and ans(Args) items.
original_items(M, Q, Items) :-
    Q =.. [_|Args],
    catch(with_output_to(string(S), findall(Args, ( M:Q, write('\u0001') ), Answers)),
          E, ( S = "", Answers = [], print_message(error, E) )),
    split_string(S, "\u0001", "", Parts),
    interleave(Answers, Parts, Items).

interleave([], [Last], Items) :-
    tail_out(Last, Items).
interleave([A|As], [P|Ps], Items) :-
    text_items(P, Items, [ans(A)|Rest]),
    interleave(As, Ps, Rest).

tail_out(Text, Items) :-
    text_items(Text, Items, []).

text_items(Text, Items, Tail) :-
    if_commit(Text == "", Items = Tail, Items = [out(Text)|Tail]).

%  The converted program: Name__cp(Args..., Packet), run once.  out/1
%  items next to each other are joined, as the original's output is one
%  stream.
converted_items(M, Q, Items) :-
    Q =.. [F|Args],
    atom_concat(F, '__cp', CF),
    conc(Args, [Packet], CArgs),
    G =.. [CF|CArgs],
    if_commit(catch(call_cleanup(M:G, Det = true), E, Det = threw(E)),
              packet_items(Det, Packet, Items),
              Items = [failed]).

packet_items(Det, Packet, Items) :-
    if_commit(var(Det),
              Items = [left_a_choicepoint],
              packet_items_known(Det, Packet, Items)).

packet_items_known(true, Packet, Items) :-
    rows_items(Packet, Items0),
    join_outs(Items0, Items).
packet_items_known(threw(E), _, [threw(E)]).

rows_items([], []).
rows_items([X|Xs], [I|Is]) :-
    if_commit(X = out(T),
              ( atom_string(T, S), I = out(S) ),
              I = ans(X)),
    rows_items(Xs, Is).

join_outs([], []).
join_outs([I|Is], Out) :-
    join_outs(Is, Rest),
    join_front(I, Rest, Out).

join_front(I, Rest, Out) :-
    if_commit(( I = out(A), Rest = [out(B)|Rest1] ),
              ( string_concat(A, B, AB), Out = [out(AB)|Rest1] ),
              Out = [I|Rest]).

compare_items(Orig, Conv, Verdict) :-
    if_commit(Orig =@= Conv,
              ( count_answers(Orig, N),
                format(atom(D), "~d answer(s) and the output identical", [N]),
                Verdict = ok(D) ),
              Verdict = bad(original(Orig)-converted(Conv))).

count_answers([], 0).
count_answers([I|Is], N) :-
    count_answers(Is, N0),
    answer_weight(I, W),
    N is N0 + W.

answer_weight(I, W) :-
    if_commit(I = ans(_), W = 1, W = 0).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).
