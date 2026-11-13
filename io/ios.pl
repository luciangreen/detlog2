/*  ios.pl - 200 inputs and the outputs they give, from real runs of
    detlog2.

    swipl io/ios.pl make           runs the 200 inputs and writes io/ios.txt
    swipl io/ios.pl check          runs them again and fails if any output changed
    swipl io/ios.pl write FILE     writes the outputs to FILE

    The inputs are made the same way every time (see case_for/2).  Each
    output is everything the command printed (standard output, then
    standard error), with its exit code when that is not 0.
*/

:- use_module('../src/detlog_runtime').
:- use_module(library(process)).

:- initialization(main, main).

title(detlog2).
binary('./build/detlog2').

main :-
    current_prolog_flag(argv, Argv),
    drop_dashes(Argv, Args),
    run_all(Outs),
    render(Outs, Text),
    ios_mode(Args, Text).

drop_dashes([], []).
drop_dashes([A|As], Fs) :-
    if_commit(A == '--', Fs = Fs1, Fs = [A|Fs1]),
    drop_dashes(As, Fs1).

ios_mode(Args, Text) :-
    if_commit(Args = [make],
              ( write_text("io/ios.txt", Text), format("wrote io/ios.txt (200 inputs and outputs)~n") ),
    if_commit(Args = [check],
              check_text(Text),
    if_commit(Args = [write, File],
              write_text(File, Text),
              ( format("usage: ios make | ios check | ios write FILE~n"), halt(2) )))).

write_text(File, Text) :-
    setup_call_cleanup(open(File, write, S, [encoding(utf8)]), write(S, Text), close(S)).

check_text(Text) :-
    read_file_to_string("io/ios.txt", Old, [encoding(utf8)]),
    if_commit(Old == Text,
              format("All 200 inputs give the outputs in io/ios.txt.~n"),
              ( split_string(Old, "\n", "", OL),
                split_string(Text, "\n", "", NL),
                differing(OL, NL, 1, Ds),
                take(20, Ds, D20),
                maplist(show_diff, D20),
                format("Outputs differ from io/ios.txt. If the change is meant, run swipl io/ios.pl make and commit io/ios.txt.~n"),
                halt(1) )).

differing([], _, _, []).
differing([A|As], Bs, N, Ds) :-
    differing_(Bs, A, As, N, Ds).

differing_([], _, _, _, []).
differing_([B|Bs], A, As, N, Ds) :-
    N1 is N + 1,
    differing(As, Bs, N1, Ds1),
    if_commit(A == B, Ds = Ds1, Ds = [N-A-B|Ds1]).

show_diff(N-A-B) :-
    format("line ~d:~n  recorded: ~s~n  now:      ~s~n", [N, A, B]).

take(N, L, T) :-
    compare(O, N, 0),
    take_(O, N, L, T).

take_(<, _, _, []).
take_(=, _, _, []).
take_(>, N, L, T) :-
    take_list(L, N, T).

take_list([], _, []).
take_list([X|Xs], N, [X|T]) :-
    N1 is N - 1,
    take(N1, Xs, T).

nth0_det(I, [X|Xs], Y) :-
    compare(O, I, 0),
    nth0_(O, I, X, Xs, Y).

nth0_(=, _, X, _, X).
nth0_(>, I, _, Xs, Y) :-
    I1 is I - 1,
    nth0_det(I1, Xs, Y).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

% ---------------------------------------------------------------------------
% The 200 inputs

%  Choose element i (from the case number k and a salt) of a list.
pick(K, Salt, Xs, X) :-
    length(Xs, L),
    I is (K * (2 * Salt + 1) + Salt * 7) mod L,
    nth0_det(I, Xs, X).

%  A list of length n from a pool, starting at a place set by k.
pick_n(K, Salt, N, Xs, Out) :-
    length(Xs, L),
    Start is (K * (Salt + 3)) mod L,
    findall(X, ( between(1, N, J), I is (Start + J - 1) mod L, nth0_det(I, Xs, X) ), Out).

show_list(Xs, S) :-
    atomic_list_concat(Xs, ',', A),
    format(string(S), "[~w]", [A]).

pool([3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5]).

case_for(K, Args) :-
    C is K mod 10,
    case_args(C, K, Args).

case_args(0, K, ["run", "examples/sample_program.pl", Q]) :-
    pool(P), N is K mod 6, pick_n(K, 1, N, P, L), show_list(L, LS),
    format(string(Q), "det_sum(~s, S)", [LS]).
case_args(1, K, ["ref", "examples/cuts.pl", Q]) :-
    A is K mod 7, B is (K * 3) mod 7,
    format(string(Q), "max(~d, ~d, Z)", [A, B]).
case_args(2, K, ["check", "examples/cuts.pl", Q]) :-
    A is (K mod 9) - 4,
    format(string(Q), "classify(~d, C)", [A]).
case_args(3, K, ["packets", "examples/splice.pl", Q]) :-
    pick(K, 1, ["c(A, B)", "q(X, Y)", "triple(X, Y, Z)", "c(1, B)", "c(A, A)", "p(X)"], Q).
case_args(4, K, ["check", "examples/sample_program.pl", Q]) :-
    A is (K mod 7) - 3,
    format(string(Q), "if_then_else(~d, Y)", [A]).
case_args(5, K, ["run", "examples/sample_program.pl", Q]) :-
    pool(P), N is 1 + K mod 5, pick_n(K, 2, N, P, L), show_list(L, LS),
    M is K mod 4 + 1,
    format(string(Q), "findall(Y, (member(X, ~s), Y is X * ~d), R)", [LS, M]).
case_args(6, K, ["check", "examples/output.pl", Q]) :-
    pick(K, 2, ["show", "pairs", "first_big(X)", "count_out(N)", "logged(L)"], Q).
case_args(7, K, ["check", "examples/memo.pl", Q]) :-
    A is K mod 13,
    format(string(Q), "fib(~d, F)", [A]).
case_args(8, K, ["check", "examples/cuts.pl", Q]) :-
    pool(P),
    pick_n(K, 3, 3, P, L3), show_list(L3, S3),
    pick_n(K, 4, 3, P, L4), show_list(L4, S4),
    format(string(F), "firsts(~s, F)", [S3]),
    format(string(NB), "no_big(~s)", [S4]),
    pick(K, 3, ["a(X)", "two(X, Y)", F, NB, "bang(O)"], Q).
case_args(9, K, ["check", "examples/sample_program.pl", Q]) :-
    pool(P),
    N5 is K mod 4,
    pick_n(K, 5, N5, P, L5), show_list(L5, S5),
    pick_n(K, 6, 3, P, L6), show_list(L6, S6),
    pick_n(K, 7, 3, P, L7), show_list(L7, S7),
    pick_n(K, 8, 4, P, L8), show_list(L8, S8),
    pick_n(K, 9, 3, P, L9), show_list(L9, S9),
    format(string(A), "append(X, Y, ~s)", [S5]),
    format(string(B), "select(X, ~s, R)", [S6]),
    format(string(C), "nth0(I, ~s, E)", [S7]),
    format(string(D), "msort(~s, S)", [S8]),
    format(string(E), "maplist(succ, ~s, L)", [S9]),
    pick(K, 4, [A, B, C, D, E], Q).

run_all(Outs) :-
    numlist(1, 200, Ks),
    maplist(run_case_k, Ks, Outs).

run_case_k(K, Args-Out) :-
    case_for(K, Args),
    run_case(Args, Out).

run_case(Args, Out) :-
    binary(Bin),
    process_create(Bin, Args, [stdout(pipe(O)), stderr(pipe(E)), process(Pid)]),
    read_string(O, _, OS),
    read_string(E, _, ES),
    close(O),
    close(E),
    process_wait(Pid, Status),
    string_concat(OS, ES, All),
    trim_end(All, Text),
    code_line(Status, CL),
    string_concat(Text, CL, Out).

code_line(Status, CL) :-
    if_commit(Status == exit(0),
              CL = "",
              if_commit(Status = exit(N),
                        format(string(CL), "\n(exit code ~d)", [N]),
                        format(string(CL), "\n(~w)", [Status]))).

trim_end(S, T) :-
    string_codes(S, Cs),
    reverse(Cs, R),
    drop_blank(R, R1),
    reverse(R1, Cs1),
    string_codes(T, Cs1).

drop_blank([], []).
drop_blank([C|Cs], Out) :-
    if_commit(memberchk(C, [0' , 0'\n]), drop_blank(Cs, Out), Out = [C|Cs]).

quote_arg(A, Q) :-
    string_codes(A, Cs),
    if_commit(( Cs \== [], plain_arg(Cs) ),
              Q = A,
              ( foldl(quote_code, Cs, [], RevQ),
                reverse(RevQ, QCs),
                conc([0'\'|QCs], [0'\'], All),
                string_codes(Q, All) )).

plain_arg([]).
plain_arg([C|Cs]) :-
    if_commit(code_type(C, alnum), true, memberchk(C, `/._-`)),
    plain_arg(Cs).

quote_code(C, Acc, Out) :-
    if_commit(C =:= 0'\',
              Q = `'\\''`,
              Q = [C]),
    reverse(Q, RQ),
    conc(RQ, Acc, Out).

render(Outs, Text) :-
    title(T),
    format(string(H), "~w: 200 inputs and outputs, from real runs (swipl io/ios.pl make writes this file; swipl io/ios.pl check checks it).", [T]),
    numlist(1, 200, Ks),
    maplist(render_case, Ks, Outs, Blocks),
    conc([H|Blocks], ["\n"], Parts),
    atomic_list_concat(Parts, '', A),
    atom_string(A, Text).

render_case(I, Args-Out, Block) :-
    title(T),
    maplist(quote_arg, Args, QArgs),
    atomic_list_concat([T|QArgs], ' ', Cmd),
    split_string(Out, "\n", "", Lines),
    out_lines(Lines, Body),
    format(string(Block), "~n~n~d. ~w~n~s", [I, Cmd, Body]).

out_lines([L|Ls], Body) :-
    if_commit(( L == "", Ls == [] ),
              Body = "   => (no output)",
              ( maplist(indent_line, Ls, ILs),
                atomic_list_concat(["   => ", L|ILs], '', A),
                atom_string(A, Body) )).

indent_line(L, S) :-
    format(string(S), "~n      ~s", [L]).
