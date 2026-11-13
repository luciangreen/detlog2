/*  cutfree.pl - check that Prolog sources are cut-free and choicepoint-free.

    swipl tools/cutfree.pl FILE...

    Rules, for every clause of every file:

      1. no cut and no control construct that prunes or backtracks:
         !/0, (;)/2, (->)/2, (*->)/2, (\+)/1, not/1, once/1, ignore/1,
         forall/2 - commitment is if_commit/3 or once_det/1;
      2. no generator (member/2, between/3, append/3, select/3, nth0/3,
         nth1/3, sub_atom/5, clause/2, ...) except where its answers are
         collected or committed: inside findall/3,4, aggregate_all/3,
         limit/2 or the condition of if_commit/3;
      3. clauses of one predicate are told apart by their first argument:
         when a predicate has two or more clauses, every first argument is
         an atomic value or a compound, and no two share the same value or
         name/arity.  First-argument indexing then selects one clause and
         leaves no choicepoint.

    The checker is written under the same rules.
*/

:- use_module('../src/detlog_runtime').

:- initialization(main, main).

main :-
    current_prolog_flag(argv, Args),
    drop_dashes(Args, Files),
    check_files(Files, 0, Bad),
    report_total(Bad).

drop_dashes([], []).
drop_dashes([A|As], Fs) :-
    if_commit(A == '--', Fs = Fs1, Fs = [A|Fs1]),
    drop_dashes(As, Fs1).

report_total(N) :-
    compare(O, N, 0),
    report_total(O, N).

report_total(=, _) :-
    format("cut-free check: no problems~n").
report_total(>, N) :-
    format("cut-free check: ~d problem(s)~n", [N]),
    halt(1).

check_files([], N, N).
check_files([F|Fs], N0, N) :-
    check_file(F, K),
    N1 is N0 + K,
    check_files(Fs, N1, N).

check_file(File, K) :-
    setup_call_cleanup(open(File, read, S),
                       read_all(S, Terms),
                       close(S)),
    clauses_of(Terms, Clauses),
    body_problems(Clauses, P1),
    index_problems(Clauses, P2),
    conc_det(P1, P2, Ps),
    print_problems(Ps, File),
    length(Ps, K).

read_all(S, Terms) :-
    read_term(S, T, [module(detlog_runtime)]),
    if_commit(T == end_of_file,
              Terms = [],
              ( Terms = [T|Ts], read_all(S, Ts) )).

% Clauses as Head-Body, directives dropped.
clauses_of([], []).
clauses_of([T|Ts], Cs) :-
    clause_kind(T, Kind),
    clause_add(Kind, T, Cs, Cs1),
    clauses_of(Ts, Cs1).

clause_kind(T, Kind) :-
    if_commit(T = (:- _),
              Kind = directive,
              if_commit(T = (_ :- _), Kind = rule, Kind = fact)).

clause_add(directive, _, Cs, Cs).
clause_add(rule, (H :- B), [H-B|Cs], Cs).
clause_add(fact, H, [H-true|Cs], Cs).

% ---------------------------------------------------------------------------
% Rules 1 and 2

body_problems([], []).
body_problems([H-B|Cs], Ps) :-
    functor(H, F, N),
    goal_problems(B, plain, F/N, P1),
    body_problems(Cs, P2),
    conc_det(P1, P2, Ps).

%  Ctx: plain (the goal must be deterministic) or collect (its answers are
%  collected or committed).
goal_problems(G, Ctx, Where, Ps) :-
    if_commit(var(G), Ps = [], goal_problems_nv(G, Ctx, Where, Ps)).

goal_problems_nv(G0, Ctx, Where, Ps) :-
    strip_module(G0, _, G),
    functor(G, F, N),
    format(atom(Key), "~w/~w", [F, N]),
    if_commit(banned_control(Key),
              Ps = [Where-control(Key)],
              if_commit(meta_spec(Key, Spec),
                        ( G =.. [_|Args], meta_problems(Spec, Args, Ctx, Where, Ps) ),
                        generator_problem(Ctx, Key, Where, Ps))).

generator_problem(plain, Key, Where, Ps) :-
    if_commit(generator(Key), Ps = [Where-generator(Key)], Ps = []).
generator_problem(collect, _, _, []).

% one spec per argument: g (deterministic goal), c (collected goal),
% - (not a goal)
meta_problems([], [], _, _, []).
meta_problems([S|Ss], [A|As], Ctx, Where, Ps) :-
    arg_problems(S, A, Ctx, Where, P1),
    meta_problems(Ss, As, Ctx, Where, P2),
    conc_det(P1, P2, Ps).

arg_problems(g, A, Ctx, Where, Ps) :-
    goal_problems(A, Ctx, Where, Ps).
arg_problems(c, A, _, Where, Ps) :-
    goal_problems(A, collect, Where, Ps).
arg_problems(-, _, _, _, []).

banned_control('!/0').
banned_control(';/2').
banned_control('->/2').
banned_control('*->/2').
banned_control('\\+/1').
banned_control('not/1').
banned_control('once/1').
banned_control('ignore/1').
banned_control('forall/2').

meta_spec(',/2', [g, g]).
meta_spec('if_commit/3', [c, g, g]).
meta_spec('once_det/1', [c]).
meta_spec('findall/3', [-, c, -]).
meta_spec('findall/4', [-, c, -, -]).
meta_spec('aggregate_all/3', [-, c, -]).
meta_spec('limit/2', [-, c]).
meta_spec('catch/3', [g, -, g]).
meta_spec('call/1', [g]).
meta_spec('with_output_to/2', [-, g]).
meta_spec('setup_call_cleanup/3', [g, g, g]).
meta_spec('call_cleanup/2', [g, g]).
meta_spec('builtin_rows/2', [c, -]).
meta_spec('effect_text/2', [g, -]).

generator('member/2').
generator('select/3').
generator('nth0/3').
generator('nth1/3').
generator('append/3').
generator('append/2').
generator('between/3').
generator('permutation/2').
generator('sub_atom/5').
generator('sub_string/5').
generator('clause/2').
generator('repeat/0').
generator('current_op/3').
generator('current_predicate/1').
generator('last/2').
generator('nb_current/2').

% ---------------------------------------------------------------------------
% Rule 3

index_problems(Clauses, Ps) :-
    keyed(Clauses, Keyed),
    msort(Keyed, Sorted),
    group_keys(Sorted, Groups),
    groups_problems(Groups, Ps).

keyed([], []).
keyed([H-_|Cs], [Key-FirstArg|Ks]) :-
    functor(H, F, N),
    format(atom(Key), "~w/~w", [F, N]),
    first_arg_key(H, N, FirstArg),
    keyed(Cs, Ks).

%  The value first-argument indexing uses: var, an atomic value, or
%  name/arity of a compound.
first_arg_key(H, N, K) :-
    if_commit(N =:= 0,
              K = none,
              ( arg(1, H, A),
                if_commit(var(A),
                          K = var,
                          if_commit(compound(A),
                                    ( functor(A, F, Ar), K = f(F, Ar) ),
                                    K = c(A))) )).

group_keys([], []).
group_keys([K-V|Rest], [K-[V|Vs]|Gs]) :-
    take_key(Rest, K, Vs, Rest1),
    group_keys(Rest1, Gs).

take_key([], _, [], []).
take_key([K1-V|Rest], K, Vs, Out) :-
    if_commit(K1 == K,
              ( Vs = [V|Vs1], take_key(Rest, K, Vs1, Out) ),
              ( Vs = [], Out = [K1-V|Rest] )).

groups_problems([], []).
groups_problems([K-Vs|Gs], Ps) :-
    length(Vs, Count),
    group_problem(Count, K, Vs, P1),
    groups_problems(Gs, P2),
    conc_det(P1, P2, Ps).

group_problem(Count, K, Vs, Ps) :-
    if_commit(Count > 1,
              if_commit(member(var, Vs),
                        Ps = [K-first_argument_unindexed],
                        if_commit(duplicate(Vs, D),
                                  Ps = [K-first_argument_shared(D)],
                                  Ps = [])),
              Ps = []).

%  Semidet: fails when no value occurs twice.
duplicate(Vs, D) :-
    msort(Vs, [X|Xs]),
    adjacent_equal(Xs, X, D).

adjacent_equal([Y|Ys], X, D) :-
    if_commit(X == Y, D = X, adjacent_equal(Ys, Y, D)).

% ---------------------------------------------------------------------------

print_problems([], _).
print_problems([Where-What|Ps], File) :-
    format("~w: ~w: ~q~n", [File, Where, What]),
    print_problems(Ps, File).

conc_det([], L, L).
conc_det([X|Xs], L, [X|Ys]) :-
    conc_det(Xs, L, Ys).
