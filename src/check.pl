/*  check.pl - static check that a converted program is choicepoint-free,
    and answer-sequence comparison with the source program.

    The static check enforces a small, sufficient discipline:

      * no cut, no disjunction, no (C -> T), no soft cut, no call/N, no
        findall/3 and no nondeterministic built-in anywhere;
      * the condition of every if_commit/3 is a conjunction of
        deterministic built-ins;
      * every predicate has exactly one clause, or exactly two clauses whose
        first arguments are [] and [_|_] (row iteration).

    Under this discipline at most one clause can match any call that the
    generated code makes, so no call ever has an alternative left.
*/

check_deterministic(P, Problems) :-
    program_clauses(P, KCs),
    prog_order(P, Order),
    sort(Order, Defined),
    maplist(check_pred(Defined), KCs, PLs),
    concat_lists(PLs, Problems).

check_pred(Defined, F/N-Cls, Ps) :-
    format(string(Name), "~w/~d", [F, N]),
    shape_problems(Cls, Name, Shape),
    maplist(check_clause_body(Defined, Name), Cls, BLs),
    concat_lists(BLs, Bodies),
    conc(Shape, Bodies, Ps).

shape_problems(Cls, Name, Ps) :-
    length(Cls, L),
    if_commit(L =:= 1, Ps = [],
    if_commit(( Cls = [A, B], first_arg_shape(A, nil), first_arg_shape(B, cons) ), Ps = [],
              ( format(string(M), "~s: ~d clauses that are not a [] / [_|_] row iteration", [Name, L]),
                Ps = [M] ))).

first_arg_shape(clause(H, _, _), S) :-
    goal_args(H, [A|_]),
    if_commit(A == atom('[]'), S = nil, ( A = comp('.', [_, _]), S = cons )).

check_clause_body(Defined, Name, clause(_, B, _), Ps) :-
    check_body(B, Defined, Name, Ps).

check_body(T, Defined, Name, Ps) :-
    if_commit(T = comp(',', [A, B]),
              ( check_body(A, Defined, Name, PA), check_body(B, Defined, Name, PB), conc(PA, PB, Ps) ),
    if_commit(T == atom(true), Ps = [],
    if_commit(T = comp(if_commit, [C, X, E]),
              ( conj_list(C, Gs),
                findall(M, ( member(G, Gs), if_commit(det_goal(G, Defined), fail, true),
                             show_term_q(G, GS),
                             format(string(M), "~s: if_commit/3 condition is not a deterministic built-in: ~s", [Name, GS]) ),
                        PC),
                check_body(X, Defined, Name, PX),
                check_body(E, Defined, Name, PE),
                concat_lists([PC, PX, PE], Ps) ),
    if_commit(T == atom('!'),
              ( format(string(M), "~s: contains a cut", [Name]), Ps = [M] ),
              check_goal(T, Defined, Name, Ps))))).

check_goal(T, Defined, Name, Ps) :-
    goal_key(T, MK),
    if_commit(MK = just(F/N),
              ( key_atom(F, N, KA),
                nondet_builtin_keys(ND),
                if_commit(forbidden_key(KA),
                          ( format(string(M), "~s: uses ~w/~d", [Name, F, N]), Ps = [M] ),
                if_commit(ord_memberchk(F/N, Defined), Ps = [],
                if_commit(( is_builtin_key(KA, true), if_commit(memberchk(KA, ['atom_concat/3'|ND]), fail, true) ),
                          Ps = [],
                if_commit(is_builtin_key(KA, true),
                          ( format(string(M), "~s: nondeterministic built-in ~w/~d", [Name, F, N]), Ps = [M] ),
                          ( format(string(M), "~s: calls undefined ~w/~d", [Name, F, N]), Ps = [M] ))))) ),
              ( show_term_q(T, TS), format(string(M), "~s: goal is not callable: ~s", [Name, TS]), Ps = [M] )).

det_goal(G, Defined) :-
    goal_key(G, just(F/N)),
    key_atom(F, N, KA),
    is_builtin_key(KA, true),
    if_commit(ord_memberchk(F/N, Defined), fail, true),
    nondet_builtin_keys(ND),
    if_commit(memberchk(KA, ['atom_concat/3'|ND]), fail, true).

forbidden_key(KA) :-
    memberchk(KA, [';/2', '->/2', '*->/2', '\\+/1', 'not/1', 'call/1',
                   'findall/3', 'findall/4', 'forall/2', 'once/1', 'ignore/1',
                   'bagof/3', 'setof/3', 'aggregate_all/3',
                   'call/2', 'call/3', 'call/4', 'call/5', 'call/6', 'call/7', 'call/8']).

% ---------------------------------------------------------------------------
% Outcomes: outcome(Answers, Output, MaybeError, Truncated)

show_outcome(outcome(As, Out, Err, Tr), S) :-
    findall(L, ( member(A, As), format(string(L), "  answer: ~s", [A]) ), L1),
    if_commit(As == [], L2 = ["  (no answers)"], L2 = []),
    if_commit(Out == "", L3 = [], ( haskell_show_string(Out, HS), format(string(L), "  output: ~s", [HS]), L3 = [L] )),
    if_commit(Err = just(E), ( format(string(L4a), "  error: ~s", [E]), L4 = [L4a] ), L4 = []),
    if_commit(Tr == true, L5 = ["  (answer limit reached)"], L5 = []),
    concat_lists([L1, L2, L3, L4, L5], Ls),
    maplist(line_nl, Ls, LNs),
    atomic_list_concat(LNs, A0),
    atom_string(A0, S).

line_nl(L, S) :-
    string_concat(L, "\n", S).

%  haskell_show_string(+Text, -Shown): a string as Haskell's show writes it.
haskell_show_string(T, S) :-
    string_codes(T, Cs),
    hs_escape(Cs, Es),
    conc([0'"|Es], `"`, All),
    string_codes(S, All).

hs_escape([], []).
hs_escape([C|Cs], Out) :-
    hs_char(C, Cs, E),
    hs_escape(Cs, Rest),
    conc(E, Rest, Out).

hs_char(C, Next, E) :-
    if_commit(C =:= 0'", E = `\\"`,
    if_commit(C =:= 0'\\, E = `\\\\`,
    if_commit(C =:= 10, E = `\\n`,
    if_commit(C =:= 9, E = `\\t`,
    if_commit(( C >= 32, C =< 126 ), E = [C],
              ( number_codes(C, D),
                if_commit(( Next = [N|_], is_digit_c(N) ), conc(D, `\\&`, D1), D1 = D),
                E = [0'\\|D1] )))))).

%  source_outcome(+Opts, +Max, +Source, +Goal, +Vars, +NVars, -Outcome):
%  the source run with the reference engine.
source_outcome(Opts, Max, Src, Goal, Vars, NV, O) :-
    with_prelude(Src, P),
    ref_run(Opts, P, Goal, NV, S),
    list_t(Vars, VL),
    source_fold(S, VL, Max, [], "", O).

source_fold(S, VL, K, As, Out, O) :-
    force(S, F),
    source_fold_f(F, VL, K, As, Out, O).

source_fold_f([], _, _, As, Out, outcome(RAs, Out, nothing, false)) :-
    rev(As, RAs).
source_fold_f([E|R], VL, K, As, Out, O) :-
    if_commit(K =:= 0,
              ( rev(As, RAs), O = outcome(RAs, Out, nothing, true) ),
              source_fold_ev(E, R, VL, K, As, Out, O)).

source_fold_ev(ans(St), R, VL, K, As, Out, O) :-
    resolve(VL, St, T),
    show_answer_term(T, A),
    K1 is K - 1,
    source_fold(R, VL, K1, [A|As], Out, O).
source_fold_ev(out(T), R, VL, K, As, Out, O) :-
    string_concat(Out, T, Out1),
    source_fold(R, VL, K, As, Out1, O).
source_fold_ev(err(E), _, _, _, As, Out, outcome(RAs, Out, just(E), false)) :-
    rev(As, RAs).

%  converted_outcome(+Opts, +Max, +Converted, +K, -Outcome): run the
%  converted query packet '$query__cp'(V1, ..., Vk, Rows) once and
%  enumerate its rows.
converted_outcome(opts(MD, _, W), Max, Conv, K, O) :-
    K1 is K - 1,
    findall(var(I, Nm), ( between(0, K1, I), format(atom(Nm), "V~d", [I]) ), Vars),
    RowsV = var(K, 'Rows'),
    conc(Vars, [RowsV], Args),
    cp_name('$query', QN),
    NV is K + 1,
    run_goal(opts(MD, true, W), Conv, comp(QN, Args), NV, S),
    stream_list(S, Evs),
    findall(T, member(out(T), Evs), Ts),
    atomic_list_concat(Ts, OA),
    atom_string(OA, OutText),
    findall(E, member(err(E), Evs), Errs),
    findall(St, member(ans(St), Evs), Sts),
    converted_result(Errs, Sts, RowsV, Max, OutText, O).

converted_result(Errs, Sts, RowsV, Max, OutText, O) :-
    if_commit(Errs = [E|_],
              O = outcome([], OutText, just(E), false),
    if_commit(Sts = [St],
              ( term_to_list(RowsV, St, MI),
                if_commit(MI = just(Items),
                          ( maplist(resolve_in(St), Items, RItems),
                            findall(A, ( member(I, RItems), if_commit(I = comp(out, [_]), fail, true),
                                         show_answer_term(I, A) ), Shown),
                            findall(Tx, member(comp(out, [atom(Tx)]), RItems), POs),
                            atomic_list_concat(POs, PA),
                            atom_string(PA, PacketOut),
                            string_concat(OutText, PacketOut, AllOut),
                            take(Max, Shown, Taken),
                            length(Shown, NS),
                            test(NS > Max, Tr),
                            O = outcome(Taken, AllOut, nothing, Tr) ),
                          O = outcome([], OutText, just("query packet is not a proper list"), false)) ),
    if_commit(Sts == [],
              O = outcome([], OutText, just("the converted query packet failed (it must succeed exactly once)"), false),
              O = outcome([], OutText, just("the converted query packet succeeded more than once"), false)))).

resolve_in(St, T, R) :-
    resolve(T, St, R).
