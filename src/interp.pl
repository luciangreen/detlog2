/*  interp.pl - the detlog2 interpreter: a choicepointless, cutless
    interpreter of Prolog, written in cut-free, choicepoint-free Prolog.

    Every goal denotes an answer packet: a lazy stream of answers and the
    output they write (stream.pl).  Conjunction splices the packet of the
    second goal into every answer of the first; a disjunction or a
    predicate with several clauses concatenates the packets of its
    alternatives.  Alternatives are ordinary data that is spliced
    deterministically:

      * there is no choicepoint stack and no backtracking - failure is the
        empty packet;
      * there is no trail - substitutions are immutable (term.pl), so
        nothing has to be undone;
      * there is no cut - '!' is rejected with an error.  Commitment is
        if_commit/3 (or (C -> T ; E)), once/1 and \+/1, which take the head
        of the condition's packet and never demand the rest.

    Options: opts(MaxDepth, DetCheck, Watch).
*/

default_options(opts(100000, false, [])).

opt_max_depth(opts(M, _, _), M).
opt_det_check(opts(_, D, _), D).
opt_watch(opts(_, _, W), W).

cut_message("cut (!) is not supported by the detlog2 interpreter; convert the program first with `detlog2 convert`, which turns cuts into if_commit/3 decisions").

run_goal(Opts, Prog, Goal, NVars, S) :-
    empty_state(NVars, St),
    solve_goal(Opts, Prog, Goal, St, S).

solve_goal(Opts, Prog, Goal, St, S) :-
    solve(cx(Prog, Opts), 0, Goal, St, S).

%  solve(+Cx, +Depth, +Goal, +State, -Stream)
solve(Cx, D, G0, St, S) :-
    walk(G0, St, G),
    solve_w(G, Cx, D, St, S).

solve_w(var(_, _), _, _, _, S) :-
    inst_err("call/1", S).
solve_w(atom(A), Cx, D, St, S) :-
    atom_goal_kind(A, K),
    solve_atom(K, A, Cx, D, St, S).
solve_w(int(I), _, _, _, S) :-
    type_err(callable, int(I), S).
solve_w(flt(F), _, _, _, S) :-
    type_err(callable, flt(F), S).
solve_w(comp(F, As), Cx, D, St, S) :-
    length(As, N),
    comp_goal_kind(F, N, As, K),
    solve_comp(K, F, As, Cx, D, St, S).

atom_goal_kind(A, K) :-
    if_commit(memberchk(A-K0, [true-true, fail-fail, false-fail, '!'-cut]),
              K = K0,
              K = call).

solve_atom(true, _, _, _, St, [ans(St)]).
solve_atom(fail, _, _, _, _, []).
solve_atom(cut, _, _, _, _, [err(M)]) :-
    cut_message(M).
solve_atom(call, A, Cx, D, St, S) :-
    call_goal(Cx, D, atom(A), A, [], St, S).

%  The control constructs, by name and arity (and, for ;/2, by the shape
%  of its first argument).
comp_goal_kind(F, N, As, K) :-
    if_commit(( F == ';', N =:= 2 ),
              disj_kind(As, K),
              if_commit(control_kind(F, N, K0), K = K0, K = user)).

disj_kind([L, _], K) :-
    if_commit(L = comp('->', [_, _]), K = ite,
              if_commit(L = comp('*->', [_, _]), K = softite, K = disj)).

control_kind(F, N, K) :-
    format(atom(Key), "~w/~w", [F, N]),
    control_table(Key, K).
control_kind(call, N, call) :-
    N >= 1.

:- relation(control_kind/3).

control_table(Key, K) :-
    memberchk(Key-K, [ ',/2'-conj, '->/2'-ifthen, '*->/2'-softthen,
                       'if_commit/3'-commit, 'once/1'-once, 'once_det/1'-once,
                       'ignore/1'-ignore, '\\+/1'-neg, 'not/1'-neg,
                       'decision/2'-decision, 'findall/3'-findall, 'findall/4'-findall,
                       'forall/2'-forall, 'aggregate_all/3'-aggregate,
                       'bagof/3'-bagof, 'setof/3'-setof ]).

solve_comp(conj, _, [A, B], Cx, D, St, S) :-
    bind_s(lz(solve(Cx, D, A, St)), solve(Cx, D, B), S).
solve_comp(ite, _, [comp(_, [C, T]), E], Cx, D, St, S) :-
    commit(Cx, D, C, T, E, St, S).
solve_comp(softite, _, [comp(_, [C, T]), E], Cx, D, St, S) :-
    soft_commit(Cx, D, C, T, E, St, S).
solve_comp(disj, _, [A, B], Cx, D, St, S) :-
    append_s(lz(solve(Cx, D, A, St)), lz(solve(Cx, D, B, St)), S).
solve_comp(ifthen, _, [C, T], Cx, D, St, S) :-
    commit(Cx, D, C, T, atom(fail), St, S).
solve_comp(softthen, _, [C, T], Cx, D, St, S) :-
    bind_s(lz(solve(Cx, D, C, St)), solve(Cx, D, T), S).
solve_comp(commit, _, [C, T, E], Cx, D, St, S) :-
    commit(Cx, D, C, T, E, St, S).
solve_comp(once, _, [X], Cx, D, St, S) :-
    commit(Cx, D, X, atom(true), atom(fail), St, S).
solve_comp(ignore, _, [X], Cx, D, St, S) :-
    commit(Cx, D, X, atom(true), atom(true), St, S).
solve_comp(neg, _, [X], Cx, D, St, S) :-
    negation(Cx, D, X, St, S).
solve_comp(decision, _, [Cases, Def], Cx, D, St, S) :-
    term_to_list(Cases, St, M),
    decision_m(M, Def, Cx, D, St, S).
solve_comp(call, _, [X|Extra], Cx, D, St, S) :-
    walk(X, St, WX),
    add_args(WX, Extra, M),
    call_m(M, X, Cx, D, St, S).
solve_comp(findall, _, As, Cx, D, St, S) :-
    findall_args(As, T, X, L, Tl),
    findall_s(Cx, D, T, X, L, Tl, St, S).
solve_comp(forall, _, [C, A], Cx, D, St, S) :-
    negation(Cx, D, comp(',', [C, comp('\\+', [A])]), St, S).
solve_comp(aggregate, _, [Spec, X, R], Cx, D, St, S) :-
    walk(Spec, St, WS),
    aggregate(WS, X, R, Cx, D, St, S).
solve_comp(bagof, _, [T, X, L], Cx, D, St, S) :-
    collect(false, Cx, D, T, X, L, St, S).
solve_comp(setof, _, [T, X, L], Cx, D, St, S) :-
    collect(true, Cx, D, T, X, L, St, S).
solve_comp(user, F, As, Cx, D, St, S) :-
    call_goal(Cx, D, comp(F, As), F, As, St, S).

findall_args(As, T, X, L, Tl) :-
    length(As, N),
    findall_args_(N, As, T, X, L, Tl).

findall_args_(3, [T, X, L], T, X, L, atom('[]')).
findall_args_(4, [T, X, L, Tl], T, X, L, Tl).

decision_m(just(Cs), Def, Cx, D, St, S) :-
    decision_goal(Cs, Def, G),
    solve(Cx, D, G, St, S).
decision_m(nothing, _, _, _, _, S) :-
    inst_err("decision/2", S).

call_m(just(G), _, Cx, D, St, S) :-
    solve(Cx, D, G, St, S).
call_m(nothing, X, _, _, St, S) :-
    resolve(X, St, R),
    type_err(callable, R, S).

decision_goal([], Def, Def).
decision_goal([C|Cs], Def, G) :-
    if_commit(C = comp('-', [Cond, Body]),
              ( decision_goal(Cs, Def, Rest), G = comp(if_commit, [Cond, Body, Rest]) ),
              G = comp(throw_decision, [C])).

% ---------------------------------------------------------------------------
% Commitment: the head of the condition's packet; the rest is never
% demanded.  No choicepoint is created or removed.

commit(Cx, D, C, T, E, St, lz(commit_scan(lz(solve(Cx, D, C, St)), Cx, D, T, E, St))).

commit_scan(SC, Cx, D, T, E, St, S) :-
    force(SC, F),
    commit_f(F, Cx, D, T, E, St, S).

commit_f([], Cx, D, _, E, St, S) :-
    solve(Cx, D, E, St, S).
commit_f([Ev|Rest], Cx, D, T, E, St, S) :-
    commit_ev(Ev, Rest, Cx, D, T, E, St, S).

commit_ev(out(O), Rest, Cx, D, T, E, St, [out(O)|lz(commit_scan(Rest, Cx, D, T, E, St))]).
commit_ev(err(X), _, _, _, _, _, _, [err(X)]).
commit_ev(ans(S1), _, Cx, D, T, _, _, S) :-
    solve(Cx, D, T, S1, S).

soft_commit(Cx, D, C, T, E, St, lz(soft_scan(lz(solve(Cx, D, C, St)), Cx, D, T, E, St))).

soft_scan(SC, Cx, D, T, E, St, S) :-
    force(SC, F),
    soft_f(F, Cx, D, T, E, St, S).

soft_f([], Cx, D, _, E, St, S) :-
    solve(Cx, D, E, St, S).
soft_f([Ev|Rest], Cx, D, T, E, St, S) :-
    soft_ev(Ev, Rest, Cx, D, T, E, St, S).

soft_ev(out(O), Rest, Cx, D, T, E, St, [out(O)|lz(soft_scan(Rest, Cx, D, T, E, St))]).
soft_ev(err(X), _, _, _, _, _, _, [err(X)]).
soft_ev(ans(S1), Rest, Cx, D, T, _, _, S) :-
    bind_s([ans(S1)|Rest], solve(Cx, D, T), S).

negation(Cx, D, X, St, lz(neg_scan(lz(solve(Cx, D, X, St)), St))).

neg_scan(SX, St, S) :-
    force(SX, F),
    neg_f(F, St, S).

neg_f([], St, [ans(St)]).
neg_f([Ev|Rest], St, S) :-
    neg_ev(Ev, Rest, St, S).

neg_ev(out(O), Rest, St, [out(O)|lz(neg_scan(Rest, St))]).
neg_ev(err(E), _, _, [err(E)]).
neg_ev(ans(_), _, _, []).

% ---------------------------------------------------------------------------
% Collecting a packet into a list term

%  gather(+Cx, +D, +Template, +Goal, +State, +K, -Stream): the outputs of
%  Goal's packet, then call(K, Items, Stream) where Items are
%  ResolvedTemplate-Next pairs.
gather(Cx, D, T, X, St, K, lz(gather_loop(lz(solve(Cx, D, X, St)), T, K, []))).

gather_loop(SX, T, K, Acc, S) :-
    force(SX, F),
    gather_f(F, T, K, Acc, S).

gather_f([], _, K, Acc, S) :-
    rev(Acc, Items),
    call(K, Items, S).
gather_f([Ev|Rest], T, K, Acc, S) :-
    gather_ev(Ev, Rest, T, K, Acc, S).

gather_ev(out(O), Rest, T, K, Acc, [out(O)|lz(gather_loop(Rest, T, K, Acc))]).
gather_ev(err(E), _, _, _, _, [err(E)]).
gather_ev(ans(S1), Rest, T, K, Acc, S) :-
    resolve(T, S1, R),
    st_next(S1, N),
    gather_loop(Rest, T, K, [R-N|Acc], S).

finish_list(Items, St0, Copies, St) :-
    st_next(St0, N0),
    pairs_values(Items, Ns),
    max_list_det([N0|Ns], Max),
    st_set_next(Max, St0, St1),
    pairs_keys(Items, Ts),
    copy_all(St1, Ts, Copies, St).

findall_s(Cx, D, T, X, L, Tl, St, S) :-
    gather(Cx, D, T, X, St, findall_k(L, Tl, St), S).

findall_k(L, Tl, St, Items, S) :-
    finish_list(Items, St, Copies, St1),
    mk_list(Copies, Tl, LT),
    unify(L, LT, St1, M),
    maybe_stream(M, S).

collect(Sorted, Cx, D, T, X, L, St, S) :-
    strip_caret(X, Inner),
    gather(Cx, D, T, Inner, St, collect_k(Sorted, L, St), S).

collect_k(Sorted, L, St, Items, S) :-
    if_commit(Items == [],
              S = [],
              ( finish_list(Items, St, Copies, St1),
                sorted_if(Sorted, St1, Copies, Out),
                mk_list(Out, atom('[]'), LT),
                unify(L, LT, St1, M),
                maybe_stream(M, S) )).

sorted_if(false, _, L, L).
sorted_if(true, St, L, Out) :-
    sort_dedup(St, L, Out).

strip_caret(G, Out) :-
    if_commit(G = comp('^', [_, G1]), strip_caret(G1, Out), Out = G).

aggregate(Spec, X, R, Cx, D, St, S) :-
    if_commit(Spec == atom(count),
              gather(Cx, D, atom(x), X, St, count_k(R, St), S),
    if_commit(Spec = comp(count, [T]),
              gather(Cx, D, T, X, St, count_k(R, St), S),
    if_commit(Spec = comp(sum, [E]),
              gather(Cx, D, E, X, St, sum_k(R, St), S),
    if_commit(Spec = comp(max, [E]),
              gather(Cx, D, E, X, St, extreme_k(max, R, St), S),
    if_commit(Spec = comp(min, [E]),
              gather(Cx, D, E, X, St, extreme_k(min, R, St), S),
    if_commit(Spec = comp(bag, [T]),
              findall_s(Cx, D, T, X, R, atom('[]'), St, S),
    if_commit(Spec = comp(set, [T]),
              gather(Cx, D, T, X, St, set_k(R, St), S),
              type_err('aggregate_all/3 specification', Spec, S)))))))).

count_k(R, St, Items, S) :-
    length(Items, N),
    unify(R, int(N), St, M),
    maybe_stream(M, S).

eval_items([], _, right([])).
eval_items([T-_|Is], St, E) :-
    eval_arith(St, T, R),
    eval_items_(R, Is, St, E).

eval_items_(left(M), _, _, left(M)).
eval_items_(right(V), Is, St, E) :-
    eval_items(Is, St, E1),
    eval_cons(E1, V, E).

eval_cons(left(M), _, left(M)).
eval_cons(right(Vs), V, right([V|Vs])).

sum_k(R, St, Items, S) :-
    eval_items(Items, St, E),
    sum_e(E, R, St, S).

sum_e(left(M), _, _, [err(M)]).
sum_e(right(Vs), R, St, S) :-
    foldl(add_n, Vs, ni(0), Total),
    num_term(Total, T),
    unify(R, T, St, M),
    maybe_stream(M, S).

extreme_k(Which, R, St, Items, S) :-
    eval_items(Items, St, E),
    extreme_e(E, Which, R, St, S).

extreme_e(left(M), _, _, _, [err(M)]).
extreme_e(right(Vs), Which, R, St, S) :-
    extreme_vs(Vs, Which, R, St, S).

extreme_vs([], _, _, _, []).
extreme_vs([V|Vs], Which, R, St, S) :-
    foldl(extreme_step(Which), Vs, V, X),
    num_term(X, T),
    unify(R, T, St, M),
    maybe_stream(M, S).

extreme_step(max, B, A, X) :-
    to_d(A, DA),
    to_d(B, DB),
    if_commit(DA >= DB, X = A, X = B).
extreme_step(min, B, A, X) :-
    to_d(A, DA),
    to_d(B, DB),
    if_commit(DA =< DB, X = A, X = B).

add_n(B, A, C) :-
    if_commit(( A = ni(X), B = ni(Y) ),
              ( Z is X + Y, C = ni(Z) ),
              ( to_d(A, DA), to_d(B, DB), Z is DA + DB, C = nf(Z) )).

set_k(R, St, Items, S) :-
    finish_list(Items, St, Copies, St1),
    sort_dedup(St1, Copies, Out),
    mk_list(Out, atom('[]'), LT),
    unify(R, LT, St1, M),
    maybe_stream(M, S).

%  sort_dedup(+State, +Terms, -Sorted): insertion sort by the standard
%  order, then adjacent duplicates (equal and identical) removed.
sort_dedup(St, Xs, Out) :-
    rev(Xs, R),
    foldl(insert_std(St), R, [], Sorted),
    dedup_ident(Sorted, St, Out).

insert_std(St, X, L, Out) :-
    insert_std_(L, X, St, Out).

insert_std_([], X, _, [X]).
insert_std_([Y|Ys], X, St, Out) :-
    compare_std(St, X, Y, O),
    insert_pick(O, X, Y, Ys, St, Out).

insert_pick(>, X, Y, Ys, St, [Y|Out]) :-
    insert_std_(Ys, X, St, Out).
insert_pick(<, X, Y, Ys, _, [X, Y|Ys]).
insert_pick(=, X, Y, Ys, _, [X, Y|Ys]).

dedup_ident([], _, []).
dedup_ident([X|Xs], St, Out) :-
    dedup_ident_(Xs, X, St, Out).

dedup_ident_([], X, _, [X]).
dedup_ident_([Y|Ys], X, St, Out) :-
    compare_std(St, X, Y, O),
    resolve(X, St, RX),
    resolve(Y, St, RY),
    same_term(RX, RY, Same),
    if_commit(( O == (=), Same == true ),
              dedup_ident_(Ys, X, St, Out),
              ( Out = [X|Out1], dedup_ident_(Ys, Y, St, Out1) )).

% ---------------------------------------------------------------------------
% Calls

call_goal(Cx, D, G, F, As, St, S) :-
    Cx = cx(_, Opts),
    opt_watch(Opts, W),
    watched_use(W, F, As, St, Bad),
    call_goal_(Bad, Cx, D, G, F, As, St, S).

call_goal_(true, _, _, _, F, As, _, [err(M)]) :-
    length(As, N),
    format(string(M), "symbolic run: ~w/~d inspects an input variable, so its result could differ for actual values", [F, N]).
call_goal_(false, Cx, D, G, F, As, St, S) :-
    builtin(F, As, St, MB),
    call_builtin_or_user(MB, Cx, D, G, F, As, St, S).

call_builtin_or_user(just(S), _, _, _, _, _, _, S).
call_builtin_or_user(nothing, Cx, D, G, F, As, St, S) :-
    length(As, N),
    call_user(Cx, D, G, F/N, St, S).

%  In a symbolic run, a built-in whose result depends on whether an input
%  variable is bound (or on its value) would decide for every input what it
%  decided for the unbound variable.  Type tests are unsafe on a watched
%  variable itself; comparisons on any term that contains one.
watched_use([], _, _, _, false).
watched_use([V|Vs], F, As, St, B) :-
    watched_ids([V|Vs], St, Ids),
    length(As, N),
    key_atom(F, N, K),
    if_commit(memberchk(K, ['var/1', 'nonvar/1', 'atom/1', 'number/1', 'integer/1', 'float/1',
                            'atomic/1', 'compound/1', 'callable/1', 'is_list/1']),
              test(( member(A, As), walk(A, St, var(I, _)), memberchk(I, Ids) ), B),
              ( var_sensitive_keys(VK),
                test(( memberchk(K, VK), member(A, As), resolve(A, St, R),
                       term_var_ids(R, RIds), member(I, RIds), memberchk(I, Ids) ), B) )).

watched_ids([], _, []).
watched_ids([V|Vs], St, Ids) :-
    walk(var(V, ''), St, W),
    watched_ids(Vs, St, Ids1),
    if_commit(W = var(I, _), Ids = [I|Ids1], Ids = Ids1).

call_user(Cx, D, G, F/N, St, S) :-
    Cx = cx(Prog, Opts),
    opt_max_depth(Opts, Max),
    if_commit(D >= Max,
              ( format(string(M), "call depth limit (~d) exceeded in ~w/~d", [Max, F, N]), S = [err(M)] ),
              ( prog_lookup(Prog, F/N, MC),
                call_user_m(MC, Cx, D, G, F/N, St, S) )).

call_user_m(nothing, _, _, _, F/N, _, [err(M)]) :-
    format(string(M), "unknown procedure ~w/~d", [F, N]).
call_user_m(just(Cls), Cx, D, G, Key, St, S) :-
    call_clauses(Cls, G, Cx, D, St, S0),
    Cx = cx(_, Opts),
    opt_det_check(Opts, DC),
    det_only_if(DC, Key, S0, S).

call_clauses([], _, _, _, _, []).
call_clauses([C|Cs], G, Cx, D, St, S) :-
    append_s(lz(try_clause(C, G, Cx, D, St)), lz(call_clauses(Cs, G, Cx, D, St)), S).

try_clause(clause(H, B, NV), G, Cx, D, St, S) :-
    st_next(St, Off),
    Next is Off + NV,
    st_set_next(Next, St, St1),
    rename_term(Off, H, H1),
    unify(H1, G, St1, M),
    try_clause_m(M, Off, B, Cx, D, S).

try_clause_m(nothing, _, _, _, _, []).
try_clause_m(just(St2), Off, B, Cx, D, S) :-
    rename_term(Off, B, B1),
    D1 is D + 1,
    solve(Cx, D1, B1, St2, S).

det_only_if(false, _, S, S).
det_only_if(true, Key, S0, lz(det_loop(S0, false, Key))).

det_loop(S0, Seen, Key, S) :-
    force(S0, F),
    det_f(F, Seen, Key, S).

det_f([], _, _, []).
det_f([E|R], Seen, Key, S) :-
    det_ev(E, R, Seen, Key, S).

det_ev(ans(St), R, Seen, F/N, S) :-
    det_ans(Seen, St, R, F/N, S).
det_ev(out(O), R, Seen, Key, [out(O)|lz(det_loop(R, Seen, Key))]).
det_ev(err(E), R, Seen, Key, [err(E)|lz(det_loop(R, Seen, Key))]).

det_ans(true, _, _, F/N, [err(M)]) :-
    format(string(M), "determinism check: ~w/~d gave a second answer, so it would need a choicepoint", [F, N]).
det_ans(false, St, R, Key, [ans(St)|lz(det_loop(R, true, Key))]).
