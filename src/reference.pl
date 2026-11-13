/*  reference.pl - a reference engine with ordinary Prolog cut semantics.

    detlog2's own interpreter (interp.pl) has no cut.  This engine is used
    only as an oracle: to check that converted code gives the same answers,
    in the same order, as the source program (which may contain cuts), and
    to compute memo tables (memo.pl).

    Its stream events are rans(Cut, State), rout(Text) and rerr(Message).
    An answer carries a flag saying whether a cut was executed on the way
    to it; once such an answer has been seen, the remaining alternatives of
    the clause (and of the predicate) are dropped.  Like the interpreter, it
    keeps no choicepoints: the alternatives are lazy stream data.
*/

ref_run(Opts, Prog, G, NV, S) :-
    empty_state(NV, St),
    ref_solve(Opts, Prog, G, St, S).

ref_solve(Opts, Prog, G, St, lz(to_ev_step(lz(solve_r(Prog, Opts, 0, G, St))))).

to_ev_step(R, S) :-
    force(R, F),
    to_ev_f(F, S).

to_ev_f([], []).
to_ev_f([E|T], [E1|lz(to_ev_step(T))]) :-
    to_ev(E, E1).

to_ev(rans(_, St), ans(St)).
to_ev(rout(O), out(O)).
to_ev(rerr(E), err(E)).

%  opaque(+R, -R): a goal opaque to cut (call/1, \+, findall, conditions).
opaque(R, lz(opaque_step(R))).

opaque_step(R, S) :-
    force(R, F),
    opaque_f(F, S).

opaque_f([], []).
opaque_f([E|T], [E1|lz(opaque_step(T))]) :-
    strip_cut(E, E1).

strip_cut(rans(_, St), rans(false, St)).
strip_cut(rout(O), rout(O)).
strip_cut(rerr(E), rerr(E)).

bind_r(R, K, lz(bind_r_step(R, K))).

bind_r_step(R, K, S) :-
    force(R, F),
    bind_r_f(F, K, S).

bind_r_f([], _, []).
bind_r_f([E|T], K, S) :-
    bind_r_ev(E, T, K, S).

bind_r_ev(rout(O), T, K, [rout(O)|lz(bind_r_step(T, K))]).
bind_r_ev(rerr(E), _, _, [rerr(E)]).
bind_r_ev(rans(C, St), T, K, S) :-
    call(K, St, S1),
    bind_r_ans(C, S1, T, K, S).

%  a cut was passed: no alternatives of the left goal
bind_r_ans(true, S1, _, _, lz(mark_cut_step(S1))).
bind_r_ans(false, S1, T, K, S) :-
    append_stop(S1, lz(bind_r_step(T, K)), S).

mark_cut_step(R, S) :-
    force(R, F),
    mark_cut_f(F, S).

mark_cut_f([], []).
mark_cut_f([E|T], [E1|lz(mark_cut_step(T))]) :-
    mark_cut(E, E1).

mark_cut(rans(_, St), rans(true, St)).
mark_cut(rout(O), rout(O)).
mark_cut(rerr(E), rerr(E)).

%  append_stop(+Xs, +Ys, -Zs): append, unless the first packet passed a cut.
append_stop(Xs, Ys, lz(append_stop_step(Xs, Ys))).

append_stop_step(Xs, Ys, S) :-
    force(Xs, F),
    append_stop_f(F, Ys, S).

append_stop_f([], Ys, Ys).
append_stop_f([E|T], Ys, S) :-
    append_stop_ev(E, T, Ys, S).

append_stop_ev(rerr(E), _, _, [rerr(E)]).
append_stop_ev(rout(O), T, Ys, [rout(O)|lz(append_stop_step(T, Ys))]).
append_stop_ev(rans(C, St), T, Ys, S) :-
    append_stop_ans(C, St, T, Ys, S).

append_stop_ans(true, St, T, _, [rans(true, St)|lz(drop_after_cut(T))]).
append_stop_ans(false, St, T, Ys, [rans(false, St)|lz(append_stop_step(T, Ys))]).

drop_after_cut(R, S) :-
    force(R, F),
    drop_after_f(F, S).

drop_after_f([], []).
drop_after_f([E|T], S) :-
    drop_after_ev(E, T, S).

drop_after_ev(rerr(E), _, [rerr(E)]).
drop_after_ev(rout(O), T, [rout(O)|lz(drop_after_cut(T))]).
drop_after_ev(rans(C, St), T, [rans(C, St)|lz(drop_after_cut(T))]).

from_stream(S, lz(from_stream_step(S))).

from_stream_step(S, R) :-
    force(S, F),
    from_stream_f(F, R).

from_stream_f([], []).
from_stream_f([E|T], [E1|lz(from_stream_step(T))]) :-
    from_ev(E, E1).

from_ev(ans(St), rans(false, St)).
from_ev(out(O), rout(O)).
from_ev(err(E), rerr(E)).

% ---------------------------------------------------------------------------

%  solve_r(+Prog, +Opts, +Depth, +Goal, +State, -R)
solve_r(Prog, Opts, D, G0, St, R) :-
    walk(G0, St, G),
    solve_r_w(G, G0, Prog, Opts, D, St, R).

solve_r_w(var(_, _), _, _, _, _, _, [rerr("instantiation error in call/1")]).
solve_r_w(atom(A), _, Prog, Opts, D, St, R) :-
    atom_goal_kind(A, K),
    solve_r_atom(K, A, Prog, Opts, D, St, R).
solve_r_w(int(_), _, _, _, _, _, [rerr("type error: callable")]).
solve_r_w(flt(_), _, _, _, _, _, [rerr("type error: callable")]).
solve_r_w(comp(F, As), G0, Prog, Opts, D, St, R) :-
    length(As, N),
    comp_goal_kind(F, N, As, K),
    solve_r_comp(K, F, As, G0, Prog, Opts, D, St, R).

solve_r_atom(true, _, _, _, _, St, [rans(false, St)]).
solve_r_atom(fail, _, _, _, _, _, []).
solve_r_atom(cut, _, _, _, _, St, [rans(true, St)]).
solve_r_atom(call, A, Prog, Opts, D, St, R) :-
    call_r(atom(A), A, [], Prog, Opts, D, St, R).

go_r(Prog, Opts, D, G, St, lz(solve_r(Prog, Opts, D, G, St))).

solve_r_comp(conj, _, [A, B], _, Prog, Opts, D, St, R) :-
    go_r(Prog, Opts, D, A, St, RA),
    bind_r(RA, solve_r(Prog, Opts, D, B), R).
solve_r_comp(ite, _, [comp(_, [C, T]), E], _, Prog, Opts, D, St, R) :-
    commit_r(Prog, Opts, D, C, T, E, St, R).
solve_r_comp(softite, _, [comp(_, [C, T]), E], _, Prog, Opts, D, St, R) :-
    go_r(Prog, Opts, D, C, St, RC0),
    opaque(RC0, RC),
    R = lz(soft_r_step(RC, Prog, Opts, D, T, E, St)).
solve_r_comp(disj, _, [A, B], _, Prog, Opts, D, St, R) :-
    go_r(Prog, Opts, D, A, St, RA),
    go_r(Prog, Opts, D, B, St, RB),
    append_stop(RA, RB, R).
solve_r_comp(ifthen, _, [C, T], _, Prog, Opts, D, St, R) :-
    commit_r(Prog, Opts, D, C, T, atom(fail), St, R).
solve_r_comp(softthen, _, [C, T], _, Prog, Opts, D, St, R) :-
    go_r(Prog, Opts, D, C, St, RC0),
    opaque(RC0, RC),
    bind_r(RC, solve_r(Prog, Opts, D, T), R).
solve_r_comp(commit, _, [C, T, E], _, Prog, Opts, D, St, R) :-
    commit_r(Prog, Opts, D, C, T, E, St, R).
solve_r_comp(once, _, [X], _, Prog, Opts, D, St, R) :-
    commit_r(Prog, Opts, D, X, atom(true), atom(fail), St, R).
solve_r_comp(ignore, _, [X], _, Prog, Opts, D, St, R) :-
    commit_r(Prog, Opts, D, X, atom(true), atom(true), St, R).
solve_r_comp(neg, _, [X], _, Prog, Opts, D, St, R) :-
    neg_r(Prog, Opts, D, X, St, R).
solve_r_comp(call, _, [X|Extra], _, Prog, Opts, D, St, R) :-
    walk(X, St, WX),
    add_args(WX, Extra, M),
    call_r_m(M, Prog, Opts, D, St, R).
solve_r_comp(forall, _, [C, A], _, Prog, Opts, D, St, R) :-
    neg_r(Prog, Opts, D, comp(',', [C, comp('\\+', [A])]), St, R).
solve_r_comp(decision, _, _, G0, Prog, Opts, D, St, R) :-
    via_interp(G0, Prog, Opts, D, St, R).
solve_r_comp(findall, _, _, G0, Prog, Opts, D, St, R) :-
    via_interp(G0, Prog, Opts, D, St, R).
solve_r_comp(aggregate, _, _, G0, Prog, Opts, D, St, R) :-
    via_interp(G0, Prog, Opts, D, St, R).
solve_r_comp(bagof, _, _, G0, Prog, Opts, D, St, R) :-
    via_interp(G0, Prog, Opts, D, St, R).
solve_r_comp(setof, _, _, G0, Prog, Opts, D, St, R) :-
    via_interp(G0, Prog, Opts, D, St, R).
solve_r_comp(user, F, As, _, Prog, Opts, D, St, R) :-
    call_r(comp(F, As), F, As, Prog, Opts, D, St, R).

call_r_m(just(G), Prog, Opts, D, St, R) :-
    go_r(Prog, Opts, D, G, St, R0),
    opaque(R0, R).
call_r_m(nothing, _, _, _, _, [rerr("type error: callable")]).

soft_r_step(RC, Prog, Opts, D, T, E, St, R) :-
    force(RC, F),
    if_commit(F == [],
              solve_r(Prog, Opts, D, E, St, R),
              bind_r(F, solve_r(Prog, Opts, D, T), R)).

commit_r(Prog, Opts, D, C, T, E, St, lz(commit_r_scan(RC, Prog, Opts, D, T, E, St))) :-
    go_r(Prog, Opts, D, C, St, RC).

commit_r_scan(RC, Prog, Opts, D, T, E, St, R) :-
    force(RC, F),
    commit_r_f(F, Prog, Opts, D, T, E, St, R).

commit_r_f([], Prog, Opts, D, _, E, St, R) :-
    solve_r(Prog, Opts, D, E, St, R).
commit_r_f([Ev|Rest], Prog, Opts, D, T, E, St, R) :-
    commit_r_ev(Ev, Rest, Prog, Opts, D, T, E, St, R).

commit_r_ev(rout(O), Rest, Prog, Opts, D, T, E, St,
            [rout(O)|lz(commit_r_scan(Rest, Prog, Opts, D, T, E, St))]).
commit_r_ev(rerr(X), _, _, _, _, _, _, _, [rerr(X)]).
commit_r_ev(rans(_, S1), _, Prog, Opts, D, T, _, _, R) :-
    solve_r(Prog, Opts, D, T, S1, R).

neg_r(Prog, Opts, D, X, St, lz(neg_r_scan(RX, St))) :-
    go_r(Prog, Opts, D, X, St, RX).

neg_r_scan(RX, St, R) :-
    force(RX, F),
    neg_r_f(F, St, R).

neg_r_f([], St, [rans(false, St)]).
neg_r_f([Ev|Rest], St, R) :-
    neg_r_ev(Ev, Rest, St, R).

neg_r_ev(rout(O), Rest, St, [rout(O)|lz(neg_r_scan(Rest, St))]).
neg_r_ev(rerr(E), _, _, [rerr(E)]).
neg_r_ev(rans(_, _), _, _, []).

%  Meta built-ins whose inner goals are opaque to cut.
via_interp(G0, Prog, Opts, D, St, R) :-
    walk(G0, St, G),
    via_interp_w(G, Prog, Opts, D, St, R).

via_interp_w(G, Prog, Opts, D, St, R) :-
    if_commit(G = comp(findall, [T, X|Rest]),
              findall_r(Rest, T, X, Prog, Opts, D, St, R),
    if_commit(G = comp(decision, [Cases, Def]),
              ( term_to_list(Cases, St, M),
                if_commit(M = just(Cs),
                          ( decision_goal(Cs, Def, DG), solve_r(Prog, Opts, D, DG, St, R) ),
                          R = [rerr("instantiation error in decision/2")]) ),
    if_commit(G = comp(aggregate_all, [Spec, X, Res]),
              aggregate_r(Spec, X, Res, Prog, Opts, D, St, R),
    if_commit(( G = comp(F, [T, X, L]), memberchk(F, [bagof, setof]) ),
              ( strip_caret(X, Inner),
                collect_with(T, Inner, Prog, Opts, D, St, bagof_r_k(F, L), R) ),
              R = [rerr("unsupported meta call")])))).

findall_r(Rest, T, X, Prog, Opts, D, St, R) :-
    collect_with(T, X, Prog, Opts, D, St, findall_r_k(Rest), R).

findall_r_k(Rest, Items, St1, R) :-
    length(Rest, N),
    findall_rest(N, Rest, L, Tl),
    mk_list(Items, Tl, LT),
    unify(L, LT, St1, M),
    maybe_r(M, R).

findall_rest(1, [L], L, atom('[]')).
findall_rest(2, [L, Tl], L, Tl).

maybe_r(nothing, []).
maybe_r(just(St), [rans(false, St)]).

aggregate_r(Spec, X, Res, Prog, Opts, D, St, R) :-
    walk(Spec, St, WS),
    if_commit(WS == atom(count),
              collect_with(atom(x), X, Prog, Opts, D, St, count_r_k(Res), R),
              if_commit(WS = comp(bag, [T]),
                        collect_with(T, X, Prog, Opts, D, St, bag_r_k(Res), R),
                        R = [rerr("aggregate_all/3: only count and bag(T) are supported by the reference engine")])).

count_r_k(Res, Items, St1, R) :-
    length(Items, N),
    unify(Res, int(N), St1, M),
    maybe_r(M, R).

bag_r_k(Res, Items, St1, R) :-
    mk_list(Items, atom('[]'), LT),
    unify(Res, LT, St1, M),
    maybe_r(M, R).

bagof_r_k(F, L, Items, St1, R) :-
    if_commit(Items == [],
              R = [],
              ( if_commit(F == setof, sort_dedup(St1, Items, Out), Out = Items),
                mk_list(Out, atom('[]'), LT),
                unify(L, LT, St1, M),
                maybe_r(M, R) )).

%  collect_with(+T, +X, ..., +K, -R): call(K, Copies, State, R) after the
%  answers of X (opaque to cut); outputs pass through.
collect_with(T, X, Prog, Opts, D, St, K, lz(collect_loop(RX, T, K, St, []))) :-
    go_r(Prog, Opts, D, X, St, RX0),
    opaque(RX0, RX).

collect_loop(RX, T, K, St, Acc, R) :-
    force(RX, F),
    collect_f(F, T, K, St, Acc, R).

collect_f([], _, K, St, Acc, R) :-
    rev(Acc, Items),
    finish_list(Items, St, Copies, St1),
    call(K, Copies, St1, R).
collect_f([Ev|Rest], T, K, St, Acc, R) :-
    collect_ev(Ev, Rest, T, K, St, Acc, R).

collect_ev(rout(O), Rest, T, K, St, Acc, [rout(O)|lz(collect_loop(Rest, T, K, St, Acc))]).
collect_ev(rerr(E), _, _, _, _, _, [rerr(E)]).
collect_ev(rans(_, S1), Rest, T, K, St, Acc, R) :-
    resolve(T, S1, RT),
    st_next(S1, N),
    collect_loop(Rest, T, K, St, [RT-N|Acc], R).

call_r(G, F, As, Prog, Opts, D, St, R) :-
    builtin(F, As, St, MB),
    call_r_b(MB, G, F, As, Prog, Opts, D, St, R).

call_r_b(just(S), _, _, _, _, _, _, _, R) :-
    from_stream(S, R).
call_r_b(nothing, G, F, As, Prog, Opts, D, St, R) :-
    length(As, N),
    opt_max_depth(Opts, Max),
    if_commit(D >= Max,
              ( format(string(M), "call depth limit exceeded in ~w/~d", [F, N]), R = [rerr(M)] ),
              ( prog_lookup(Prog, F/N, MC),
                call_r_user(MC, G, F/N, Prog, Opts, D, St, R) )).

call_r_user(nothing, _, F/N, _, _, _, _, [rerr(M)]) :-
    format(string(M), "unknown procedure ~w/~d", [F, N]).
call_r_user(just(Cls), G, _, Prog, Opts, D, St, R) :-
    clauses_r(Cls, G, Prog, Opts, D, St, R0),
    opaque(R0, R).

clauses_r([], _, _, _, _, _, []).
clauses_r([C|Cs], G, Prog, Opts, D, St, R) :-
    append_stop(lz(try_clause_r(C, G, Prog, Opts, D, St)),
                lz(clauses_r(Cs, G, Prog, Opts, D, St)), R).

try_clause_r(clause(H, B, NV), G, Prog, Opts, D, St, R) :-
    st_next(St, Off),
    Next is Off + NV,
    st_set_next(Next, St, St1),
    rename_term(Off, H, H1),
    unify(H1, G, St1, M),
    try_clause_r_m(M, Off, B, Prog, Opts, D, R).

try_clause_r_m(nothing, _, _, _, _, _, []).
try_clause_r_m(just(St2), Off, B, Prog, Opts, D, R) :-
    rename_term(Off, B, B1),
    D1 is D + 1,
    solve_r(Prog, Opts, D1, B1, St2, R).
