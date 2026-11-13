/*  cut_elim.pl - cut elimination: every cut becomes an explicit decision.

    A predicate whose clauses contain top-level cuts is rewritten into one
    clause whose body is a chain of decisions: the clause H :- G, !, B
    followed by clauses Rest becomes if_commit((Args = HArgs, G), B', Rest'),
    where B' is B with its own later cuts converted (after the first cut the
    remaining clauses are already gone, so the "else" of a later cut is
    fail).  Clauses without a cut become disjunction alternatives
    (Args = HArgs, Body ; Rest').

    Cuts inside opaque contexts (\+, call/N, findall/3, once/1, the
    condition of an if-then-else) are local to that context and are
    converted in place with "else = fail".  A cut inside a disjunction or
    if-then-else branch at the clause level would cut the clause; that
    placement is reported as unsupported rather than guessed.

    Events: cut_to_if_commit(Key, I), local_cut_removed(Key, I),
    unsupported_cut(Key, I, Why).
*/

show_cut_event(cut_to_if_commit(F/N, I), S) :-
    format(string(S), "cut_to_if_commit(~w/~d, clause ~d)", [F, N, I]).
show_cut_event(local_cut_removed(F/N, I), S) :-
    format(string(S), "local_cut_to_if_commit(~w/~d, clause ~d)", [F, N, I]).
show_cut_event(unsupported_cut(F/N, I, Why), S) :-
    format(string(S), "unsupported_cut(~w/~d, clause ~d): ~s", [F, N, I, Why]).

%  has_cut(+Term, -Bool): a cut in a goal position (data such as the string
%  "!" is not a cut).
has_cut(T, B) :-
    test(has_cut_(T), B).

has_cut_(T) :-
    if_commit(T == atom('!'), true,
    if_commit(( T = comp(Op, [A, Bb]), memberchk(Op, [',', ';', '->', '*->', forall]) ),
              if_commit(has_cut_(A), true, has_cut_(Bb)),
    if_commit(T = comp(if_commit, [A, Bb, C]),
              if_commit(has_cut_(A), true, if_commit(has_cut_(Bb), true, has_cut_(C))),
    if_commit(( T = comp(F, [A]), memberchk(F, ['\\+', not, once, once_det, ignore, call]) ),
              has_cut_(A),
    if_commit(T = comp(findall, [_, G, _]), has_cut_(G),
    if_commit(T = comp(aggregate_all, [_, G, _]), has_cut_(G),
              fail)))))).

%  eliminate_cuts(+Program, -Either): right(Program-Events) or
%  left(UnsupportedEvents).
eliminate_cuts(P, E) :-
    program_clauses(P, KCs),
    maplist(elim_kc, KCs, Results),
    bad_events(Results, Bad),
    if_commit(Bad == [],
              ( P = prog(Preds, Order, Ds),
                foldl(put_result, Results, Preds, Preds1),
                good_events(Results, Evs),
                E = right(prog(Preds1, Order, Ds)-Evs) ),
              E = left(Bad)).

elim_kc(K-Cs, K-R) :-
    elim_pred(K, Cs, R).

bad_events([], []).
bad_events([_-R|Rs], Bad) :-
    bad_events(Rs, Bad1),
    bad_of(R, Bad1, Bad).

bad_of(left(Es), Rest, All) :-
    conc(Es, Rest, All).
bad_of(right(_), Rest, Rest).

good_events([], []).
good_events([_-R|Rs], Evs) :-
    good_events(Rs, Evs1),
    good_of(R, Evs1, Evs).

good_of(right(_-Es), Rest, All) :-
    conc(Es, Rest, All).
good_of(left(_), Rest, Rest).

put_result(K-R, M0, M) :-
    put_result_(R, K, M0, M).

put_result_(right(Cs-_), K, M0, M) :-
    map_put(K, Cs, M0, M).
put_result_(left(_), _, M, M).

body_has_cut(clause(_, B, _)) :-
    has_cut_(B).

elim_pred(Key, Cls, R) :-
    if_commit(( member(C, Cls), body_has_cut(C) ),
              elim_pred_cut(Key, Cls, R),
              R = right(Cls-[])).

elim_pred_cut(Key, Cls, R) :-
    % Convert local cuts first, then check what is left at clause level.
    numbered_list(Cls, 1, NCls),
    maplist(local_clause, NCls, Locals),
    local_events(Locals, Key, LocalEvs),
    maplist(local_clause_out, Locals, Cls1),
    numbered_list(Cls1, 1, NCls1),
    problems(NCls1, Key, Problems),
    if_commit(Problems == [],
              if_commit(( member(clause(_, B1, _), Cls1), top_cut(B1) ),
                        merge_pred(Key, NCls1, LocalEvs, R),
                        R = right(Cls1-LocalEvs)),
              R = left(Problems)).

numbered_list([], _, []).
numbered_list([X|Xs], I, [I-X|Ys]) :-
    I1 is I + 1,
    numbered_list(Xs, I1, Ys).

local_clause(I-clause(H, B, NV), I-clause(H, B1, NV)-Changed) :-
    local_cuts(B, B1, Changed).

local_clause_out(_-C-_, C).

local_events([], _, []).
local_events([I-_-Ch|Ls], Key, Evs) :-
    local_events(Ls, Key, Rest),
    if_commit(Ch == true, Evs = [local_cut_removed(Key, I)|Rest], Evs = Rest).

problems([], _, []).
problems([I-clause(_, B, _)|Cs], Key, Ps) :-
    problems(Cs, Key, Rest),
    bad_placement(B, MW),
    problem_of(MW, Key, I, Rest, Ps).

problem_of(nothing, _, _, Rest, Rest).
problem_of(just(Why), Key, I, Rest, [unsupported_cut(Key, I, Why)|Rest]).

%  Merge the predicate into one clause of decisions.
merge_pred(F/Arity, NCls, LocalEvs, right([clause(HeadT, Alts, MaxV)]-Evs)) :-
    head_args(0, Arity, Args),
    rev(NCls, Rev),
    foldl(alt_step(F/Arity, Args), Rev, atom(fail)-Arity-[], Alts-_-AltEvs),
    if_commit(Arity =:= 0, HeadT = atom(F), HeadT = comp(F, Args)),
    max_var_id(comp(x, [HeadT, Alts]), M0),
    MaxV is M0 + 1,
    conc(LocalEvs, AltEvs, Evs).

head_args(I, N, Args) :-
    if_commit(I >= N,
              Args = [],
              ( I1 is I + 1,
                format(atom(Name), "A~d", [I1]),
                head_args(I1, N, Rest),
                Args = [var(I, Name)|Rest] )).

%  Fold from the last clause: build "this clause, else the rest".
alt_step(Key, Args, I-clause(H0, B0, NV), Rest-Off-Evs, Alt-Off1-Evs1) :-
    rename_term(Off, H0, H),
    rename_term(Off, B0, B),
    Off1 is Off + NV,
    head_match(H, Args, Match),
    conj_list(B, Gs),
    split_at_cut(Gs, MS),
    alt_build(MS, Key, I, Match, B, Rest, Evs, Alt, Evs1).

head_match(H, Args, Match) :-
    if_commit(H = comp(_, HArgs),
              ( maplist(eq_goal, Args, HArgs, Eqs), mk_conj(Eqs, Match) ),
              Match = atom(true)).

eq_goal(A, X, comp('=', [A, X])).

alt_build(just(Guard-After), Key, I, Match, _, Rest, Evs,
          comp(if_commit, [Cond, AfterT, Rest]), [cut_to_if_commit(Key, I)|Evs]) :-
    conj_list(Match, MGs),
    conc(MGs, Guard, CGs),
    mk_conj(CGs, Cond),
    after_cuts(After, AfterT).
alt_build(nothing, _, _, Match, B, Rest, Evs, Alt, Evs) :-
    conj_list(Match, MGs),
    conj_list(B, BGs),
    conc(MGs, BGs, Gs),
    mk_conj(Gs, X),
    disj_alt(X, Rest, Alt).

disj_alt(X, Rest, Alt) :-
    if_commit(Rest == atom(fail), Alt = X, Alt = comp(';', [X, Rest])).

%  Goals after the first cut: later cuts commit with "else fail".
after_cuts(Gs, T) :-
    split_at_cut(Gs, MS),
    after_cuts_(MS, Gs, T).

after_cuts_(just(G-Rest), _, comp(if_commit, [C, A, atom(fail)])) :-
    mk_conj(G, C),
    after_cuts(Rest, A).
after_cuts_(nothing, Gs, T) :-
    mk_conj(Gs, T).

%  split_at_cut(+Goals, -Maybe): just(Before-After) at the first '!'.
split_at_cut(Gs, M) :-
    split_cut_(Gs, [], M).

split_cut_([], _, nothing).
split_cut_([G|Gs], Acc, M) :-
    if_commit(G == atom('!'),
              ( rev(Acc, Before), M = just(Before-Gs) ),
              split_cut_(Gs, [G|Acc], M)).

top_cut(B) :-
    conj_list(B, Gs),
    memberchk(atom('!'), Gs).

%  A cut not at the top level of the clause body, and not local.
bad_placement(B, M) :-
    conj_list(B, Gs),
    if_commit(( member(G, Gs), G \== atom('!'), has_cut_(G) ),
              ( describe_goal(G, D),
                format(string(Why), "cut inside ~w cuts the clause; memoise this predicate instead", [D]),
                M = just(Why) ),
              M = nothing).

describe_goal(G, D) :-
    if_commit(G = comp(';', [comp('->', _), _]), D = 'an if-then-else branch',
    if_commit(G = comp(';', _), D = 'a disjunction',
    if_commit(G = comp('->', _), D = 'an if-then branch',
              D = 'a goal'))).

%  local_cuts(+Body, -Body, -Changed): convert cuts local to opaque goals.
local_cuts(T, T1, Ch) :-
    local_shape(T, Shape),
    local_cuts_(Shape, T, T1, Ch).

local_shape(T, Shape) :-
    if_commit(T = comp(',', [_, _]), Shape = pair,
    if_commit(T = comp(';', [comp('->', [_, _]), _]), Shape = ite,
    if_commit(T = comp(';', [_, _]), Shape = pair,
    if_commit(T = comp('->', [_, _]), Shape = ifthen,
    if_commit(( T = comp(F, [_]), memberchk(F, ['\\+', not, once, ignore, call]) ), Shape = wrap1,
    if_commit(T = comp(findall, [_, _, _]), Shape = findall,
    if_commit(T = comp(forall, [_, _]), Shape = forall,
    if_commit(T = comp(aggregate_all, [_, _, _]), Shape = aggregate,
              Shape = other)))))))).

local_cuts_(pair, comp(Op, [A, B]), comp(Op, [A1, B1]), Ch) :-
    local_cuts(A, A1, C1),
    local_cuts(B, B1, C2),
    bool_or(C1, C2, Ch).
local_cuts_(ite, comp(';', [comp('->', [C, X]), E]), comp(';', [comp('->', [C1, X1]), E1]), Ch) :-
    opaque_body(C, C1, Ch1),
    local_cuts(X, X1, Ch2),
    local_cuts(E, E1, Ch3),
    bool_or(Ch1, Ch2, Ch12),
    bool_or(Ch12, Ch3, Ch).
local_cuts_(ifthen, comp('->', [C, X]), comp('->', [C1, X1]), Ch) :-
    opaque_body(C, C1, Ch1),
    local_cuts(X, X1, Ch2),
    bool_or(Ch1, Ch2, Ch).
local_cuts_(wrap1, comp(F, [G]), comp(F, [G1]), Ch) :-
    opaque_body(G, G1, Ch).
local_cuts_(findall, comp(findall, [X, G, L]), comp(findall, [X, G1, L]), Ch) :-
    opaque_body(G, G1, Ch).
local_cuts_(forall, comp(forall, [C, A]), comp(forall, [C1, A1]), Ch) :-
    opaque_body(C, C1, Ch1),
    opaque_body(A, A1, Ch2),
    bool_or(Ch1, Ch2, Ch).
local_cuts_(aggregate, comp(aggregate_all, [S, G, R]), comp(aggregate_all, [S, G1, R]), Ch) :-
    opaque_body(G, G1, Ch).
local_cuts_(other, T, T, false).

%  A goal run as its own cut barrier: G1, !, G2 means if_commit(G1, G2, fail).
opaque_body(G, G2, Ch) :-
    local_cuts(G, G1, Ch1),
    if_commit(top_cut(G1),
              ( conj_list(G1, Gs), after_cuts_barrier(Gs, G2), Ch = true ),
              ( G2 = G1, Ch = Ch1 )).

after_cuts_barrier(Gs, T) :-
    split_at_cut(Gs, MS),
    after_barrier_(MS, Gs, T).

after_barrier_(just(Before-After), _, comp(if_commit, [C, A, atom(fail)])) :-
    mk_conj(Before, C),
    after_cuts_barrier(After, A).
after_barrier_(nothing, Gs, T) :-
    mk_conj(Gs, T).
