/*  term.pl - terms, immutable substitutions and unification.

    Object terms are data, never Prolog variables:

      var(Id, Name)   a variable: an integer id and its display name (atom)
      atom(A)         an atom
      int(I)          an integer
      flt(F)          a float
      comp(F, Args)   a compound: functor name and argument list

    A state st(Sub, Next) holds the bindings (an AVL tree from variable id
    to term, as library(assoc) builds it) and the next fresh variable id.
    Substitutions are immutable, so nothing is ever undone: a unification
    that fails gives `nothing`, and the interpreter needs no trail and no
    choicepoint stack.

    Results that may be absent are maybe values (`nothing` or `just(X)`);
    tests return the booleans true and false.  Every predicate here is
    deterministic.
*/

% ---------------------------------------------------------------------------
% Maps (AVL trees of library(assoc)), looked up without choicepoints

map_empty(t).

%  map_get(+Map, +Key, -Maybe)
map_get(t, _, nothing).
map_get(t(K1, V1, _, L, R), K, M) :-
    compare(O, K, K1),
    map_get_(O, V1, L, R, K, M).

map_get_(=, V, _, _, _, just(V)).
map_get_(<, _, L, _, K, M) :-
    map_get(L, K, M).
map_get_(>, _, _, R, K, M) :-
    map_get(R, K, M).

map_put(K, V, M0, M) :-
    put_assoc(K, M0, V, M).

%  map_find(+Map, +Key, +Default, -Value)
map_find(Map, K, D, V) :-
    map_get(Map, K, M),
    maybe_default(M, D, V).

maybe_default(nothing, D, D).
maybe_default(just(V), _, V).

map_member(Map, K, B) :-
    map_get(Map, K, M),
    is_just(M, B).

is_just(nothing, false).
is_just(just(_), true).

map_from_pairs(Pairs, Map) :-
    map_empty(E),
    map_put_pairs(Pairs, E, Map).

map_put_pairs([], M, M).
map_put_pairs([K-V|Ps], M0, M) :-
    map_put(K, V, M0, M1),
    map_put_pairs(Ps, M1, M).

map_pairs(Map, Pairs) :-
    assoc_to_list(Map, Pairs).

map_keys(Map, Keys) :-
    assoc_to_keys(Map, Keys).

% ---------------------------------------------------------------------------
% Booleans and small list helpers

bool_not(true, false).
bool_not(false, true).

bool_and(true, B, B).
bool_and(false, _, false).

bool_or(true, _, true).
bool_or(false, B, B).

%  test(:Goal, -Bool): whether Goal has an answer (its bindings are kept).
test(G, B) :-
    if_commit(G, B = true, B = false).

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

concat_lists([], []).
concat_lists([L|Ls], Out) :-
    concat_lists(Ls, Rest),
    conc(L, Rest, Out).

rev(L, R) :-
    rev_(L, [], R).

rev_([], A, A).
rev_([X|Xs], A, R) :-
    rev_(Xs, [X|A], R).

%  nth_det(+Index1, +List, -Maybe)
nth_det(I, L, M) :-
    compare(O, I, 1),
    nth_det_(O, I, L, M).

nth_det_(<, _, _, nothing).
nth_det_(=, _, L, M) :-
    head_maybe(L, M).
nth_det_(>, I, L, M) :-
    tail_nth(L, I, M).

tail_nth([], _, nothing).
tail_nth([_|Xs], I, M) :-
    I1 is I - 1,
    nth_det(I1, Xs, M).

head_maybe([], nothing).
head_maybe([X|_], just(X)).

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

drop(N, L, D) :-
    compare(O, N, 0),
    drop_(O, N, L, D).

drop_(<, _, L, L).
drop_(=, _, L, L).
drop_(>, N, L, D) :-
    drop_list(L, N, D).

drop_list([], _, []).
drop_list([_|Xs], N, D) :-
    N1 is N - 1,
    drop(N1, Xs, D).

%  elem(+X, +List, -Bool): X == some element (structural identity).
elem(X, L, B) :-
    elem_(L, X, B).

elem_([], _, false).
elem_([Y|Ys], X, B) :-
    test(X == Y, B1),
    elem_more(B1, Ys, X, B).

elem_more(true, _, _, true).
elem_more(false, Ys, X, B) :-
    elem_(Ys, X, B).

max_list_det([X|Xs], M) :-
    foldl(max_step, Xs, X, M).

max_step(X, A, M) :-
    M is max(A, X).

sum_ints(L, S) :-
    foldl(plus_step, L, 0, S).

plus_step(X, A, S) :-
    S is A + X.

% ---------------------------------------------------------------------------
% States

empty_state(N, st(T, N)) :-
    map_empty(T).

st_next(st(_, N), N).

st_set_next(N, st(S, _), st(S, N)).

st_sub(st(S, _), S).

st_set_sub(S, st(_, N), st(S, N)).

%  walk(+Term, +State, -Walked)
walk(var(I, N), St, W) :-
    St = st(Sub, _),
    map_get(Sub, I, M),
    walk_var(M, var(I, N), St, W).
walk(atom(A), _, atom(A)).
walk(int(I), _, int(I)).
walk(flt(F), _, flt(F)).
walk(comp(F, As), _, comp(F, As)).

walk_var(nothing, V, _, V).
walk_var(just(T), _, St, W) :-
    walk(T, St, W).

%  resolve(+Term, +State, -Resolved): fully dereference.
resolve(T, St, R) :-
    walk(T, St, W),
    resolve_w(W, St, R).

resolve_w(var(I, N), _, var(I, N)).
resolve_w(atom(A), _, atom(A)).
resolve_w(int(I), _, int(I)).
resolve_w(flt(F), _, flt(F)).
resolve_w(comp(F, As), St, comp(F, Rs)) :-
    resolve_list(As, St, Rs).

resolve_list([], _, []).
resolve_list([A|As], St, [R|Rs]) :-
    resolve(A, St, R),
    resolve_list(As, St, Rs).

bind(I, T, st(Sub, N), st(Sub1, N)) :-
    map_put(I, T, Sub, Sub1).

%  unify(+A, +B, +State, -MaybeState): unification without occurs check.
unify(A, B, St, M) :-
    walk(A, St, WA),
    walk(B, St, WB),
    unify_w(WA, WB, St, M).

unify_w(var(I, _), B, St, M) :-
    unify_var(B, I, St, M).
unify_w(atom(X), B, St, M) :-
    unify_atom(B, X, St, M).
unify_w(int(X), B, St, M) :-
    unify_int(B, X, St, M).
unify_w(flt(X), B, St, M) :-
    unify_flt(B, X, St, M).
unify_w(comp(F, As), B, St, M) :-
    unify_comp(B, F, As, St, M).

unify_var(var(J, N), I, St, M) :-
    compare(O, I, J),
    unify_vv(O, I, var(J, N), St, M).
unify_var(atom(X), I, St, just(St1)) :-
    bind(I, atom(X), St, St1).
unify_var(int(X), I, St, just(St1)) :-
    bind(I, int(X), St, St1).
unify_var(flt(X), I, St, just(St1)) :-
    bind(I, flt(X), St, St1).
unify_var(comp(F, As), I, St, just(St1)) :-
    bind(I, comp(F, As), St, St1).

unify_vv(=, _, _, St, just(St)).
unify_vv(<, I, V, St, just(St1)) :-
    bind(I, V, St, St1).
unify_vv(>, I, V, St, just(St1)) :-
    bind(I, V, St, St1).

unify_atom(var(J, _), X, St, just(St1)) :-
    bind(J, atom(X), St, St1).
unify_atom(atom(Y), X, St, M) :-
    compare(O, X, Y),
    eq_state(O, St, M).
unify_atom(int(_), _, _, nothing).
unify_atom(flt(_), _, _, nothing).
unify_atom(comp(_, _), _, _, nothing).

unify_int(var(J, _), X, St, just(St1)) :-
    bind(J, int(X), St, St1).
unify_int(atom(_), _, _, nothing).
unify_int(int(Y), X, St, M) :-
    compare(O, X, Y),
    eq_state(O, St, M).
unify_int(flt(_), _, _, nothing).
unify_int(comp(_, _), _, _, nothing).

unify_flt(var(J, _), X, St, just(St1)) :-
    bind(J, flt(X), St, St1).
unify_flt(atom(_), _, _, nothing).
unify_flt(int(_), _, _, nothing).
unify_flt(flt(Y), X, St, M) :-
    test(X =:= Y, B),
    eq_bool(B, St, M).
unify_flt(comp(_, _), _, _, nothing).

unify_comp(var(J, _), F, As, St, just(St1)) :-
    bind(J, comp(F, As), St, St1).
unify_comp(atom(_), _, _, _, nothing).
unify_comp(int(_), _, _, _, nothing).
unify_comp(flt(_), _, _, _, nothing).
unify_comp(comp(G, Bs), F, As, St, M) :-
    same_functor(F, As, G, Bs, B),
    unify_comp_(B, As, Bs, St, M).

unify_comp_(false, _, _, _, nothing).
unify_comp_(true, As, Bs, St, M) :-
    unify_args(As, Bs, St, M).

same_functor(F, As, G, Bs, B) :-
    length(As, N),
    length(Bs, K),
    test(( F == G, N =:= K ), B).

eq_state(=, St, just(St)).
eq_state(<, _, nothing).
eq_state(>, _, nothing).

eq_bool(true, St, just(St)).
eq_bool(false, _, nothing).

unify_args([], _, St, just(St)).
unify_args([A|As], Bs, St, M) :-
    unify_args_(Bs, A, As, St, M).

unify_args_([], _, _, _, nothing).
unify_args_([B|Bs], A, As, St, M) :-
    unify(A, B, St, M1),
    unify_args_more(M1, As, Bs, M).

unify_args_more(nothing, _, _, nothing).
unify_args_more(just(St), As, Bs, M) :-
    unify_args(As, Bs, St, M).

%  unify_then(+A, +B, +MaybeState, -MaybeState): Maybe's >>= for unify.
unify_then(_, _, nothing, nothing).
unify_then(A, B, just(St), M) :-
    unify(A, B, St, M).

% ---------------------------------------------------------------------------
% Lists as terms

mk_list([], Tl, Tl).
mk_list([X|Xs], Tl, comp('.', [X, T])) :-
    mk_list(Xs, Tl, T).

%  term_to_list(+Term, +State, -MaybeList)
term_to_list(T, St, M) :-
    walk(T, St, W),
    term_to_list_w(W, St, M).

term_to_list_w(var(_, _), _, nothing).
term_to_list_w(atom(A), _, M) :-
    test(A == '[]', B),
    nil_list(B, M).
term_to_list_w(int(_), _, nothing).
term_to_list_w(flt(_), _, nothing).
term_to_list_w(comp(F, As), St, M) :-
    cons_parts(F, As, C),
    term_to_list_cons(C, St, M).

nil_list(true, just([])).
nil_list(false, nothing).

%  cons_parts(+Functor, +Args, -Cons): cons(H, T) for '.'/2, or none.
cons_parts(F, As, C) :-
    if_commit(( F == '.', As = [H, T] ), C = cons(H, T), C = none).

term_to_list_cons(none, _, nothing).
term_to_list_cons(cons(H, T), St, M) :-
    walk(H, St, WH),
    term_to_list(T, St, MT),
    maybe_cons(MT, WH, M).

maybe_cons(nothing, _, nothing).
maybe_cons(just(Xs), X, just([X|Xs])).

%  partial_list(+Term, +State, -Items, -End)
partial_list(T, St, Xs, End) :-
    walk(T, St, W),
    partial_w(W, St, Xs, End).

partial_w(var(I, N), _, [], var(I, N)).
partial_w(atom(A), _, [], atom(A)).
partial_w(int(I), _, [], int(I)).
partial_w(flt(F), _, [], flt(F)).
partial_w(comp(F, As), St, Xs, End) :-
    cons_parts(F, As, C),
    partial_cons(C, comp(F, As), St, Xs, End).

partial_cons(none, T, _, [], T).
partial_cons(cons(H, T), _, St, [WH|Xs], End) :-
    walk(H, St, WH),
    partial_list(T, St, Xs, End).

%  char_list(+Text, -Term): a text as a list of one-character atoms.
char_list(Text, T) :-
    atom_chars(Text, Cs),
    char_atoms(Cs, As),
    mk_list(As, atom('[]'), T).

char_atoms([], []).
char_atoms([C|Cs], [atom(C)|As]) :-
    char_atoms(Cs, As).

% ---------------------------------------------------------------------------
% Variables of terms

%  term_var_ids(+Term, -OrdSet)
term_var_ids(T, S) :-
    var_ids_acc(T, [], L),
    sort(L, S).

var_ids_acc(var(I, _), A, [I|A]).
var_ids_acc(atom(_), A, A).
var_ids_acc(int(_), A, A).
var_ids_acc(flt(_), A, A).
var_ids_acc(comp(_, As), A0, A) :-
    foldl(var_ids_acc, As, A0, A).

%  term_vars_ordered(+Term, -Vars): var/2 terms in order of first occurrence.
term_vars_ordered(T, Vs) :-
    vars_ord(T, [], [], _, Rev),
    rev(Rev, Vs).

vars_ord(var(I, N), Seen, Out, Seen1, Out1) :-
    elem(I, Seen, B),
    vars_ord_var(B, I, N, Seen, Out, Seen1, Out1).
vars_ord(atom(_), S, O, S, O).
vars_ord(int(_), S, O, S, O).
vars_ord(flt(_), S, O, S, O).
vars_ord(comp(_, As), S0, O0, S, O) :-
    vars_ord_list(As, S0, O0, S, O).

vars_ord_var(true, _, _, S, O, S, O).
vars_ord_var(false, I, N, S, O, [I|S], [var(I, N)|O]).

vars_ord_list([], S, O, S, O).
vars_ord_list([A|As], S0, O0, S, O) :-
    vars_ord(A, S0, O0, S1, O1),
    vars_ord_list(As, S1, O1, S, O).

%  rename_term(+Offset, +Term, -Renamed)
rename_term(Off, var(I, N), var(J, N)) :-
    J is I + Off.
rename_term(_, atom(A), atom(A)).
rename_term(_, int(I), int(I)).
rename_term(_, flt(F), flt(F)).
rename_term(Off, comp(F, As), comp(F, Rs)) :-
    rename_list(As, Off, Rs).

rename_list([], _, []).
rename_list([A|As], Off, [R|Rs]) :-
    rename_term(Off, A, R),
    rename_list(As, Off, Rs).

max_var_id(var(I, _), I).
max_var_id(atom(_), -1).
max_var_id(int(_), -1).
max_var_id(flt(_), -1).
max_var_id(comp(_, As), M) :-
    max_var_ids(As, -1, M).

max_var_ids([], M, M).
max_var_ids([A|As], M0, M) :-
    max_var_id(A, K),
    M1 is max(M0, K),
    max_var_ids(As, M1, M).

%  fresh_var(+Name, +State, -Var, -State)
fresh_var(N, st(S, I), var(I, N), st(S, I1)) :-
    I1 is I + 1.

fresh_vars(K, St0, Vs, St) :-
    compare(O, K, 0),
    fresh_vars_(O, K, St0, Vs, St).

fresh_vars_(=, _, St, [], St).
fresh_vars_(<, _, St, [], St).
fresh_vars_(>, K, St0, [V|Vs], St) :-
    fresh_var('_', St0, V, St1),
    K1 is K - 1,
    fresh_vars(K1, St1, Vs, St).

%  copy_term_st(+State, +Term, -Copy, -State): resolve, then rename every
%  unbound variable freshly.
copy_term_st(St, T0, C, St1) :-
    resolve(T0, St, T),
    term_var_ids(T, Vs),
    st_next(St, Base),
    numbered(Vs, Base, Pairs),
    map_from_pairs(Pairs, Table),
    rename_by(T, Table, C),
    length(Vs, K),
    Next is Base + K,
    st_set_next(Next, St, St1).

numbered([], _, []).
numbered([V|Vs], I, [V-I|Ps]) :-
    I1 is I + 1,
    numbered(Vs, I1, Ps).

rename_by(var(I, N), Table, var(J, N)) :-
    map_find(Table, I, I, J).
rename_by(atom(A), _, atom(A)).
rename_by(int(I), _, int(I)).
rename_by(flt(F), _, flt(F)).
rename_by(comp(F, As), Table, comp(F, Rs)) :-
    rename_by_list(As, Table, Rs).

rename_by_list([], _, []).
rename_by_list([A|As], T, [R|Rs]) :-
    rename_by(A, T, R),
    rename_by_list(As, T, Rs).

%  copy_all(+State, +Terms, -Copies, -State)
copy_all(St, [], [], St).
copy_all(St0, [T|Ts], [C|Cs], St) :-
    copy_term_st(St0, T, C, St1),
    copy_all(St1, Ts, Cs, St).

% ---------------------------------------------------------------------------
% Kinds of terms

is_var_t(var(_, _), true).
is_var_t(atom(_), false).
is_var_t(int(_), false).
is_var_t(flt(_), false).
is_var_t(comp(_, _), false).

is_callable_t(var(_, _), false).
is_callable_t(atom(_), true).
is_callable_t(int(_), false).
is_callable_t(flt(_), false).
is_callable_t(comp(_, _), true).

%  goal_key(+Term, -MaybeKey): just(Name/Arity) for a callable term.
goal_key(var(_, _), nothing).
goal_key(atom(A), just(A/0)).
goal_key(int(_), nothing).
goal_key(flt(_), nothing).
goal_key(comp(F, As), just(F/N)) :-
    length(As, N).

goal_args(var(_, _), []).
goal_args(atom(_), []).
goal_args(int(_), []).
goal_args(flt(_), []).
goal_args(comp(_, As), As).

%  add_args(+Goal, +Extra, -MaybeGoal)
add_args(G, Extra, M) :-
    add_args_(Extra, G, M).

add_args_([], G, just(G)).
add_args_([X|Xs], G, M) :-
    add_args_ne(G, [X|Xs], M).

add_args_ne(var(_, _), _, nothing).
add_args_ne(atom(A), Xs, just(comp(A, Xs))).
add_args_ne(int(_), _, nothing).
add_args_ne(flt(_), _, nothing).
add_args_ne(comp(F, As), Xs, just(comp(F, Bs))) :-
    conc(As, Xs, Bs).

%  conj_list(+Goal, -Goals): flatten ','/2, dropping true.
conj_list(T, Gs) :-
    conj_kind(T, K),
    conj_list_(K, T, Gs).

conj_kind(T, K) :-
    if_commit(T = comp(',', [_, _]),
              K = conj,
              if_commit(T = atom(true), K = true, K = goal)).

conj_list_(conj, comp(',', [A, B]), Gs) :-
    conj_list(A, GA),
    conj_list(B, GB),
    conc(GA, GB, Gs).
conj_list_(true, _, []).
conj_list_(goal, T, [T]).

mk_conj([], atom(true)).
mk_conj([G|Gs], C) :-
    mk_conj_(Gs, G, C).

mk_conj_([], G, G).
mk_conj_([H|Hs], G, comp(',', [G, C])) :-
    mk_conj_(Hs, H, C).

% ---------------------------------------------------------------------------
% Term identity, variants and the standard order

%  same_term(+A, +B, -Bool): structural equality (Haskell's Eq on terms;
%  variables are equal when their ids are).
same_term(A, B, Bo) :-
    strip_names(A, A1),
    strip_names(B, B1),
    test(A1 == B1, Bo).

strip_names(var(I, _), v(I)).
strip_names(atom(A), atom(A)).
strip_names(int(I), int(I)).
strip_names(flt(F), flt(F)).
strip_names(comp(F, As), comp(F, Bs)) :-
    maplist(strip_names, As, Bs).

%  variant_t(+State, +A, +B, -Bool): equal up to a consistent renaming.
variant_t(St, A, B, Bo) :-
    resolve(A, St, RA),
    resolve(B, St, RB),
    map_empty(E),
    variant_go(RA, RB, E, E, M),
    is_just(M, Bo).

variant_go(var(I, _), Y, M1, M2, R) :-
    variant_var(Y, I, M1, M2, R).
variant_go(atom(A), Y, M1, M2, R) :-
    variant_const(Y, atom(A), M1, M2, R).
variant_go(int(A), Y, M1, M2, R) :-
    variant_const(Y, int(A), M1, M2, R).
variant_go(flt(A), Y, M1, M2, R) :-
    variant_const(Y, flt(A), M1, M2, R).
variant_go(comp(F, As), Y, M1, M2, R) :-
    variant_comp(Y, F, As, M1, M2, R).

variant_var(var(J, _), I, M1, M2, R) :-
    map_get(M1, I, LI),
    map_get(M2, J, LJ),
    variant_vv(LI, LJ, I, J, M1, M2, R).
variant_var(atom(_), _, _, _, nothing).
variant_var(int(_), _, _, _, nothing).
variant_var(flt(_), _, _, _, nothing).
variant_var(comp(_, _), _, _, _, nothing).

variant_vv(nothing, LJ, I, J, M1, M2, R) :-
    variant_new(LJ, I, J, M1, M2, R).
variant_vv(just(J1), LJ, I, J, M1, M2, R) :-
    variant_old(LJ, J1, I, J, M1, M2, R).

variant_new(nothing, I, J, M1, M2, just(N1-N2)) :-
    map_put(I, J, M1, N1),
    map_put(J, I, M2, N2).
variant_new(just(_), _, _, _, _, nothing).

variant_old(nothing, _, _, _, _, _, nothing).
variant_old(just(I1), J1, I, J, M1, M2, R) :-
    test(( J1 =:= J, I1 =:= I ), B),
    variant_ok(B, M1, M2, R).

variant_ok(true, M1, M2, just(M1-M2)).
variant_ok(false, _, _, nothing).

variant_const(Y, X, M1, M2, R) :-
    is_var_t(Y, V),
    variant_const_(V, Y, X, M1, M2, R).

variant_const_(true, _, _, _, _, nothing).
variant_const_(false, Y, X, M1, M2, R) :-
    same_term(X, Y, B),
    variant_ok(B, M1, M2, R).

variant_comp(var(_, _), _, _, _, _, nothing).
variant_comp(atom(_), _, _, _, _, nothing).
variant_comp(int(_), _, _, _, _, nothing).
variant_comp(flt(_), _, _, _, _, nothing).
variant_comp(comp(G, Bs), F, As, M1, M2, R) :-
    same_functor(F, As, G, Bs, B),
    variant_args(B, As, Bs, M1, M2, R).

variant_args(false, _, _, _, _, nothing).
variant_args(true, As, Bs, M1, M2, R) :-
    variant_list(As, Bs, M1, M2, R).

variant_list([], [], M1, M2, just(M1-M2)).
variant_list([A|As], [B|Bs], M1, M2, R) :-
    variant_go(A, B, M1, M2, R1),
    variant_list_more(R1, As, Bs, R).

variant_list_more(nothing, _, _, nothing).
variant_list_more(just(M1-M2), As, Bs, R) :-
    variant_list(As, Bs, M1, M2, R).

%  compare_std(+State, +A, +B, -Order): Var < Number < Atom < Compound.
compare_std(St, A, B, O) :-
    walk(A, St, WA),
    walk(B, St, WB),
    rank(WA, RA),
    rank(WB, RB),
    compare(OR, RA, RB),
    compare_ranked(OR, RA, WA, WB, St, O).

rank(var(_, _), 0).
rank(flt(_), 1).
rank(int(_), 1).
rank(atom(_), 3).
rank(comp(_, _), 4).

compare_ranked(<, _, _, _, _, <).
compare_ranked(>, _, _, _, _, >).
compare_ranked(=, R, A, B, St, O) :-
    compare_same(R, A, B, St, O).

compare_same(0, var(I, _), var(J, _), _, O) :-
    compare(O, I, J).
compare_same(1, A, B, _, O) :-
    compare_num(A, B, O).
compare_same(3, atom(X), atom(Y), _, O) :-
    compare(O, X, Y).
compare_same(4, comp(F, As), comp(G, Bs), St, O) :-
    length(As, N),
    length(Bs, K),
    compare(O1, N, K),
    compare(O2, F, G),
    compare_args_std(As, Bs, St, O3),
    then_order(O1, O2, O12),
    then_order(O12, O3, O).

compare_num(int(X), Y, O) :-
    compare_int_num(Y, X, O).
compare_num(flt(X), Y, O) :-
    compare_flt_num(Y, X, O).

compare_int_num(int(Y), X, O) :-
    compare(O, X, Y).
compare_int_num(flt(Y), X, O) :-
    XF is float(X),
    float_order(XF, Y, O0),
    eq_then(O0, >, O).

compare_flt_num(int(Y), X, O) :-
    YF is float(Y),
    float_order(X, YF, O0),
    eq_then(O0, <, O).
compare_flt_num(flt(Y), X, O) :-
    float_order(X, Y, O).

float_order(X, Y, O) :-
    if_commit(X < Y, O = (<), if_commit(X > Y, O = (>), O = (=))).

eq_then(=, O, O).
eq_then(<, _, <).
eq_then(>, _, >).

then_order(=, O, O).
then_order(<, _, <).
then_order(>, _, >).

compare_args_std([], _, _, =).
compare_args_std([A|As], Bs, St, O) :-
    compare_args_std_(Bs, A, As, St, O).

compare_args_std_([], _, _, _, =).
compare_args_std_([B|Bs], A, As, St, O) :-
    compare_std(St, A, B, O1),
    compare_args_more(O1, As, Bs, St, O).

compare_args_more(<, _, _, _, <).
compare_args_more(>, _, _, _, >).
compare_args_more(=, As, Bs, St, O) :-
    compare_args_std(As, Bs, St, O).
