/*  prelude.pl - library predicates for interpreted programs.

    These are object-level Prolog clauses, run by detlog2's own engines
    (interp.pl, reference.pl), not by SWI-Prolog.  A program's own
    definition of a predicate always replaces the library one.
*/

prelude_source(S) :-
    prelude_lines(Ls),
    atomic_list_concat(Ls, '\n', A),
    atom_string(A, S).

prelude_lines([
    "append([], L, L).",
    "append([H|T], L, [H|R]) :- append(T, L, R).",
    "member(X, [X|_]).",
    "member(X, [_|T]) :- member(X, T).",
    "memberchk(X, L) :- once(member(X, L)).",
    "reverse(L, R) :- reverse_(L, [], R).",
    "reverse_([], A, A).",
    "reverse_([H|T], A, R) :- reverse_(T, [H|A], R).",
    "nth0(I, L, E) :- nth_(L, 0, I, E).",
    "nth1(I, L, E) :- nth_(L, 1, I, E).",
    "nth_([H|_], B, B, H).",
    "nth_([_|T], B, I, E) :- B1 is B + 1, nth_(T, B1, I, E).",
    "last([X], X).",
    "last([_|T], X) :- last(T, X).",
    "select(X, [X|T], T).",
    "select(X, [H|T], [H|R]) :- select(X, T, R).",
    "selectchk(X, L, R) :- once(select(X, L, R)).",
    "delete([], _, []).",
    "delete([H|T], X, R) :- ( H \\= X -> R = [H|R1] ; R = R1 ), delete(T, X, R1).",
    "subtract([], _, []).",
    "subtract([H|T], L, R) :- ( memberchk(H, L) -> R = R1 ; R = [H|R1] ), subtract(T, L, R1).",
    "permutation([], []).",
    "permutation(L, [H|T]) :- select(H, L, R), permutation(R, T).",
    "sum_list(L, S) :- sum_list_(L, 0, S).",
    "sum_list_([], S, S).",
    "sum_list_([H|T], A, S) :- A1 is A + H, sum_list_(T, A1, S).",
    "sumlist(L, S) :- sum_list(L, S).",
    "max_list([H|T], M) :- max_list_(T, H, M).",
    "max_list_([], M, M).",
    "max_list_([H|T], A, M) :- A1 is max(A, H), max_list_(T, A1, M).",
    "min_list([H|T], M) :- min_list_(T, H, M).",
    "min_list_([], M, M).",
    "min_list_([H|T], A, M) :- A1 is min(A, H), min_list_(T, A1, M).",
    "numlist(L, H, R) :- L =< H, numlist_(L, H, R).",
    "numlist_(L, H, R) :- ( L =:= H -> R = [L] ; R = [L|T], L1 is L + 1, numlist_(L1, H, T) ).",
    "list_to_set(L, S) :- lts_(L, [], S).",
    "lts_([], _, []).",
    "lts_([H|T], Seen, R) :- ( memberchk(H, Seen) -> R = R1 ; R = [H|R1] ), lts_(T, [H|Seen], R1).",
    "exclude(G, L, R) :- exclude_(L, G, R).",
    "exclude_([], _, []).",
    "exclude_([X|Xs], G, R) :- ( call(G, X) -> R = R1 ; R = [X|R1] ), exclude_(Xs, G, R1).",
    "include(G, L, R) :- include_(L, G, R).",
    "include_([], _, []).",
    "include_([X|Xs], G, R) :- ( call(G, X) -> R = [X|R1] ; R = R1 ), include_(Xs, G, R1).",
    "maplist(G, L) :- maplist_(L, G).",
    "maplist_([], _).",
    "maplist_([X|Xs], G) :- call(G, X), maplist_(Xs, G).",
    "maplist(G, L1, L2) :- maplist_(L1, L2, G).",
    "maplist_([], [], _).",
    "maplist_([X|Xs], [Y|Ys], G) :- call(G, X, Y), maplist_(Xs, Ys, G).",
    "maplist(G, L1, L2, L3) :- maplist_(L1, L2, L3, G).",
    "maplist_([], [], [], _).",
    "maplist_([X|Xs], [Y|Ys], [Z|Zs], G) :- call(G, X, Y, Z), maplist_(Xs, Ys, Zs, G).",
    "foldl(G, L, A0, A) :- foldl_(L, G, A0, A).",
    "foldl_([], _, A, A).",
    "foldl_([X|Xs], G, A0, A) :- call(G, X, A0, A1), foldl_(Xs, G, A1, A).",
    "foldl(G, L1, L2, A0, A) :- foldl_(L1, L2, G, A0, A).",
    "foldl_([], [], _, A, A).",
    "foldl_([X|Xs], [Y|Ys], G, A0, A) :- call(G, X, Y, A0, A1), foldl_(Xs, Ys, G, A1, A).",
    "concat_atom(L, A) :- atomic_list_concat(L, A).",
    "pairs_keys_values([], [], []).",
    "pairs_keys_values([K-V|T], [K|Ks], [V|Vs]) :- pairs_keys_values(T, Ks, Vs)."
]).

prelude_program(P) :-
    prelude_source(S),
    parse_program(S, E),
    prelude_ok(E, P).

prelude_ok(right(P), P).
prelude_ok(left(M), _) :-
    format(string(Msg), "detlog2 prelude does not parse: ~s", [M]),
    throw(detlog2_bug(Msg)).

%  with_prelude(+Program, -Program): add the library predicates the program
%  does not define itself.
with_prelude(prog(Preds, Order, Ds), prog(Preds1, Order1, Ds)) :-
    prelude_program(prog(LP, LO, _)),
    extra_keys(LO, Preds, Extra),
    foldl(add_prelude_pred(LP), Extra, Preds, Preds1),
    conc(Order, Extra, Order1).

extra_keys([], _, []).
extra_keys([K|Ks], Preds, Out) :-
    map_member(Preds, K, B),
    extra_keys(Ks, Preds, Rest),
    extra_key(B, K, Rest, Out).

extra_key(true, _, Rest, Rest).
extra_key(false, K, Rest, [K|Rest]).

add_prelude_pred(LP, K, P0, P) :-
    map_get(LP, K, just(Cs)),
    map_put(K, Cs, P0, P).
