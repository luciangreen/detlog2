% 2. a(X) :- b(X), !, c(X).   a(X) :- d(X).
a(X) :-
    if_commit(b(X), c(X), d(X)).

a__cp(X, Rows) :-
    b__cp(X, PB),
    packet_first(PB, _, First),
    a__cp_commit(First, X, Rows).

a__cp_commit(none, X, Rows) :-
    d__cp(X, Rows).
a__cp_commit(first([X1]), _, Rows) :-
    c__cp(X1, Rows).

b__cp(X, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [X], Rows).

c__cp(X, Rows) :-
    member_cp(P, [[1]]),
    cp_filter(P, [X], Rows).

d__cp(X, Rows) :-
    member_cp(P, [[3]]),
    cp_filter(P, [X], Rows).

% the facts, used by the cut-free form a/1 above
b(1).
b(2).
c(1).
d(3).

% 3. max(X, Y, X) :- X >= Y, !.   max(_, Y, Y).
max(X, Y, Z) :-
    if_commit(( Z = X, X >= Y ), true, Z = Y).

max__cp(X, Y, Z, Rows) :-
    copy_term([X, Y, Z], [X1, Y1, Z1]),
    if_commit(max(X1, Y1, Z1), Rows = [[X1, Y1, Z1]], Rows = []).

% 4. classify(N, neg) :- N < 0, !.   classify(0, zero) :- !.   classify(_, pos).
classify(N, C) :-
    if_commit(( C = neg, N < 0 ),
              true,
              if_commit(( N = 0, C = zero ), true, C = pos)).

classify__cp(N, C, Rows) :-
    copy_term([N, C], [N1, C1]),
    if_commit(classify(N1, C1), Rows = [[N1, C1]], Rows = []).
