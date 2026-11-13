% Cuts of several kinds.  detlog2 turns each into an explicit decision.

% a :- b, !, c.  a :- d.   becomes   a :- if_commit(b, c, d).
a(X) :- b(X), !, c(X).
a(X) :- d(X).
b(1). b(2).
c(1).
d(3).

% A red cut (meaning-changing) and a green one.
max(X, Y, X) :- X >= Y, !.
max(_, Y, Y).

classify(N, neg) :- N < 0, !.
classify(0, zero) :- !.
classify(_, pos).

% First solution only, with a cut local to findall's goal.
firsts(L, F) :- findall(X, (member(X, L), X > 1, !), F).

% Two cuts in one clause.
two(X, Y) :- member(X, [1, 2, 3]), X > 1, !, member(Y, [a, b]), !.
two(none, none).

% A cut inside \+ is local to it.
no_big(L) :- \+ (member(X, L), X > 5, !).
