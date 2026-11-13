/*  unfold.pl - data and the rules over it, for detlog2 unfold.

    detlog2 unfold examples/unfold.pl -o out.pl --check 'step(X, 13)'

    Every pure predicate is unfolded into its answer table, and each table
    becomes an S2A loop.  first_colour/1 has a cut and evens/1 has infinitely
    many answers, so they are converted as usual instead.
*/

% facts with a pattern: V = 3 + 5*I
step(0, 3).
step(1, 8).
step(2, 13).
step(3, 18).
step(4, 23).

% data computed by rules
square(N, S) :- between(0, 6, N), S is N * N.
triangle(N, T) :- between(0, 9, N), T is N * (N + 1) // 2.
cube(N, C) :- between(0, 5, N), C is N * N * N - 2.

% facts with no formula: the values are listed
colour(0, red).
colour(1, green).
colour(2, blue).

% rules over the data, recursion included
pair(N, S, C) :- square(N, S), N < 3, colour(N, C).
two_steps(X, Z) :- step(X, Y), step(Y, Z).
parent(ann, bob).
parent(bob, cy).
parent(cy, dee).
anc(X, Y) :- parent(X, Y).
anc(X, Y) :- parent(X, Z), anc(Z, Y).
either(X) :- ( X = 1 ; X = 2 ; X = 1 ).

% not pure: converted, not unfolded (it calls colour/2's loop)
first_colour(C) :- colour(_, C), !.

% infinitely many answers: converted, not unfolded
evens(X) :- between(0, inf, Y), X is 2 * Y.
