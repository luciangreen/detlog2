% The splice example from the Detlog notes: two generators whose answers
% are combined.  detlog2 computes each packet once and splices them:
%   ?- c(A, B).   A = 1, B = 3 ; A = 1, B = 4 ; A = 2, B = 3 ; A = 2, B = 4.

c(A, B) :- a(A), b(B).
a(A) :- member(A, [1, 2]).
b(B) :- member(B, [3, 4]).

% Three positions, one of them fixed: splice([fixed, cp([1,2]), x], Rows).
triple(X, Y, Z) :- X = fixed, member(Y, [1, 2]), Z = x.

% A dependent conjunction: q/2 needs the answer of p/1.
p(1). p(2). p(3).
q(X, Y) :- p(X), Y is X * 10, Y > 10.
