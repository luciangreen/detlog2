% A cut inside an if-then-else branch cuts the clause; detlog2 does not
% guess its conversion.  Memoise the calls you need instead:
%   detlog2 memoise examples/memo.pl --goal 'pick(2, X)' --goal 'pick(5, X)' --complete
pick(N, X) :- ( N > 3 -> member(X, [big, huge]), ! ; X = small ).
pick(_, other).

fib(0, 0).
fib(1, 1).
fib(N, F) :- N > 1, N1 is N - 1, N2 is N - 2, fib(N1, F1), fib(N2, F2), F is F1 + F2.
