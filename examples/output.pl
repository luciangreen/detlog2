% Output written from inside generators.  In converted code output is data
% (out(Text) items of the answer packets), so it comes out in exactly the
% order Prolog writes it.

gen(X) :- member(X, [1, 2]), write(g(X)).

% g(1)s(1)  then  g(2)s(2): the generator's output interleaves with the caller's
show :- gen(X), write(s(X)), nl, fail.
show.

% two writing generators in one conjunction
pairs :- gen(X), gen(Y), write(X-Y), nl, fail.
pairs.

% commitment stops output at the first answer
first_big(X) :- once((member(X, [1, 5, 9]), write(try(X)), X > 3)).

% output inside findall/3 and aggregate_all/3
count_out(N) :- aggregate_all(count, gen(_), N).
logged(L) :- findall(X, (gen(X), write(','), X > 0), L), nl.
