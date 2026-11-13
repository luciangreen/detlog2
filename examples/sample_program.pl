% The sample program of the original Detlog (github.com/luciangreen/detlog,
% test/fixtures/sample_program.pl).  The regression requirement is that
% det_sum/2, if_then_else/2 and safe_cut/1 are converted, not fallen back.

det_sum([], 0).
det_sum([H|T], S) :-
    det_sum(T, Rest),
    S is H + Rest.

nondet_member(X, List) :-
    member(X, List).

multi_fact(a).
multi_fact(b).
multi_fact(b).

if_then_else(X, Y) :-
    (X > 0 -> Y = pos ; Y = nonpos).

safe_cut(X) :-
    X > 0, !.
safe_cut(_).

side_effect(X) :-
    writeln(X).
