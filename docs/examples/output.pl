% 8. gen(X) :- member(X, [1, 2]), write(g(X)).
gen__cp(X, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [X], Env),
    gen__cp_write(Env, Rows).

gen__cp_write([], []).
gen__cp_write([[X]|Env], [out(T), [X]|Rows]) :-
    effect_text(write(g(X)), T),
    gen__cp_write(Env, Rows).
