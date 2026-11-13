% 5. Multi-clause facts
multi_fact__cp(A, Rows) :-
    member_cp(P, [[a], [b], [b]]),
    cp_filter(P, [A], Rows).

% 6. det_sum([], 0).   det_sum([H|T], S) :- det_sum(T, Rest), S is H + Rest.
det_sum__cp(L, S, Rows) :-
    det_sum__cp_c1([L, S], R1),
    det_sum__cp_c2([L, S], R2),
    rows_concat([R1, R2], Rows).

det_sum__cp_c1(Args, Rows) :-
    if_commit(copy_term(Args, [[], 0]), Rows = [[[], 0]], Rows = []).

det_sum__cp_c2(Args, Rows) :-
    if_commit(copy_term(Args, [[H|T], S]),
              ( det_sum__cp(T, Rest, R1),
                splice_extend(R1, [H, T, S, Rest], [T, Rest], Env),
                det_sum__cp_add(Env, Rows) ),
              Rows = []).

det_sum__cp_add([], []).
det_sum__cp_add([[H, T, S, Rest]|Env], Rows) :-
    if_commit(S is H + Rest, R1 = [[[H|T], S]], R1 = []),
    det_sum__cp_add(Env, R2),
    rows_concat([R1, R2], Rows).
