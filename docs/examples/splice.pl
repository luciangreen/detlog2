% 1. Independent generators: c(A, B) :- a(A), b(B).
c__cp(A, B, Rows) :-
    if_commit(splice_safe([[A], [B]]),
              ( a__cp(A, PA),
                b__cp(B, PB),
                splice([cp(PA), cp(PB)], Combos),
                splice_extend(Combos, [A, B], [[A], [B]], Rows) ),
              c__cp_seq(A, B, Rows)).

c__cp_seq(A, B, Rows) :-
    a__cp(A, PA),
    splice_extend(PA, [A, B], [A], Env),
    c__cp_seq_rows(Env, Rows).

c__cp_seq_rows([], []).
c__cp_seq_rows([[A, B]|Env], Rows) :-
    b__cp(B, PB),
    splice_extend(PB, [A, B], [B], R1),
    c__cp_seq_rows(Env, R2),
    rows_concat([R1, R2], Rows).

a__cp(A, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [A], Rows).

b__cp(B, Rows) :-
    member_cp(P, [[3], [4]]),
    cp_filter(P, [B], Rows).

% 7. Dependent conjunction: q(X, Y) :- p(X), Y is X * 10, Y > 10.
p__cp(X, Rows) :-
    member_cp(P, [[1], [2], [3]]),
    cp_filter(P, [X], Rows).

q__cp(X, Y, Rows) :-
    copy_term([X, Y], [X1, Y1]),
    p__cp(X1, PX),
    splice_extend(PX, [X1, Y1], [X1], Env),
    q__cp_test(Env, Rows).

q__cp_test([], []).
q__cp_test([[X, Y]|Env], Rows) :-
    if_commit(( Y is X * 10, Y > 10 ), R1 = [[X, Y]], R1 = []),
    q__cp_test(Env, R2),
    rows_concat([R1, R2], Rows).
