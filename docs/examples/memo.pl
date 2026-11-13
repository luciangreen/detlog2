% 9. pick(N, X) :- ( N > 3 -> member(X, [big, huge]), ! ; X = small ).   pick(_, other).
pick__cp(A1, A2, Rows) :-
    if_commit(memo_lookup([A1, A2],
                          [ [[2, _], [[2, small], [2, other]]],
                            [[5, _], [[5, big]]]
                          ],
                          Rows),
              true,
              memo_miss(pick / 2, [A1, A2])).
