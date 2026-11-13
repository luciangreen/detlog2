# Input Prolog and output Detlog

These are complete input → output pairs, with no ellipses. Each output program:

- gives the same answers as its input, in the same order, with the same output;
- uses no cut, `;`, `->` or `\+`;
- leaves no choicepoint.

The Detlog forms below are in [`docs/examples/`](examples/). [`tests/native_tests.pl`](../tests/native_tests.pl) runs 20 queries against them on plain SWI-Prolog, with only [`src/detlog_runtime.pl`](../src/detlog_runtime.pl) loaded. It compares each with the original program, cuts included, running on SWI-Prolog itself. Every query gives the same answers.

They are written compactly. `detlog2 convert` writes the same constructions in a longer, regular form, where:

- every clause becomes its own `p__cp_cK` predicate;
- every conjunction is spliced row by row;
- every step is justified in a proof.

CI checks that output against the originals too.

A predicate `p/n` becomes `p__cp(A1, ..., An, Rows)`. It succeeds exactly once. `Rows` is the answer packet: one row `[A1, ..., An]` per answer, with `out(Text)` items where output is written.

---

### 1. Independent generators (`examples/splice.pl`)

**Input Prolog**
```prolog
c(A, B) :- a(A), b(B).
a(A) :- member(A, [1, 2]).
b(B) :- member(B, [3, 4]).
```

**Output Detlog**
```prolog
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
```

`c(A, B)` gives `A = 1, B = 3`; `A = 1, B = 4`; `A = 2, B = 3`; `A = 2, B = 4`.

The generators share no variable, so each packet is computed once and spliced. `c__cp_seq/3` is the sequential form, used when `splice_safe/1` fails.

---

### 2. Cut elimination: a simple cut (`examples/cuts.pl`)

**Input Prolog**
```prolog
a(X) :- b(X), !, c(X).
a(X) :- d(X).
b(1).
b(2).
c(1).
d(3).
```

**Output Detlog**
```prolog
a(X) :-
    if_commit(b(X), c(X), d(X)).

a__cp(X, Rows) :-
    b__cp(X, PB),
    packet_first(PB, _, First),
    a__cp_commit(First, X, Rows).

a__cp_commit(none, X, Rows) :-
    d__cp(X, Rows).
a__cp_commit(first([X1]), _, Rows) :-
    c__cp(X1, Rows).

b__cp(X, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [X], Rows).

c__cp(X, Rows) :-
    member_cp(P, [[1]]),
    cp_filter(P, [X], Rows).

d__cp(X, Rows) :-
    member_cp(P, [[3]]),
    cp_filter(P, [X], Rows).

% the facts, used by the cut-free form a/1 above
b(1).
b(2).
c(1).
d(3).
```

The cut commits to the first answer of `b(X)`, so the clauses are not joined with `rows_concat/2`.

- `a(X)` gives only `X = 1`.
- `a(2)` fails, because `b(2)` succeeds and then `c(2)` fails.
- `a(3)` gives `a(3)`, because `b(3)` fails and `d(3)` succeeds.

---

### 3. `max/3` (a red cut)

**Input Prolog**
```prolog
max(X, Y, X) :- X >= Y, !.
max(_, Y, Y).
```

**Output Detlog**
```prolog
max(X, Y, Z) :-
    if_commit(( Z = X, X >= Y ), true, Z = Y).

max__cp(X, Y, Z, Rows) :-
    copy_term([X, Y, Z], [X1, Y1, Z1]),
    if_commit(max(X1, Y1, Z1), Rows = [[X1, Y1, Z1]], Rows = []).
```

The head unification `Z = X` is part of the condition.

- `max(7, 3, Z)` gives only `Z = 7`.
- `max(7, 3, 3)` succeeds, as in Prolog: the first clause's head does not match, so the second clause is used.

---

### 4. `classify/2`

**Input Prolog**
```prolog
classify(N, neg) :- N < 0, !.
classify(0, zero) :- !.
classify(_, pos).
```

**Output Detlog**
```prolog
classify(N, C) :-
    if_commit(( C = neg, N < 0 ),
              true,
              if_commit(( N = 0, C = zero ), true, C = pos)).

classify__cp(N, C, Rows) :-
    copy_term([N, C], [N1, C1]),
    if_commit(classify(N1, C1), Rows = [[N1, C1]], Rows = []).
```

Each query gets exactly one answer: `classify(-1, C)` gives `C = neg`, `classify(0, C)` gives `C = zero`, and `classify(5, C)` gives `C = pos`.

---

### 5. Multi-clause facts (`examples/sample_program.pl`)

**Input Prolog**
```prolog
multi_fact(a).
multi_fact(b).
multi_fact(b).
```

**Output Detlog**
```prolog
multi_fact__cp(A, Rows) :-
    member_cp(P, [[a], [b], [b]]),
    cp_filter(P, [A], Rows).
```

---

### 6. Deterministic recursion (`det_sum`)

**Input Prolog**
```prolog
det_sum([], 0).
det_sum([H|T], S) :-
    det_sum(T, Rest),
    S is H + Rest.
```

**Output Detlog**
```prolog
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
```

`det_sum([1, 2, 3], S)` gives `S = 6`. `det_sum([1, 2], 3)` succeeds and `det_sum([1, 2], 4)` fails. The sum is computed once for each row of the recursive call's packet.

---

### 7. Dependent conjunction

**Input Prolog**
```prolog
p(1).
p(2).
p(3).
q(X, Y) :- p(X), Y is X * 10, Y > 10.
```

**Output Detlog**
```prolog
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
```

`q(X, Y)` gives `X = 2, Y = 20` and `X = 3, Y = 30`. `Y` depends on `X`, so the test runs once for each row of `p/1`'s packet.

---

### 8. Side effects as data (`examples/output.pl`)

**Input Prolog**
```prolog
gen(X) :- member(X, [1, 2]), write(g(X)).
```

**Output Detlog**
```prolog
gen__cp(X, Rows) :-
    member_cp(P, [[1], [2]]),
    cp_filter(P, [X], Env),
    gen__cp_write(Env, Rows).

gen__cp_write([], []).
gen__cp_write([[X]|Env], [out(T), [X]|Rows]) :-
    effect_text(write(g(X)), T),
    gen__cp_write(Env, Rows).
```

The packet is `[out('g(1)'), [1], out('g(2)'), [2]]`. Each text comes just before its answer, in the order Prolog writes it.

---

### 9. Memoisation of an unsupported cut (`examples/memo.pl`)

**Input Prolog**
```prolog
pick(N, X) :- (N > 3 -> member(X, [big, huge]), ! ; X = small).
pick(_, other).
```

**Output after `detlog2 memoise examples/memo.pl --goal 'pick(2, X)' --goal 'pick(5, X)' --complete`**
```prolog
pick__cp(A1, A2, Rows) :-
    if_commit(memo_lookup([A1, A2],
                          [ [[2, _], [[2, small], [2, other]]],
                            [[5, _], [[5, big]]]
                          ],
                          Rows),
              true,
              memo_miss(pick / 2, [A1, A2])).
```

`pick(5, X)` gives only `X = big`: the cut after `member/2` commits the whole predicate. `pick(2, X)` gives `small`, then `other`.

---

### Mapping

| Prolog | Detlog |
| --- | --- |
| facts | `member_cp/2` and `cp_filter/3` |
| `member/2`, `between/3` | `member_cp/2`, `between_cp/3` (with `cp_rows/2`) |
| independent generators | each packet once, then `splice/2`, guarded by `splice_safe/1`, with a sequential fallback |
| dependent conjunction | `splice_extend/4`, then one step per row, joined with `rows_concat/2` |
| several clauses, `(A ; B)` | `rows_concat/2` |
| cut, `->`, `once/1`, `\+/1` | `if_commit/3`; a clause's head unification is part of its condition |
| commitment to a packet's first answer | `packet_first/3` |
| `findall/3`, `aggregate_all/3` | the packet itself (`packet_split/3`, `length_det/2`) |
| `write/1` and other output | `effect_text/2` and `out(Text)` items in the packet |
| cuts the converter does not support | a memo table (`memo_lookup/3`, `memo_miss/2`) |

### Corrections to the earlier text

The earlier version of this text had programs that gave different answers from the originals:

- **`a/1`, `max/3`, `classify/2`.** It joined every clause with `rows_concat/2`, so a cut no longer removed the later clauses.
  - `a(X)` gave `X = 1` and also `X = 3`.
  - `max(7, 3, Z)` gave `Z = 7` and also `Z = 3`.
  - `classify(-1, C)` gave `neg` and also `pos`.
- **The cut-free `max/3`.** `max(X, Y, Z) :- if_commit(X >= Y, Z = X, Z = Y)` fails for `max(7, 3, 3)`, which Prolog accepts.
- **`pick(5, X)`.** The memo table listed `big`, `huge` and `other`. Prolog gives only `big`.
- **`c/2`.** `splice/2` alone gave rows `[[1], [3]]`, not `[1, 3]`; `splice_extend/4` now forms the rows.
- **`det_sum/2`, `q/2`.** They tested `S is H + Rest` and `Y is X * 10` once, outside the rows. The test is now run on every row.
- **`gen/1`.** It wrote `g(_)` once, before all the rows. Now each `g(X)` is written before its own row.
