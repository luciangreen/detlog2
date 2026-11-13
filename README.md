# detlog2

detlog2 is Detlog redone in Haskell. It has four parts:

1. **A choicepointless, cutless Prolog interpreter.**
2. **A converter** that rewrites Prolog with choicepoints and cuts into
   deterministic Detlog code. The code combines alternatives with splices
   (`member_cp/2`, `splice/2`) and expresses commitment with `if_commit/3`.
3. **A memoiser** that expands calls into answer tables, so that they need
   neither choicepoints nor cuts.
4. **A bridge to [mnns](https://github.com/luciangreen/mnns)** that runs mnns's
   proof-checked rewrites (`optimise.pl`) first and then converts what they
   produce.

The original, SWI-Prolog Detlog is at
[luciangreen/detlog](https://github.com/luciangreen/detlog).

## Build

detlog2 uses only GHC's own libraries (base, containers, process, directory).

```sh
./scripts/ci.sh                  # builds build/detlog2 and runs the tests
# or
ghc -O1 -isrc -outputdir build -o build/detlog2 app/Main.hs
# or
cabal build
```

The mnns tests also need SWI-Prolog and a clone of mnns: either next to this
repository (`../mnns`), in `MNNS_DIR`, or given with `--mnns DIR`.

## 1. The interpreter: no choicepoints, no cut

```sh
detlog2 run examples/sample_program.pl 'member(X, [1,2,3])'
X = 1.
X = 2.
X = 3.
```

Every goal denotes an **answer packet**: a lazy list of answers, together with
the output they write.

- A conjunction splices the second goal's packet into every answer of the
  first.
- A disjunction, or a predicate with several clauses, concatenates the
  packets of its alternatives.

Alternatives are therefore ordinary data, combined deterministically:

- **No choicepoint stack and no backtracking.** Failure is just the empty
  packet.
- **No trail.** Substitutions are immutable, so nothing ever has to be undone.
- **No cut.** `!` is rejected. Commitment is written `if_commit(C, T, E)` (or
  `(C -> T ; E)`), `once/1` or `\+/1`. Each of these takes the head of the
  condition's packet and never demands the rest.

Because packets are lazy, only answers that are actually needed are computed:
`once(between(1, inf, X))` gives `X = 1`.

`detlog2 run --det` additionally checks that every predicate call gives at
most one answer. This is the run-time version of "this code needs no
choicepoints".

`detlog2 ref FILE QUERY` runs the same query with ordinary cut semantics. It is
the reference that conversions are checked against.

## 2. The converter: cuts → decisions, choicepoints → splices

```sh
detlog2 convert examples/sample_program.pl -o out.pl
detlog2 check examples/cuts.pl 'max(5, 3, Z)' 'classify(0, C)' 'a(X)'
detlog2 packets examples/splice.pl 'c(A, B)'
packet: cp([[1, 3], [1, 4], [2, 3], [2, 4]])
A = 1, B = 3.
A = 1, B = 4.
A = 2, B = 3.
A = 2, B = 4.
```

**Cuts.** Every cut becomes an explicit decision.

- A clause `H :- G, !, B` followed by clauses `Rest` becomes
  `if_commit((match H, G), B, Rest)`. For example, `a :- b, !, c.  a :- d.`
  becomes `a :- if_commit(b, c, d)`.
- A later cut in the same clause becomes `if_commit(G2, B2, fail)`.
- A cut local to `\+`, `findall/3`, `once/1`, `call/1` or an if-then-else
  condition is converted in place.
- A cut inside a disjunction or if-then-else branch would cut the whole
  clause. That placement is reported as unsupported rather than guessed;
  memoise such predicates instead (see 3).

**Choicepoints.** Every predicate `p/n` becomes `p__cp(A1, ..., An, Rows)`.
It succeeds exactly once, and `Rows` is its answer packet: one row per
answer of `p`, in Prolog order, duplicates included. Inside a clause, each
goal maps a list of environment rows to a new list of rows:

| source | Detlog code |
| --- | --- |
| facts `p(a). p(b). p(b).` | `member_cp(P, [[a],[b],[b]]), cp_filter(P, [A], Rows)` |
| `member(X, L)`, `between(L, H, X)` | `member_cp(P, L)` / `between_cp(L, H, P)` packets |
| call `q(X, Y)` | `q__cp(X, Y, Packet), splice_extend(Packet, Env, [X, Y], Out)` |
| independent generators `a(A), b(B)` | each packet computed once, then `splice([cp(PA), cp(PB)], Rows)` (splice early, enumerate late) |
| `(A ; B)` | `rows_concat([RowsA, RowsB], Out)` |
| `(C -> T ; E)`, `once/1`, `\+/1` | `if_commit/3` |
| `findall/3`, `aggregate_all(count, ...)` | the packet itself |
| `maplist(succ, L, R)` and other closures | a copy of `maplist/3` specialised to `succ`, so no `call/N` remains |

A splice of goals that may share variables at run time is guarded by
`splice_safe/1`, which falls back to sequential splicing.

**The output contains:**

- no cut, no `;`, no `->`, no `call/N`, and no nondeterministic built-in;
- predicates that each have either one clause, or two clauses whose first
  arguments are `[]` and `[_|_]` (iteration over a proper list of rows).

`Detlog2.Check` verifies this structure for every converted program, and
`check` and `packets` also run the result with `--det`.

**`detlog2 check FILE QUERY...` does three things:**

1. converts the program;
2. runs the choicepoint check;
3. compares the answer sequence of the source (ordinary cut semantics) with
   that of the converted code, including order and duplicates.

For the original Detlog sample this covers `det_sum/2`, `if_then_else/2` and
`safe_cut/1`, which are converted, not fallen back.

**Known differences:**

- **Output order.** Packets are computed before their continuation runs, so
  output written inside a generator can come in a different order. `check`
  reports this as a note.
- **Infinite generators.** A generator with infinitely many answers
  (`between(1, inf, X)`, `length(L, N)` with both unbound) cannot be turned
  into a finite packet and raises an error in converted code.
- **Collections.** `bagof/3` and `setof/3` do not group by free variables.

## 3. Memoisation: expanding choicepoints and cuts into data

```sh
detlog2 memoise examples/memo.pl --goal 'pick(2, X)' --goal 'pick(5, X)' --complete \
    -o pick.pl --check 'pick(5, X)'
detlog2 memoise examples/memo.pl --goal 'fib(20, F)' -o fib.pl --check 'fib(7, F)'
```

Each goal is run once with cut semantics, and its complete answer packet is
written into the converted program as a table:

```prolog
pick__cp(A1, A2, Rows) :-
    if_commit(memo_lookup([A1, A2], [[[2, _], [[2, small], [2, other]]], ...], Rows),
              true,
              memo_miss(pick / 2, [A1, A2])).
```

- Without `--complete`, a call that is not in the table runs the converted
  code (`p__cp__compute`).
- With `--complete`, the table is the whole predicate: its source clauses,
  even ones with cuts that cannot be converted, are not needed.

## 4. The mnns bridge

```sh
detlog2 mnns prog.pl --mnns ../mnns -o out.pl --check 'big(R)'
```

This runs `swipl ../mnns/optimise.pl -- prog.pl tmp.pl`. In that pass, mnns
applies only rewrites that its independent proof checker accepts:

- PLOp: `findall/3` over finite generators becomes deterministic loops;
- AIOC simplification;
- mnns's own Detlog stage: `once/1` and terminal-cut lowering.

detlog2 then converts the result and removes every remaining cut and
choicepoint. The mnns report line is kept in the output header. If SWI-Prolog
or mnns is missing, the pass is reported as not applied, and the conversion
still runs.

## Runtime constructs

| predicate | meaning |
| --- | --- |
| `member_cp(P, L)` | `P = cp(L)`: a choice packet |
| `between_cp(L, H, P)` | `P = cp([L, ..., H])` |
| `cp_rows(cp(L), Rows)` | `[[E1], [E2], ...]` |
| `splice(Positions, Rows)` | deterministic Cartesian product in Prolog order; fixed values and nested packets (`cp([1, cp([2,3])])`) are allowed |
| `splice_first(Positions, Row)` | the first row |
| `splice_extend(Rows, Env, Pattern, Out)` | splice an answer packet into an environment |
| `rows_concat(Lists, Rows)` | concatenate packets |
| `if_commit(C, T, E)`, `once_det(G)`, `decision(Cases, Default)` | commitment without cut |
| `memo_lookup/3`, `memo_miss/2` | memo tables |

## Layout

```
src/Detlog2/Term.hs       terms, immutable substitutions, unification
src/Detlog2/Parser.hs     standard Prolog reader (operators, strings as char lists)
src/Detlog2/Pretty.hs     re-readable printing
src/Detlog2/Builtins.hs   built-ins and the Detlog runtime
src/Detlog2/Prelude.hs    cut-free library (append, select, maplist, foldl, ...)
src/Detlog2/Interp.hs     the choicepointless, cutless interpreter
src/Detlog2/Reference.hs  ordinary cut semantics (oracle for checks and memo tables)
src/Detlog2/CutElim.hs    cuts -> if_commit/3
src/Detlog2/Convert.hs    choicepoints -> packets and splices
src/Detlog2/Check.hs      static choicepoint-freedom check
src/Detlog2/Memo.hs       answer tables
src/Detlog2/Mnns.hs       mnns optimise.pl bridge
src/Detlog2/Equiv.hs      answer-sequence comparison
app/Main.hs               command line
tests/cli.sh              end-to-end tests (run by scripts/ci.sh and GitHub Actions)
```

Related: [plop2](https://github.com/luciangreen/plop2) builds one separate
program per output character on top of detlog2.
