# detlog2

detlog2 is Detlog redone in cut-free, choicepoint-free Prolog. It has four
parts:

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

detlog2 is written in SWI-Prolog. The Prolog has no cut, `;`, `->`, `\+`,
`once/1` or other pruning or backtracking construct, and no predicate leaves a
choicepoint:

- commitment is `if_commit/3` from the Detlog runtime;
- alternatives are data, as packets and lazy answer streams;
- the clauses of a predicate are told apart by their first argument, so
  first-argument indexing selects exactly one.

[`tools/cutfree.pl`](tools/cutfree.pl) checks all of this for every source
file in CI.

```sh
swipl build.pl            # builds build/detlog2 (a saved state)
swipl build.pl test       # builds, checks the sources are cut-free and choicepoint-free,
                          # then runs the runtime, end-to-end and native tests
swipl build.pl ci         # as test, then checks the 200 recorded inputs and outputs
swipl detlog2.pl run FILE QUERY   # or run from source, without building
```

The Haskell version it was ported from is kept in [`haskell/`](haskell/).
Build and test it with `runghc haskell/Build.hs test`. CI runs both, and
checks that they give the same output for all 200 recorded inputs:
`swipl io/ios.pl compare haskell/io/ios.txt`.

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

`src/check.pl` verifies this structure for every converted program, and
`check` and `packets` also run the result with `--det`.

**`detlog2 check FILE QUERY...` does three things:**

1. converts the program;
2. runs the choicepoint check;
3. compares the answer sequence of the source (ordinary cut semantics) with
   that of the converted code, including order and duplicates.

For the original Detlog sample this covers `det_sum/2`, `if_then_else/2` and
`safe_cut/1`, which are converted, not fallen back.

**Output is data.** An output built-in such as `write(X)` becomes
`effect_text(write(X), T)`, and the packet gets the item `out(T)` at the place
where Prolog writes it. Packets therefore carry output in exactly Prolog's
order, interleaved with the answers. `check` fails if the output differs in
any way.

**Every conversion carries a proof.** `convert -o OUT` also writes
`OUT.proof`: one Prolog term per rewrite, naming its rule, the source and the
code it produced.

- `src/proof.pl` checks the proof independently of the converter:
  - it re-derives cut elimination and closure specialisation itself;
  - it checks every generated goal against its rule's template and side
    conditions;
  - it requires every clause of the output to be justified.
- Nothing is written unless the proof is accepted.
- `detlog2 proof-check SOURCE OUT OUT.proof` re-checks the proof from files.
- The rules and their lemmas are in [docs/proof_rules.md](docs/proof_rules.md).

The tests change one character of the code, the source, the proof or a memo
table, and check that the proof is rejected.

**Limits:**

- **Infinite generators.** A generator with infinitely many answers
  (`between(1, inf, X)`, `length(L, N)` with both unbound) has no finite
  packet, and converted code raises an error.
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
- The proof checker re-runs every table entry with ordinary Prolog semantics
  and requires exactly the recorded packet.

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
| `cp_filter(P, Pattern, Rows)` | the rows of a fact packet that unify with Pattern |
| `splice_safe(Groups)` | the groups share no unbound variable, so they can be spliced |
| `length_det/2`, `builtin_rows/2`, `effect_text/2`, `packet_first/3`, `packet_split/3` | deterministic built-in modes, output as data, packet access |

### The runtime in plain Prolog

[`src/detlog_runtime.pl`](src/detlog_runtime.pl) implements every construct above as an SWI-Prolog module, so converted programs run without detlog2.

The library is written in the style it supports:

- no cut, `;`, `->`, `\+` or `once/1`;
- clauses are told apart by their first argument, so first-argument indexing leaves no choicepoint;
- `if_commit/3` takes the first answer of its condition with `findall/3` over `limit/2`.

`swipl tools/cutfree.pl -- FILE...` checks these rules. `swipl tests/runtime_tests.pl` runs the runtime's tests, each of which must leave no choicepoint.

[`tests/native_tests.pl`](tests/native_tests.pl) runs every converted example on plain SWI-Prolog. It compares each query with the original program, cuts included, run on SWI-Prolog itself.

See [docs/examples.md](docs/examples.md) for the input Prolog and output Detlog of every example, and [docs/report.md](docs/report.md) for what detlog2 does and does not optimise.

## Layout

```
detlog2.pl                the command line (loads src/)
src/detlog_runtime.pl     the Detlog runtime as a cut-free SWI-Prolog module
src/term.pl               terms, immutable substitutions, unification
src/stream.pl             lazy answer streams (packets)
src/reader.pl             standard Prolog reader (operators, strings as char lists)
src/pretty.pl             re-readable printing
src/builtins.pl           built-ins and the Detlog runtime over object terms
src/prelude.pl            library predicates for interpreted programs
src/interp.pl             the choicepointless, cutless interpreter
src/reference.pl          ordinary cut semantics (oracle for checks and memo tables)
src/cut_elim.pl           cuts -> if_commit/3
src/convert.pl            choicepoints -> packets and splices
src/check.pl              static choicepoint-freedom check, answer comparison
src/proof.pl              independent proof checker (docs/proof_rules.md)
src/proof_steps.pl        its step and derivation rules
src/memo.pl               answer tables, mnns optimise.pl bridge
src/cli.pl                the commands
tools/cutfree.pl          cut-free / choicepoint-free source checker
tests/cli.pl              end-to-end tests
tests/runtime_tests.pl    runtime tests on SWI-Prolog
tests/native_tests.pl     converted examples on plain SWI-Prolog vs the originals
io/ios.pl, io/ios.txt     200 recorded inputs and outputs
build.pl                  build and test
docs/examples.md          input Prolog and output Detlog for every example
docs/report.md            does detlog2 work, and does it optimise?
haskell/                  the Haskell version (src/Detlog2/*.hs, app/, tests/, io/, Build.hs)
```

Related: [plop2](https://github.com/luciangreen/plop2) builds one separate
program per output character on top of detlog2.
