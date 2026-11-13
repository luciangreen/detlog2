# Does detlog2 work, and does it optimise?

**Yes, by its own tests, proofs and CI, it does what it claims.** Its optimisation is real, but it is limited and layered.

The input Prolog and the Detlog output for every example are listed in
[examples.md](examples.md).

## What detlog2 is

detlog2 reimplements the earlier SWI-Prolog Detlog. It has four main pieces.

1. **A choicepoint-free, cut-free interpreter.**
   - Goals produce *answer packets*: lists of answers and of the output written between them.
   - Conjunction splices packets, and disjunction concatenates them.
   - There is no choicepoint stack and no trail. A cut (`!`) is rejected.
   - Commitment is written with `if_commit/3`, or with `once/1` or `\+/1`.

2. **A converter.**
   - Cuts become explicit decisions (`if_commit/3`).
   - Choicepoints become packets and deterministic combinators: `member_cp/2`, `between_cp/3`, `splice/2`, `splice_extend/4`, `rows_concat/2`, and so on.
   - Every predicate `p/n` becomes a deterministic `p__cp(..., Rows)`. It succeeds once and returns the full answer packet.
   - The output contains no cut, no `;`, no `->`, no `call/N` and no nondeterministic built-in.
   - The checker verifies this shape statically. The runtime `--det` mode confirms at most one answer per call.

3. **A memoiser.**
   - It runs selected goals under ordinary cut semantics.
   - It stores their complete answer packets as tables.
   - So even cuts and choicepoints that are hard to convert disappear into data.

4. **An mnns bridge.**
   - It can first run the separate mnns optimiser: proof-checked rewrites such as `findall` to loops, and lowering of `once/1` and terminal cuts.
   - It then converts the result.

Conversions are **proof-carrying**: every rewrite is recorded and independently re-checked, and a bad proof is rejected.

`detlog2 check` converts a program and checks that the result is choicepoint-free. It then compares the answer sequences, including order, duplicates and output, against a reference interpreter that uses ordinary cut semantics.

## Does it actually work?

- **CI.** GitHub Actions runs on `main` are green as of mid-November 2026.
- **End-to-end tests.** They exercise conversion, checking, packets, memoisation, and proof rejection on mutated inputs.
- **200 recorded runs.** `io/ios.txt` holds 200 inputs and outputs, and CI re-runs all of them.
- **Plain SWI-Prolog.** The converted programs also run outside detlog2.
  - `tests/native_tests.pl` loads each converted example into SWI-Prolog with only [`src/detlog_runtime.pl`](../src/detlog_runtime.pl).
  - It compares 30 queries with the original programs running on SWI-Prolog itself, cuts included.
  - All 30 give the same answers, in the same order, with the same output, and every converted call leaves no choicepoint.
- **The runtime.** `src/detlog_runtime.pl` is written in the style it supports: no cut, no `;`, no `->`, no `\+`, and clauses told apart by their first argument.
  - `tools/cutfree.pl` checks this.
  - `tests/runtime_tests.pl` runs 49 tests, each of which must leave no choicepoint.
- **Documented limits.**
  - Infinite generators have no finite packet, which is an error.
  - `bagof/3` and `setof/3` do not group by free variables.
  - Some cut placements inside disjunctions or if-then-else are unsupported, and must be memoised instead.

So for the supported fragment, it does replace choicepoints with splices and cuts with `if_commit/3`. The tests and the independent proof checker give reasonable evidence that the transformation preserves observable behaviour.

## Does it optimise?

- **Yes, in a structural sense.**
  - It turns nondeterministic search into building packets and iterating over them, deterministically.
  - Independent generators are computed once and then spliced: their Cartesian product, in Prolog order.
  - Memoisation turns repeated work into a table lookup.
  - The mnns front end can apply further proven rewrites before conversion.
- **No, not in the classic sense** of making the program faster by algebraic simplification, loop fusion or closed forms.
  - That is closer to the related tools: [plop2](https://github.com/luciangreen/plop2) (one program per output character) and [algebraplop2](https://github.com/luciangreen/algebraplop2) (proved closed forms).
  - detlog2's main goal is determinisation and explicit control, not peak performance.
  - Packets still have to be built, or at least walked, so very large answer sets cost memory and time. Infinite generators are rejected.

**Bottom line.** For finite, supported Prolog, it does what the README says: choicepoints become splices and packets, and cuts become decisions. The result runs deterministically, both on detlog2 and on plain SWI-Prolog with the runtime library, and it is checked.

The optimisation is real, but it is mainly about removing hidden nondeterminism, not about large speed-ups.
