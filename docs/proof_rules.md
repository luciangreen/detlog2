# detlog2 proof rules

`detlog2 convert` writes `OUT` and `OUT.proof`. The proof is a list of
Prolog terms, one step per rewrite. `src/proof.pl` checks it without using
the converter: `detlog2 proof-check SOURCE OUT OUT.proof`. Every command that
converts (`convert`, `check`, `packets`, `memoise`, `mnns`) runs the checker
first, and writes nothing that the checker rejects.

## Semantics

The **packet** of a goal G in an environment θ, written ⟦G⟧θ, is the list of
events Prolog produces when it runs G under θ:

- one row `[V1θ', ..., Vkθ']` for each answer θ' (in order, duplicates kept);
- one item `out(Text)` for each piece of output, in the position where
  Prolog writes it.

Prolog's own failure-driven backtracking enumerates exactly this list, so two
goals with equal packets in every θ cannot be told apart by answers, their
order, their multiplicity or their output.

Each rule below states a lemma of the form "the generated code computes
⟦G⟧θ". The checker re-establishes the rule's syntactic side conditions; the
lemma is what makes the rule sound. A rule's generated code may use fresh
variables only (variables that do not occur in the clause), and each fresh
variable may be introduced once.

## Program rules

**CUT (cut elimination).** Take a predicate with clauses
C1 … Cn, where Ci = `H_i :- G_i, !, B_i` or a cut-free clause.

- **Rewrite.** The predicate is replaced by one clause
  `p(A1..An) :- D1`, where:
  - for a clause with a cut,
    `Di = if_commit((A = h_i, G_i), B_i', D(i+1))`;
  - for a cut-free clause, `Di = ((A = h_i, Body_i) ; D(i+1))`;
  - `D(n+1) = fail`;
  - in `B_i'`, every later cut `X, !, Y` becomes `if_commit(X, Y', fail)`.
- **Local cuts.** A cut inside `\+`, `once/1`, `call/1`, `findall/3`,
  `forall/2`, `aggregate_all/3` or an if-then-else condition is local to that
  goal and becomes `if_commit(before, after, fail)` in place.
- **Lemma.** Cut commits to the first answer of `A = h_i, G_i` and discards
  the remaining clauses. That is exactly `if_commit/3`'s semantics: the head
  of the condition's packet, with the else branch taken only when the packet
  has no row. After the cut, the remaining clauses are gone, so a later cut
  only discards the answers of the goals before it, which is
  `if_commit(…, …, fail)`.
- **Check.** The checker re-derives the cut-free predicate with its own
  implementation and compares the compiled clauses with it, up to variable
  renaming.
- **Not supported.** A cut in a disjunction or if-then-else branch cuts the
  clause from inside a nested goal. CUT does not apply there, and the
  conversion stops; memoise such predicates instead (rule MEMO).

**SPEC (closure specialisation).** `q(…, Clo, …)`, where Clo is a callable
term at an argument that q calls with `call/N`, becomes
`q_spec(vars(Clo), …)`.

- **Definition.** The clauses of `q_spec` are those of q, with the closure
  variable replaced by a renamed Clo and `call(Clo', X…)` read as the goal
  `Clo'(X…)`.
- **Lemma.** Unifying the head variable with Clo at call time is the same
  substitution, and `call/N` of a known term is that term's goal.
- **Check.** The checker rebuilds every `q_spec` from `closure_spec` steps and
  accepts a call site either unchanged or replaced by its specialised copy.

**PRED and FACTS (predicate packets).**

- **PRED.** `p__cp(A, Rows) :- p__cp_c1(A, R1), …, rows_concat([R1…Rn], Rows)`.
  A predicate's packet is the concatenation of its clauses' packets, in
  clause order.
- **FACTS.** For facts f1 … fn the code is
  `member_cp(P, [args(f1), …, args(fn)]), cp_filter(P, A, Rows)`, with the
  rows renamed apart. The packet of a fact predicate is the list of fact
  instances that unify with the call.

**CLAUSE (clause packet).**

```prolog
p__cp_ci(Args, Rows) :-
    if_commit(copy_term(Args, HeadArgs), (Code, splice_extend(Env, HeadArgs, Vs, Rows)), Rows = [])
```

Here `Vs` is the list of all clause variables, and `Code` is a derivation of
the body that computes the environment packet `Env`.

- **Lemma.** Renaming the call apart and unifying it with the head is
  resolution. If unification fails the clause contributes nothing. Otherwise
  each environment row, projected onto the head arguments, is one answer of
  the clause.

**ROWS (packet iteration).** An auxiliary predicate with the clauses
`name([], [])` and
`name([Row|Rs], Out) :- if_commit(Row = out(T), Out1 = [out(T)], (copy_term(Row, Vs), Code)), name(Rs, Out2), rows_concat([Out1, Out2], Out)`
maps a packet to the concatenation of the goal's packet in each row.
Output items pass through in place.

- **Lemma.** The packet of `(A, B)` is ⟦A⟧ with every row ρ replaced by
  ⟦B⟧ρ. This is depth-first, left-to-right execution, written as a fold.

**MEMO (memo tables).**

```prolog
p__cp(A, Rows) :- if_commit(memo_lookup(A, Table, Rows), true, Fallback)
```

- **Fallback.** Fallback is `p__cp__compute(A, Rows)`, or `memo_miss/2` when
  the table is complete.
- **Check.** The checker checks the template, then re-runs every table entry
  with ordinary Prolog semantics and requires exactly the recorded packet,
  including output items. This is proof by evaluation.

**S2A (unfolded data as a loop).**

```prolog
p__cp(A1, ..., An, Rows) :- s2a_rows(s2a(K, [Col1, ..., Coln]), [A1, ..., An], Rows)
```

Each column `Colj` is `newton(Ds)`, `const(T)` or `data(Vs)` (README, part 5).
Row I, for I = 0 .. K-1, is `[v1(I), ..., vn(I)]` with
`newton([D0, ..., Dd])` giving `D0 + D1*C(I,1) + ... + Dd*C(I,d)`, `const(T)`
giving T and `data(Vs)` giving the I-th element of Vs.

- **Purity.** p is pure: every clause of p, and of every predicate it calls,
  uses only `,`, `;` (without `->`), `true`, `=/2`, `is/2`, the arithmetic
  comparisons, `between/3`, `member/2`, `succ/2`, `plus/3` and calls to pure
  predicates. The checker computes this itself, as the greatest set of
  predicates closed under these conditions.
- **Instance lemma.** Let p be pure and let ⟦p(A1..An)⟧ be finite, with
  ground answers and no output. Then for every call p(T1..Tn),
  ⟦p(T1..Tn)⟧ is ⟦p(A1..An)⟧ with the rows that do not unify with
  `[T1..Tn]` left out, in the same order and with the same multiplicities,
  whenever the call p(T1..Tn) raises no error.
  *Reason:* every SLD derivation of the instance is an instance of a
  derivation of the general goal, taken in the same order (lifting). For
  the built-ins allowed above, binding an argument only removes answers,
  never adds, reorders or duplicates them. Each general answer is ground,
  so it yields at most one answer of the instance: the instance itself,
  when it unifies. A rule that is not pure (a cut, `\+`, `->`, `var/1`,
  output) can change with the binding, so it is excluded.
- **Errors are not preserved.** A call whose argument makes a built-in raise
  an error, such as `square(a, S)` reaching `between(0, 6, a)`, raises a type
  error in Prolog but gives no rows from the loop. The lemma, and so the rule,
  covers calls that raise no error.
- **Check.** The checker checks the template (head variables distinct, the
  argument list is the head arguments, one column per argument, a
  well-formed spec), re-derives purity, re-runs p(A1..An) on the source
  program with ordinary Prolog semantics, and requires its packet to be
  exactly the K rows of the spec, in order: proof by evaluation.
- **Runtime.** `s2a_rows/3` computes the K rows in a loop and keeps those that
  unify with the call (`splice_extend/4`). When a column is
  `newton([D0, D1])` with D1 ≠ 0 and the call gives that argument as an
  integer X, it computes the single row I = (X − D0)/D1 when that is an
  integer in 0 .. K−1, and no row otherwise. This is the same filter: the
  only row whose column can equal X is row I.

## Goal rules

In every goal rule, E is the environment row (the clause variables) and O is
the output packet.

| rule | source | generated code | lemma |
| --- | --- | --- | --- |
| true / fail | `true`, `fail` | `O = [E]`, `O = []` | one empty answer; none |
| det | deterministic built-in B (not user-defined, no output) | `if_commit(B, O = [E], O = [])` | B has at most one answer |
| effect | `write/1` etc. | `effect_text(B, T), O = [out(T), E]` | B writes T and succeeds once |
| call | user predicate q | `q__cp(Args, P), splice_extend(P, E, Args, O)` | each answer row of q, unified with the call, extends E |
| member_cp / between_cp | `member(X, L)`, `between(L, H, X)` | the list as a packet, spliced on `[X]` | answers are the elements in order |
| length_det | `length/2` | `if_commit(length_det(L, N), …)` | det in its supported modes; error otherwise |
| builtin_rows | other nondeterministic built-ins | `builtin_rows(B, R), splice_extend(R, E, [B], O)` | the built-in's answers as a packet |
| seq | `G1, G2…` | Code(G1 → R1), ROWS(G2… over R1 → O) | ROWS lemma |
| det_prefix | `B1…Bk, Rest` (det built-ins first) | `if_commit((B1…Bk), Code(Rest), O = [])` | the prefix has at most one answer and binds E in place |
| disj | `(A ; B)` | ROWS(A over [E]), ROWS(B over [E]), `rows_concat` | the packet of a disjunction is the concatenation |
| ite_det | `(C -> T ; F)`, C det built-ins | `if_commit(C, Code(T), Code(F))` | C has at most one answer |
| ite | `(C -> T ; F)`, `once/1`, `ignore/1` | ROWS(C over [E] → Rc), `packet_first(Rc, Pre, Res)`, then Pre ++ (T on the first row, or F) | commitment: output of C up to its first answer, then T on that answer; F if C has no answer |
| neg_det / neg | `\+ G` | as ite with T = fail, F = true | negation as failure |
| findall | `findall(T, G, L)` | ROWS(G over [E]), `packet_split`, project T, unify L | all of G's output, then one answer |
| count | `aggregate_all(count, G, N)` | as findall, with the number of rows | the same |
| rewrite | `forall/2`, `aggregate_all(bag(T), …)`, `decision/2`, `call(G, X…)` | the fixed equivalent goal | standard identities |
| splice | independent generators G1…Gk (k ≥ 2), then Rest | `if_commit(splice_safe(Pats), Chain, Seq)`, then ROWS(Rest) | see below |

**The splice rule in detail.** Chain computes each Gi's packet once, stops as
soon as one is empty, and combines them with `splice/2`, a Cartesian product
in left-to-right order. Seq is the sequential code for the same goals, and it
is derived and checked separately.

- **Side conditions.**
  - The Gi share no variables syntactically.
  - Each Gi is a generator: a user predicate, `member/2` or `between/3`.
  - No Gi writes output, transitively.
- **Run-time guard.** `splice_safe/1` checks that the argument groups share
  no unbound variable at run time.
- **Lemma.** When no Gi binds anything another Gi reads, ⟦G1, G2⟧ is the
  product of ⟦G1⟧ and ⟦G2⟧, in Prolog's order (G1 varies slowest). Computing
  ⟦G2⟧ once instead of once per answer of G1 changes neither answers nor
  output, because G2 writes nothing. The stop-if-empty step ensures G2 runs
  only when Prolog would run it at least once.

## Choicepoint-freedom

Separately, `src/check.pl` verifies that the converted program has the
following shape:

- no cut, `;`, `->` or `call/N`, and no nondeterministic built-in;
- every `if_commit/3` condition is a deterministic built-in;
- every predicate has one clause, or exactly the `[]` / `[_|_]` iteration
  pair.

Under this discipline, at most one clause can match any call, so no call
leaves an alternative. `--det` checks the same property at run time.

## What is not proved

- **mnns rewrites.** detlog2's proof is relative to the program mnns
  produced; mnns keeps only rewrites accepted by its own independent checker.
- **Infinite generators** (`between(1, inf, X)`, `length(L, N)` with both
  unbound). They have no finite packet, so converted code raises an error
  rather than giving a wrong answer.
- **Errors and non-termination after the first answer of a committed goal.**
  Packets are complete, so a condition that loops after its first answer
  loops in converted code, while Prolog would have stopped.
