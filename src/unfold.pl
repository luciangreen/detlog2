/*  unfold.pl - unfold the data of a program into answer tables, then
    replace every table by a loop found with Spec to Algorithm (S2A).

    1. Unfold.  A predicate is pure when its clauses use only conjunction,
       disjunction, true, the instantiation-monotone built-ins of
       pure_builtin_keys/1 and calls to pure predicates (recursion
       included).  For every pure predicate p/n, the most general goal
       p(A1, ..., An) is run once with ordinary Prolog semantics.  When its
       packet is finite (at most the row limit), writes no output and every
       answer is ground, that packet is p's whole answer table.

    2. Spec to Algorithm.  Each column of the table is described by the
       index I = 0 .. K-1 of its row:

         newton([D0, ..., Dd])   an integer polynomial of degree d =< 3,
                                 V = D0 + D1*C(I,1) + ... + Dd*C(I,d)
                                 (Newton's forward-difference form, so all
                                 coefficients are integers); accepted only
                                 when it fits at least d + 2 rows, so the
                                 formula explains more rows than it has
                                 coefficients
         const(T)                the same term in every row
         data([V0, ..., VK-1])   no formula: the values themselves

       The spec s2a(K, Columns) replaces the table:

         p__cp(A1, ..., An, Rows) :- s2a_rows(s2a(K, Columns), [A1, ..., An], Rows).

       s2a_rows/3 (Detlog runtime) builds the rows with a deterministic
       loop over I and keeps those that unify with the call.  When a column
       is linear (newton([D0, D1]), D1 =\= 0) and the call gives that
       argument as an integer X, the loop is skipped: I = (X - D0) / D1 is
       computed directly.  Either way no choicepoint is left.

    3. Proof (rule S2A in docs/proof_rules.md).  The checker re-derives
       purity, re-runs p(A1, ..., An) on the source program and requires
       that the spec's rows are exactly its packet, in order.  Purity is what
       carries the table over to every call: for a pure program whose most
       general goal has a finite packet of ground answers, the packet of
       p(T1, ..., Tn) is that packet filtered by unification with
       [T1, ..., Tn], in the same order, whenever the call raises no error
       (instance lemma).

    Objects are the object terms of term.pl (int/1, atom/1, comp/2, ...).
*/

% ---------------------------------------------------------------------------
% Purity

%  Built-ins whose answers for an instance of a call are the instances of
%  the call's answers, in the same order, when the instance raises no error
%  (an ill-typed instance, such as between(0, 6, a), raises an error that the
%  loop does not reproduce: docs/proof_rules.md, rule S2A).
pure_builtin_keys(['true/0', '=/2', 'is/2', '=:=/2', '=\\=/2', '</2', '>/2',
                   '=</2', '>=/2', 'between/3', 'member/2', 'succ/2', 'plus/3']).

%  pure_preds(+Program, -Keys): the greatest set of the program's own
%  predicates that are pure (an ordset).
pure_preds(P, Keys) :-
    prog_order(P, Order),
    sort(Order, Own),
    prog_preds(P, Preds),
    pure_fix(Own, Preds, Own, Keys).

pure_fix(Cur, Preds, Own, Keys) :-
    include(pure_pred(Preds, Own, Cur), Cur, Next),
    length(Cur, LC),
    length(Next, LN),
    if_commit(LN =:= LC, Keys = Cur, pure_fix(Next, Preds, Own, Keys)).

pure_pred(Preds, Own, Cur, K) :-
    map_find(Preds, K, [], Cls),
    Cls \== [],
    findall(x, ( member(clause(_, B, _), Cls), if_commit(pure_body(B, Own, Cur), fail, true) ), []).

pure_body(B, Own, Cur) :-
    if_commit(B = comp(',', [X, Y]),
              ( pure_body(X, Own, Cur), pure_body(Y, Own, Cur) ),
    if_commit(B = comp(';', [X, Y]),
              ( if_commit(X = comp('->', _), fail, true),
                if_commit(X = comp('*->', _), fail, true),
                pure_body(X, Own, Cur), pure_body(Y, Own, Cur) ),
              pure_goal(B, Own, Cur))).

pure_goal(G, Own, Cur) :-
    goal_key(G, just(F/N)),
    if_commit(ord_memberchk(F/N, Own),
              ord_memberchk(F/N, Cur),
              ( key_atom(F, N, KA), pure_builtin_keys(PK), memberchk(KA, PK) )).

% ---------------------------------------------------------------------------
% Unfolding: the answer table of the most general goal

%  general_goal(+Key, -Goal, -Args, -NVars)
general_goal(F/N, Goal, Args, N) :-
    head_vars_a(N, Args),
    if_commit(N =:= 0, Goal = atom(F), Goal = comp(F, Args)).

%  general_table(+Program, +MaxRows, +Key, -Either): right(Rows), each row
%  the list of the goal's ground arguments in one answer, in Prolog order;
%  left(Reason) when the packet is not a finite table of ground answers.
general_table(P, Max, Key, E) :-
    general_goal(Key, Goal, Args, NV),
    with_prelude(P, OP),
    default_options(Opts),
    ref_run(Opts, OP, Goal, NV, S),
    K is Max + 1,
    stream_take_events(K, S, Evs),
    list_t(Args, ArgsL),
    table_from_events(Evs, Max, ArgsL, E).

table_from_events(Evs, Max, ArgsL, E) :-
    findall(M, member(err(M), Evs), Errs),
    findall(O, member(out(O), Evs), Outs),
    findall(R, ( member(ans(St), Evs), resolve(ArgsL, St, R) ), Rs),
    length(Rs, NR),
    findall(R, ( member(R, Rs), max_var_id(R, MV), MV >= 0 ), NonGround),
    if_commit(Errs = [Err|_], format(string(Why), "raised: ~s", [Err]),
    if_commit(Outs \== [], Why = "writes output",
    if_commit(NR > Max, format(string(Why), "more than ~d answers (raise --max if it is finite)", [Max]),
    if_commit(NonGround \== [], Why = "an answer is not ground",
              Why = ok)))),
    if_commit(Why == ok,
              ( maplist(row_values, Rs, Rows), E = right(Rows) ),
              E = left(Why)).

row_values(R, Vs) :-
    static_list(R, just(Vs)).

% ---------------------------------------------------------------------------
% Spec to Algorithm: a loop for a table

%  s2a_spec(+Arity, +Rows, -Spec): Spec = s2a(K, Columns) as an object term.
s2a_spec(N, Rows, comp(s2a, [int(K), ColsT])) :-
    length(Rows, K),
    N1 is N - 1,
    findall(C, ( between(0, N1, J), column(Rows, J, Vs), column_spec(Vs, C) ), Cols),
    list_t(Cols, ColsT).

column(Rows, J, Vs) :-
    maplist(nth0_det(J), Rows, Vs).

nth0_det(J, L, X) :-
    J1 is J + 1,
    nth_det(J1, L, just(X)).

column_spec(Vs, C) :-
    if_commit(maplist(int_value, Vs, Is),
              ( newton_fit(Is, M), column_int(M, Vs, C) ),
              column_other(Vs, C)).

int_value(int(I), I).

column_int(nothing, Vs, C) :-
    column_other(Vs, C).
column_int(just(Ds), _, comp(newton, [DsT])) :-
    maplist(int_t, Ds, DTs),
    list_t(DTs, DsT).

int_t(I, int(I)).

column_other(Vs, C) :-
    if_commit(( Vs = [V|_], findall(x, ( member(W, Vs), if_commit(same_term(V, W, true), fail, true) ), []) ),
              C = comp(const, [V]),
              ( list_t(Vs, VsT), C = comp(data, [VsT]) )).

%  newton_fit(+Ints, -Maybe): just([D0, ..., Dd]) for the lowest degree
%  d =< 3 whose (d+1)-th differences are all zero, when the table has at
%  least d + 2 rows; otherwise nothing.
newton_fit(Is, M) :-
    length(Is, K),
    if_commit(K >= 2, fit_deg(0, Is, K, [], M), M = nothing).

fit_deg(D, L, K, Acc, M) :-
    L = [H|_],
    conc(Acc, [H], Acc1),
    diffs(L, L1),
    D2 is D + 2,
    if_commit(( all_zero(L1), K >= D2 ),
              M = just(Acc1),
              if_commit(D >= 3,
                        M = nothing,
                        if_commit(L1 == [],
                                  M = nothing,
                                  ( D1 is D + 1, fit_deg(D1, L1, K, Acc1, M) )))).

diffs([X|Xs], Ds) :-
    diffs_(Xs, X, Ds).

diffs_([], _, []).
diffs_([Y|Ys], X, [Z|Zs]) :-
    Z is Y - X,
    diffs_(Ys, Y, Zs).

all_zero(L) :-
    findall(x, ( member(X, L), X =\= 0 ), []).

% ---------------------------------------------------------------------------
% Evaluating a spec (shared by the interpreter's s2a_rows/3 and the proof
% checker; the native runtime has its own copy in detlog_runtime.pl)

%  spec_parts(+SpecObject, -Maybe): just(K-Columns) for a well-formed spec.
spec_parts(T, M) :-
    if_commit(( T = comp(s2a, [int(K), ColsT]), K >= 0, static_list(ColsT, just(Cols)),
                maplist(col_ok(K), Cols) ),
              M = just(K-Cols),
              M = nothing).

col_ok(K, comp(F, As)) :-
    col_ok_(F, As, K).

col_ok_(newton, [DsT], _) :-
    static_list(DsT, just(Ds)),
    length(Ds, L),
    L >= 1,
    maplist(int_value, Ds, _).
col_ok_(const, [_], _).
col_ok_(data, [VsT], K) :-
    static_list(VsT, just(Vs)),
    length(Vs, K).

%  spec_all_rows(+K, +Columns, -Rows): the K rows, I = 0 .. K-1.
spec_all_rows(K, Cols, Rows) :-
    K1 is K - 1,
    findall(R, ( between(0, K1, I), spec_row(Cols, I, R) ), Rows).

spec_row(Cols, I, R) :-
    maplist(col_value(I), Cols, R).

col_value(I, comp(F, As), V) :-
    col_value_(F, As, I, V).

col_value_(newton, [DsT], I, int(V)) :-
    static_list(DsT, just(Ds)),
    maplist(int_value, Ds, Is),
    newton_value(Is, I, V).
col_value_(const, [T], _, T).
col_value_(data, [VsT], I, V) :-
    static_list(VsT, just(Vs)),
    nth0_det(I, Vs, V).

%  newton_value(+Ds, +I, -V): V = sum of Dk * C(I, k).
newton_value(Ds, I, V) :-
    newton_acc(Ds, I, 0, 1, 0, V).

newton_acc([], _, _, _, V, V).
newton_acc([D|Ds], I, K, C, A, V) :-
    A1 is A + D * C,
    C1 is C * (I - K) // (K + 1),
    K1 is K + 1,
    newton_acc(Ds, I, K1, C1, A1, V).

%  spec_select(+K, +Columns, +ArgValues, -Rows): the rows to unify with the
%  call.  A linear column whose argument is an integer gives the row index
%  directly; otherwise every row.
spec_select(K, Cols, Args, Rows) :-
    s2a_numbered(Cols, 0, NCols),
    if_commit(( member(J-comp(newton, [DsT]), NCols), static_list(DsT, just([int(D0), int(D1)])),
                D1 =\= 0, nth0_det(J, Args, int(X)) ),
              index_rows(K, Cols, D0, D1, X, Rows),
              spec_all_rows(K, Cols, Rows)).

index_rows(K, Cols, D0, D1, X, Rows) :-
    Q is X - D0,
    if_commit(( Q mod D1 =:= 0, I is Q // D1, I >= 0, I < K ),
              ( spec_row(Cols, I, R), Rows = [R] ),
              Rows = []).

s2a_numbered(Xs, Start, NXs) :-
    length(Xs, L),
    Last is Start + L - 1,
    findall(I, between(Start, Last, I), Is),
    pairs_keys_values(NXs, Is, Xs).

% ---------------------------------------------------------------------------
% Showing a spec as formulas

spec_text(N, comp(s2a, [int(K), ColsT]), Text) :-
    static_list(ColsT, just(Cols)),
    N1 is N - 1,
    findall(S, ( between(0, N1, J), nth0_det(J, Cols, C), J1 is J + 1, col_text(C, J1, S) ), Ss),
    atomic_list_concat(Ss, ', ', A),
    K1 is K - 1,
    format(string(Text), "for I = 0..~d: ~w", [K1, A]).

col_text(comp(F, As), J, S) :-
    col_text_(F, As, J, S).

col_text_(newton, [DsT], J, S) :-
    static_list(DsT, just(DTs)),
    maplist(int_value, DTs, Ds),
    monomial(Ds, Cs),
    poly_text(Cs, P),
    format(string(S), "A~d = ~s", [J, P]).
col_text_(const, [T], J, S) :-
    show_term_q(T, TS),
    format(string(S), "A~d = ~s", [J, TS]).
col_text_(data, [VsT], J, S) :-
    static_list(VsT, just(Vs)),
    length(Vs, L),
    format(string(S), "A~d = row I of ~d listed values", [J, L]).

%  monomial(+NewtonDs, -Coeffs): the coefficients of 1, I, I^2, I^3 (rationals).
monomial(Ds, [C0, C1, C2, C3]) :-
    conc(Ds, [0, 0, 0, 0], Ds4),
    Ds4 = [D0, D1, D2, D3|_],
    C0 is D0,
    C1 is D1 - D2 rdiv 2 + D3 rdiv 3,
    C2 is D2 rdiv 2 - D3 rdiv 2,
    C3 is D3 rdiv 6.

poly_text(Cs, Text) :-
    s2a_numbered(Cs, 0, NCs),
    findall(T, ( member(P-C, NCs), C =\= 0, term_text(P, C, T) ), Ts),
    if_commit(Ts == [],
              Text = "0",
              ( atomic_list_concat(Ts, ' + ', A), atom_string(A, Text) )).

term_text(P, C, T) :-
    coeff_text(C, CT),
    power_text(P, PT),
    if_commit(P =:= 0, T = CT,
    if_commit(C =:= 1, T = PT,
              format(atom(T), "~w*~w", [CT, PT]))).

coeff_text(C, T) :-
    if_commit(integer(C),
              format(atom(T), "~d", [C]),
              ( N is numerator(C), D is denominator(C), format(atom(T), "(~d/~d)", [N, D]) )).

power_text(P, T) :-
    if_commit(P =:= 1, T = 'I', format(atom(T), "I^~d", [P])).

% ---------------------------------------------------------------------------
% The S2A clauses in the converted program

%  s2a_clause(+Key, +Spec, -Clause)
s2a_clause(F/N, Spec, clause(comp(CF, HArgs), comp(s2a_rows, [Spec, ArgsL, RowsV]), NV)) :-
    cp_name(F, CF),
    head_vars_a(N, Args),
    RowsV = var(N, 'Rows'),
    conc(Args, [RowsV], HArgs),
    list_t(Args, ArgsL),
    NV is N + 1.

%  add_s2a_tables(+Entries, +Converted, -Program, -Steps): Entries are
%  Key-Spec pairs.
add_s2a_tables(Entries, Conv, P, Steps) :-
    foldl(add_s2a, Entries, Conv-[], P-Steps).

add_s2a(Key-Spec, prog(Preds, Order, Ds)-Steps0, prog(Preds1, Order1, Ds)-Steps) :-
    s2a_clause(Key, Spec, Cl),
    Key = F/N,
    cp_name(F, CF),
    N1 is N + 1,
    CK = CF/N1,
    map_put(CK, [Cl], Preds, Preds1),
    exclude(==(CK), Order, O1),
    conc(O1, [CK], Order1),
    key_t(Key, KT),
    clause_t(Cl, CT),
    conc(Steps0, [comp(s2a_table, [KT, CT])], Steps).

% ---------------------------------------------------------------------------
% Rule S2A, checked by evaluation

check_s2a_step(pctx(_, _, Orig), S, [Cl]) :-
    if_commit(S = comp(s2a_table, [KT, ClT]), true, pfail("bad s2a step")),
    term_key_or(KT, "s2a_table: bad key", F/N),
    show_key(F/N, KS),
    format(string(Here), "S2A loop for ~s: ", [KS]),
    as_clause(ClT, Cl),
    Cl = clause(H, B, _),
    % 1. the template
    cp_name(F, CF),
    N1 is N + 1,
    wmsg(Here, "not an s2a_rows clause", M1),
    ensure(( H = comp(CF, HArgs), length(HArgs, N1), B = comp(s2a_rows, [Spec, ArgsT, RowsT]) ), M1),
    take(N, HArgs, Args),
    last_of(HArgs, Last),
    list_t(Args, ArgsL),
    wmsg(Here, "frame", M2),
    ensure(( distinct_vars(HArgs), teq(ArgsT, ArgsL), teq(RowsT, Last) ), M2),
    wmsg(Here, "the spec is not well formed", M3),
    ensure(spec_parts(Spec, just(_)), M3),
    spec_parts(Spec, just(K-Cols)),
    wmsg(Here, "a column has the wrong arity", M4),
    length(Cols, LC),
    ensure(LC =:= N, M4),
    % 2. purity, so the table holds for every call (instance lemma)
    pure_preds(Orig, Pure),
    wmsg(Here, "the predicate is not pure (cut, negation, if-then-else, a type test, output, or a call to such a predicate)", M5),
    ensure(ord_memberchk(F/N, Pure), M5),
    % 3. the spec's rows are the packet of the most general goal
    spec_all_rows(K, Cols, Rows),
    general_table(Orig, K, F/N, TE),
    if_commit(TE = right(Actual), true,
              ( TE = left(Why), format(string(M6), "~sthe most general goal is not a finite table: ~s", [Here, Why]),
                pfail(M6) )),
    format(string(M7), "~sthe loop's rows are not the program's answers, in order", [Here]),
    empty_state(0, St0),
    ensure(( same_length(Rows, Actual), maplist(row_variant(St0), Rows, Actual) ), M7).

row_variant(St, R, A) :-
    list_t(R, RT),
    list_t(A, AT),
    variant_ok(St, RT, AT).
