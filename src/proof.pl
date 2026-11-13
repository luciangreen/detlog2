/*  proof.pl - the independent checker for detlog2 conversion proofs.

    The converter (convert.pl) emits one proof step per rewrite.  This
    module checks them without using the converter or the cut eliminator:

      1. It re-derives the cut-free intermediate program from the source
         with its own implementation of the cut-elimination lemma (rule CUT)
         and of closure specialisation (rule SPEC), and checks that the
         clauses the converter compiled are these clauses, up to variable
         renaming and up to calls replaced by their specialised copies.
      2. For every generated clause it checks the step that justifies it:
         PRED, FACTS, CLAUSE, ROWS and MEMO.  Inside clauses, each
         derivation node is checked against its rule: the generated goals
         must be exactly the rule's template instantiated with the source
         goal, the sub-derivations' code and fresh variables, and the rule's
         side conditions must hold.
      3. Every clause of the converted program must be justified, and every
         justification must be in the program.

    The rules are in docs/proof_rules.md.  A failed condition is thrown as
    proof_fail(Message) and returned as left(Message).

    Context: pctx(Source, External, Original).
*/

%  teq(+A, +B): term equality as Haskell's Eq (variables by id).
teq(A, B) :-
    same_term(A, B, true).

ensure(G, Msg) :-
    if_commit(G, true, throw(proof_fail(Msg))).

pfail(Msg) :-
    throw(proof_fail(Msg)).

show_key(F/N, S) :-
    format(string(S), "~w/~d", [F, N]).

term_key(T, M) :-
    if_commit(T = comp('/', [atom(F), int(N)]), M = just(F/N), M = nothing).

term_key_or(T, Msg, K) :-
    term_key(T, M),
    if_commit(M = just(K0), K = K0, pfail(Msg)).

as_clause(T, C) :-
    max_var_id(T, MV),
    NV is MV + 1,
    if_commit(T = comp(':-', [H, B]),
              C = clause(H, B, NV),
              if_commit(is_callable_t(T, true),
                        C = clause(T, atom(true), NV),
                        ( show_term_q(T, S), format(string(M), "not a clause: ~s", [S]), pfail(M) ))).

list_of(T, L) :-
    static_list(T, M),
    if_commit(M = just(L0), L = L0, ( show_term_q(T, S), format(string(Msg), "not a list: ~s", [S]), pfail(Msg) )).

% ---------------------------------------------------------------------------
% Proof files are plain Prolog terms, one step per clause.

proof_to_text(Steps, Text) :-
    maplist(step_line, Steps, Ls),
    atomic_list_concat(["% detlog2 conversion proof: one step per rewrite (see docs/proof_rules.md).\n"|Ls], A),
    atom_string(A, Text).

step_line(S, L) :-
    show_term_q(S, T),
    format(string(L), "~s.\n", [T]).

proof_from_text(Src, E) :-
    parse_program(Src, PE),
    proof_from_prog(PE, E).

proof_from_prog(left(M), left(M)).
proof_from_prog(right(P), right(Steps)) :-
    program_clauses(P, KCs),
    findall(T, ( member(_-Cs, KCs), member(C, Cs), clause_term(C, T) ), Steps).

% ---------------------------------------------------------------------------
% Entry point

check_proof(Ctx, Steps, Conv, E) :-
    catch(( check_proof_(Ctx, Steps, Conv, R), E = right(R) ),
          proof_fail(M),
          E = left(M)).

check_proof_(pctx(Src, Ext0, Orig), Steps, Conv, [Report]) :-
    findall(K, ( member(comp(memo_table, [KT, atom(true), _]), Steps), term_key(KT, just(K)) ), CM1),
    findall(K, ( member(comp(s2a_table, [KT, _]), Steps), term_key(KT, just(K)) ), CS0),
    conc(CM1, CS0, CM0),
    sort(CM0, CM),
    ord_union(Ext0, CM, Ext),
    Ctx = pctx(Src, Ext, Orig),
    base_program(Src, Base0),
    findall(S, ( member(S, Steps), S = comp(closure_spec, _) ), SpecSteps),
    map_empty(T0),
    foldl(add_spec, SpecSteps, Base0-T0, Base-SpecTable),
    findall(S, ( member(S, Steps), S = comp(F, _), memberchk(F, [pred_packet, facts_packet]) ), PredSteps),
    findall(S, ( member(S, Steps), S = comp(clause_packet, _) ), ClauseSteps),
    findall(S, ( member(S, Steps), S = comp(aux, _) ), AuxSteps),
    findall(S, ( member(S, Steps), S = comp(memo_table, _) ), MemoSteps),
    findall(S, ( member(S, Steps), S = comp(s2a_table, _) ), S2ASteps),
    % 1. the compiled clauses are the cut-free intermediate clauses
    maplist(intermediate_of(Base, ClauseSteps, SpecTable), PredSteps, InterPairs),
    map_from_pairs(InterPairs, Inter),
    prog_preds(Src, SrcPreds),
    map_member(SrcPreds, member/2, UserMember),
    map_keys(Inter, IK),
    findall(K, ( member(comp(memo_table, [KT|_]), MemoSteps), term_key(KT, just(K)) ), MK0),
    sort(MK0, MK),
    ord_union(IK, Ext, D1),
    ord_union(D1, MK, Defined),
    effectful_of(Inter, Eff0),
    ord_union(Eff0, Ext, Effectful),
    prog_order(Conv, CO),
    sort(CO, ConvKeys),
    findall(N-S, ( member(S, AuxSteps), S = comp(aux, [atom(N), _, _, _]) ), AuxPairs),
    map_from_pairs(AuxPairs, AuxMap),
    Cx0 = pcx(Defined, Effectful, UserMember, ConvKeys, AuxMap, atom('[]'), []),
    % 2. every step
    maplist(check_pred_step(Inter), PredSteps, PredCls),
    maplist(check_clause_step(Cx0), ClauseSteps, ClauseCls),
    maplist(check_aux_step(Cx0), AuxSteps, AuxCls),
    maplist(check_memo_step(Ctx), MemoSteps, MemoCls),
    maplist(check_s2a_step(Ctx), S2ASteps, S2ACls),
    % 3. coverage: the converted program is exactly the justified clauses
    findall(CF-CFC, ( member(comp(memo_table, [KT, C, _]), MemoSteps), term_key(KT, just(F/_)),
                      C \== atom(true), cp_name(F, CF), atom_concat(CF, '__compute', CFC) ), Renamed),
    concat_lists(PredCls, PC),
    maplist(rename_head(Renamed), PC, PC1),
    concat_lists([PC1|ClauseCls], J1),
    concat_lists(AuxCls, J2),
    concat_lists(MemoCls, J3),
    concat_lists(S2ACls, J4),
    concat_lists([J1, J2, J3, J4], Justified),
    by_key(Justified, ByKey),
    program_clauses(Conv, ConvKCs),
    maplist(coverage(ByKey), ConvKCs),
    map_keys(ByKey, BK),
    maplist(in_conv(ConvKeys), BK),
    length(Steps, NS),
    findall(C, ( member(_-Cs, ConvKCs), member(C, Cs) ), AllConv),
    length(AllConv, NC),
    format(string(Report), "proof accepted: ~d steps, ~d clauses justified", [NS, NC]).

intermediate_of(Base, ClauseSteps, SpecTable, S, Key-Cls) :-
    S = comp(Kind, [KT|_]),
    term_key_or(KT, "bad predicate indicator in a step", Key),
    show_key(Key, KS),
    prog_preds(Base, BP),
    map_get(BP, Key, MB),
    if_commit(MB = just(BaseCls), true,
              ( format(string(M), "no source predicate ~s", [KS]), pfail(M) )),
    intermediate_kind(Kind, Key, KS, BaseCls, ClauseSteps, SpecTable, Cls).

intermediate_kind(facts_packet, _, KS, BaseCls, _, _, BaseCls) :-
    format(string(M), "~s: facts_packet for a predicate that is not all facts", [KS]),
    ensure(( BaseCls \== [], all_facts(BaseCls) ), M).
intermediate_kind(pred_packet, Key, KS, BaseCls, ClauseSteps, SpecTable, Srcs) :-
    findall(CS, ( member(CS, ClauseSteps), CS = comp(clause_packet, [K|_]), term_key(K, just(Key0)), Key0 == Key ), Mine),
    length(Mine, LM),
    length(BaseCls, LB),
    format(string(M), "~s: ~d clauses but ~d clause_packet steps", [KS, LB, LM]),
    ensure(LM =:= LB, M),
    numbered_list(BaseCls, 1, NB),
    maplist(match_clause_step(Mine, KS, SpecTable), NB, Srcs).

match_clause_step(Mine, KS, SpecTable, I-BC, SrcC) :-
    findall(C, ( member(C, Mine), C = comp(clause_packet, [_, int(J), _, _, _]), J =:= I ), Cs),
    if_commit(Cs = [C1], true,
              ( format(string(M), "~s: missing or repeated clause_packet ~d", [KS, I]), pfail(M) )),
    C1 = comp(clause_packet, [_, _, SrcT, _, _]),
    as_clause(SrcT, SrcC),
    if_commit(clause_matches(SpecTable, BC, SrcC),
              true,
              ( clause_term(BC, BT), clause_term(SrcC, ST), show_term_q(BT, BS), show_term_q(ST, SS),
                format(string(M), "~s clause ~d: compiled clause is not the cut-free source clause\n  source:   ~s\n  compiled: ~s",
                       [KS, I, BS, SS]),
                pfail(M) )).

rename_head(Renamed, clause(H, B, NV), clause(H1, B, NV)) :-
    if_commit(( H = comp(Nm, As), memberchk(Nm-Nm1, Renamed) ), H1 = comp(Nm1, As), H1 = H).

by_key(Cls, Map) :-
    map_empty(E),
    foldl(by_key_add, Cls, E, Map).

by_key_add(C, M0, M) :-
    C = clause(H, _, _),
    goal_key(H, MK),
    if_commit(MK = just(K),
              ( map_find(M0, K, [], Old), conc(Old, [C], New), map_put(K, New, M0, M) ),
              M = M0).

coverage(ByKey, K-Cs) :-
    show_key(K, KS),
    map_get(ByKey, K, MJ),
    if_commit(MJ = just(Js), true,
              ( format(string(M), "unjustified predicate in the converted program: ~s", [KS]), pfail(M) )),
    length(Cs, LC),
    length(Js, LJ),
    format(string(M1), "~s: ~d clauses, ~d justified", [KS, LC, LJ]),
    ensure(LC =:= LJ, M1),
    maplist(same_clause(KS), Cs, Js).

same_clause(KS, C, J) :-
    clause_term(C, CT),
    clause_term(J, JT),
    empty_state(0, St),
    if_commit(variant_t(St, CT, JT, true), true,
              ( show_term_q(CT, CS), show_term_q(JT, JS),
                format(string(M), "~s: a clause differs from its justification:\n  program: ~s\n  proof:   ~s", [KS, CS, JS]),
                pfail(M) )).

in_conv(ConvKeys, K) :-
    show_key(K, KS),
    format(string(M), "justified but missing from the program: ~s", [KS]),
    ensure(ord_memberchk(K, ConvKeys), M).

% ---------------------------------------------------------------------------
% Rule CUT, re-derived: the cut-free form of the source program.
% Predicates whose cuts cannot be eliminated are left out.

base_program(Src, Base) :-
    program_clauses(Src, KCs),
    findall(K-Cs1, ( member(K-Cs, KCs), catch(cut_free(K, Cs, Cs1), proof_fail(_), fail) ), Pairs),
    pairs_keys(Pairs, Order),
    map_from_pairs(Pairs, Preds),
    prog_directives(Src, Ds),
    with_prelude(prog(Preds, Order, Ds), WL),
    prog_preds(Src, SP),
    map_member(SP, member/2, UM),
    drop_member(UM, WL, Base).

%  goal_cut(+Term): a cut in a goal position.
goal_cut(T) :-
    if_commit(T == atom('!'), true,
    if_commit(( T = comp(Op, [A, B]), memberchk(Op, [',', ';', '->', '*->', forall]) ),
              if_commit(goal_cut(A), true, goal_cut(B)),
    if_commit(T = comp(if_commit, As), once_det(( member(X, As), goal_cut(X) )),
    if_commit(( T = comp(F, [A]), memberchk(F, ['\\+', not, once, once_det, ignore, call]) ), goal_cut(A),
    if_commit(T = comp(findall, [_, G, _]), goal_cut(G),
    if_commit(T = comp(aggregate_all, [_, G, _]), goal_cut(G),
              fail)))))).

cut_free(F/N, Cls, Out) :-
    if_commit(( member(clause(_, B, _), Cls), goal_cut(B) ),
              cut_free_(F/N, Cls, Out),
              Out = Cls).

cut_free_(F/N, Cls, Out) :-
    maplist(local_clause_p, Cls, Cls1),
    show_key(F/N, KS),
    format(string(M), "~s: a cut that is neither top-level nor local", [KS]),
    maplist(only_top_cuts(M), Cls1),
    if_commit(( member(clause(_, B1, _), Cls1), conj_list(B1, Gs1), memberchk(atom('!'), Gs1) ),
              ( N1 is N - 1,
                findall(var(I, Nm), ( between(0, N1, I), format(atom(Nm), "A~d", [I]) ), Args),
                if_commit(N =:= 0, HeadT = atom(F), HeadT = comp(F, Args)),
                cf_go(Cls1, N, Args, Body),
                max_var_id(comp(c, [HeadT, Body]), MV),
                NV is MV + 1,
                Out = [clause(HeadT, Body, NV)] ),
              Out = Cls1).

local_clause_p(clause(H, B, NV), clause(H, B1, NV)) :-
    local_p(B, B1).

only_top_cuts(M, clause(_, B, _)) :-
    conj_list(B, Gs),
    ensure(no_inner_cut(Gs), M).

no_inner_cut(Gs) :-
    if_commit(( member(G, Gs), G \== atom('!'), goal_cut(G) ), fail, true).

cf_go([], _, _, atom(fail)).
cf_go([clause(H0, B0, NV)|Rest], Off, Args, T) :-
    rename_term(Off, H0, H),
    rename_term(Off, B0, B),
    Off1 is Off + NV,
    goal_args(H, HAs),
    maplist(eq_goal, Args, HAs, Match),
    conj_list(B, Gs),
    split_at_cut(Gs, MS),
    cf_go(Rest, Off1, Args, RestT),
    cf_alt(MS, Match, Gs, RestT, T).

cf_alt(just(Before-After), Match, _, RestT, comp(if_commit, [C, CR, RestT])) :-
    conc(Match, Before, MB),
    mk_conj(MB, C),
    commit_rest(After, CR).
cf_alt(nothing, Match, Gs, RestT, T) :-
    conc(Match, Gs, MGs),
    mk_conj(MGs, X),
    disj_alt(X, RestT, T).

commit_rest(Gs, T) :-
    split_at_cut(Gs, MS),
    commit_rest_(MS, Gs, T).

commit_rest_(just(Before-After), _, comp(if_commit, [C, CR, atom(fail)])) :-
    mk_conj(Before, C),
    commit_rest(After, CR).
commit_rest_(nothing, Gs, T) :-
    mk_conj(Gs, T).

%  cuts local to opaque goals commit inside them
local_p(T, T1) :-
    if_commit(T = comp(',', [A, B]), ( local_p(A, A1), local_p(B, B1), T1 = comp(',', [A1, B1]) ),
    if_commit(T = comp(';', [comp('->', [C, X]), E]),
              ( barrier_p(C, C1), local_p(X, X1), local_p(E, E1), T1 = comp(';', [comp('->', [C1, X1]), E1]) ),
    if_commit(T = comp(';', [A, B]), ( local_p(A, A1), local_p(B, B1), T1 = comp(';', [A1, B1]) ),
    if_commit(T = comp('->', [C, X]), ( barrier_p(C, C1), local_p(X, X1), T1 = comp('->', [C1, X1]) ),
    if_commit(( T = comp(G, [X]), memberchk(G, ['\\+', not, once, ignore, call]) ),
              ( barrier_p(X, X1), T1 = comp(G, [X1]) ),
    if_commit(T = comp(findall, [X, G, L]), ( barrier_p(G, G1), T1 = comp(findall, [X, G1, L]) ),
    if_commit(T = comp(forall, [C, A]), ( barrier_p(C, C1), barrier_p(A, A1), T1 = comp(forall, [C1, A1]) ),
    if_commit(T = comp(aggregate_all, [S, G, R]), ( barrier_p(G, G1), T1 = comp(aggregate_all, [S, G1, R]) ),
              T1 = T)))))))).

barrier_p(G, G2) :-
    local_p(G, G1),
    conj_list(G1, Gs),
    if_commit(memberchk(atom('!'), Gs), commit_rest(Gs, G2), G2 = G1).

% ---------------------------------------------------------------------------
% Rule SPEC, re-derived: a closure-specialised copy of a predicate.

add_spec(S, P-Table, P1-Table1) :-
    if_commit(S = comp(closure_spec, [NewT, OldT, int(Pos), Clo]), true, pfail("bad closure_spec step")),
    term_key_or(NewT, "closure_spec: bad new key", NewName/NewArity),
    term_key_or(OldT, "closure_spec: bad old key", F/N),
    show_key(F/N, KS),
    prog_preds(P, Preds),
    map_get(Preds, F/N, MO),
    if_commit(MO = just(OldCls), true, ( format(string(M0), "closure_spec: unknown ~s", [KS]), pfail(M0) )),
    term_vars_ordered(Clo, FreeVs),
    ensure(is_callable_t(Clo, true), "closure_spec: closure is not callable"),
    length(FreeVs, NF),
    ensure(NewArity =:= NF + N - 1, "closure_spec: wrong arity"),
    maplist(spec_clause_p(NewName, Pos, Clo, KS), OldCls, NewCls),
    show_answer_term(comp(k, [atom(F), int(N), int(Pos), Clo]), Canon),
    P = prog(Preds0, Order, Ds),
    map_put(NewName/NewArity, NewCls, Preds0, Preds1),
    conc(Order, [NewName/NewArity], Order1),
    P1 = prog(Preds1, Order1, Ds),
    map_put(Canon, NewName, Table, Table1).

spec_clause_p(NewName, Pos, Clo, KS, clause(H, B, NV), clause(H1, B1, NV1)) :-
    goal_args(H, HAs),
    P1 is Pos + 1,
    nth_det(P1, HAs, MG),
    maybe_default(MG, atom('[]'), G),
    rename_term(NV, Clo, CloR),
    format(string(M), "closure_spec: argument ~d of ~s is not a variable", [P1, KS]),
    ensure(G = var(_, _), M),
    term_vars_ordered(CloR, CVs),
    other_args(HAs, Pos, Others),
    maplist(sub_p(G, CloR), Others, Others1),
    conc(CVs, Others1, NewArgs),
    H1 = comp(NewName, NewArgs),
    sub_p(G, CloR, B, B1),
    max_var_id(comp(c, [H1, B1]), MV),
    NV1 is MV + 1.

sub_p(G, CloR, T, T1) :-
    if_commit(teq(T, G), T1 = CloR,
    if_commit(( T = comp(call, [X|Extra]), teq(X, G), add_args(CloR, Extra, just(T2)) ), T1 = T2,
    if_commit(T = comp(Fn, As), ( maplist(sub_p(G, CloR), As, As1), T1 = comp(Fn, As1) ),
              T1 = T))).

%  clause_matches(+Table, +Base, +Compiled): equal up to variable renaming,
%  call(G, X...) with a known G read as G(X...), and closure calls replaced
%  by their specialised copies.
clause_matches(Table, clause(H1, B1, _), clause(H2, B2, _)) :-
    map_empty(E),
    m_term(H1, H2, E-E, M),
    M = just(Bij),
    m_goal(Table, B1, B2, Bij, R),
    R = just(_).

m_term(A, B, Bij, M) :-
    if_commit(( A = var(I, _), B = var(J, _) ),
              m_vars(I, J, Bij, M),
    if_commit(( A = comp(F, As), B = comp(G, Bs), F == G, same_length(As, Bs) ),
              m_args(As, Bs, Bij, M),
    if_commit(either_var(A, B),
              M = nothing,
              if_commit(teq(A, B), M = just(Bij), M = nothing)))).

either_var(A, B) :-
    if_commit(is_var_t(A, true), true, is_var_t(B, true)).

m_vars(I, J, M1-M2, M) :-
    map_get(M1, I, L1),
    map_get(M2, J, L2),
    if_commit(( L1 == nothing, L2 == nothing ),
              ( map_put(I, J, M1, N1), map_put(J, I, M2, N2), M = just(N1-N2) ),
              if_commit(( L1 = just(J1), L2 = just(I1), J1 =:= J, I1 =:= I ),
                        M = just(M1-M2),
                        M = nothing)).

m_args([], [], Bij, just(Bij)).
m_args([X|Xs], [Y|Ys], Bij, M) :-
    m_term(X, Y, Bij, M1),
    m_then(M1, m_args(Xs, Ys), M).

m_then(nothing, _, nothing).
m_then(just(B), K, M) :-
    call(K, B, M).

m_goal(Table, A, B, Bij, M) :-
    if_commit(( A = comp(call, [G|Extra]), is_var_t(G, false), add_args(G, Extra, just(A1)) ),
              m_goal(Table, A1, B, Bij, M),
    if_commit(( A = comp(F, [X, Y]), B = comp(F, [U, V]), memberchk(F, [',', ';', '->', '*->']) ),
              ( m_goal(Table, X, U, Bij, M1), m_then(M1, m_goal(Table, Y, V), M) ),
    if_commit(( A = comp(if_commit, [X, Y, Z]), B = comp(if_commit, [U, V, W]) ),
              ( m_goal(Table, X, U, Bij, M1), m_then(M1, m_goal(Table, Y, V), M2),
                m_then(M2, m_goal(Table, Z, W), M) ),
    if_commit(( A = comp(F, [X]), B = comp(F, [U]), memberchk(F, ['\\+', not, once, once_det, ignore]) ),
              m_goal(Table, X, U, Bij, M),
    if_commit(( A = comp(findall, [T, X, L]), B = comp(findall, [T1, U, L1]) ),
              ( m_term(T, T1, Bij, M1), m_then(M1, m_goal(Table, X, U), M2), m_then(M2, m_term(L, L1), M) ),
              ( m_term(A, B, Bij, M0),
                if_commit(M0 = just(_), M = M0, spec_call(Table, A, B, Bij, M)) )))))).

spec_call(Table, A, B, Bij, M) :-
    goal_key(A, MK),
    if_commit(( MK = just(F/N), B = comp(Name, Args1) ),
              ( goal_args(A, As),
                numbered_list(As, 0, NAs),
                if_commit(( member(Pos-Clo, NAs), is_var_t(Clo, false), is_callable_t(Clo, true),
                            show_answer_term(comp(k, [atom(F), int(N), int(Pos), Clo]), Canon),
                            map_get(Table, Canon, just(Name0)), Name0 == Name ),
                          ( term_vars_ordered(Clo, CVs), other_args(As, Pos, Others),
                            conc(CVs, Others, Expected),
                            list_t(Expected, EL), list_t(Args1, AL),
                            m_term(EL, AL, Bij, M) ),
                          M = nothing) ),
              M = nothing).
