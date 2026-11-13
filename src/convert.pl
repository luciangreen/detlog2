/*  convert.pl - the Detlog converter: Prolog with choicepoints and cuts
    becomes deterministic code that combines alternatives with splices,
    together with a proof of every rewrite.

    After cut elimination (cut_elim.pl) and closure specialisation, every
    predicate p/n becomes a deterministic predicate p__cp(A1, ..., An, Packet)
    which succeeds exactly once.  Packet is the answer packet of the
    original predicate: in Prolog order, one row [A1', ..., An'] per answer
    (duplicates included) and one item out(Text) for each piece of output,
    placed where Prolog would write it.

    Every piece of generated code is justified by a proof step: a
    derivation node d(Rule, Source, Env, Out, Generated, Subderivations).
    proof.pl checks the steps independently of this module.

    Options: copts(SpliceEarly, External, Roots), External an ordset of
    keys, Roots nothing or just(Keys).  The result is
    cres(Program, Events, ProofSteps).  Generation errors are thrown as
    gfail(Message) and returned as left(Message).
*/

default_convert_options(copts(true, [], nothing)).

co_splice(copts(S, _, _), S).
co_external(copts(_, E, _), E).
co_roots(copts(_, _, R), R).

cp_name(F, CF) :-
    atom_concat(F, '__cp', CF).

key_t(F/N, comp('/', [atom(F), int(N)])).

%  add_query_clause(+Goal, +Vars, +NVars, +Program, -Program, -Key): a
%  clause '$query'(V1, ..., Vk) :- Goal, converted like any other predicate.
add_query_clause(Goal, Vars, NV, prog(Preds, Order, Ds), prog(Preds1, Order1, Ds), Key) :-
    length(Vars, K),
    Key = '$query'/K,
    if_commit(Vars == [], H = atom('$query'), H = comp('$query', Vars)),
    map_put(Key, [clause(H, Goal, NV)], Preds, Preds1),
    exclude(==(Key), Order, O1),
    conc(O1, [Key], Order1).

%  prepare_program(+External, +Program, -Either): cut elimination, library
%  predicates, closure specialisation and removal of unused library code.
prepare_program(External, P0, E) :-
    eliminate_cuts(P0, CE),
    prepare_cuts(CE, External, P0, E).

prepare_cuts(left(Bad), _, _, left(M)) :-
    maplist(show_cut_event, Bad, Ss),
    atomic_list_concat(Ss, '\n  ', A),
    format(string(M), "cannot convert these cuts:\n  ~w", [A]).
prepare_cuts(right(P1-CutEvents), External, P0, E) :-
    with_prelude(P1, P2),
    specialise_meta(P2, SE),
    prepare_meta(SE, External, P0, CutEvents, E).

prepare_meta(left(M), _, _, _, left(M)).
prepare_meta(right(P3-MetaEvents-MetaSteps), _, P0, CutEvents, right(P4-Events-Steps)) :-
    prog_order(P0, Own),
    restrict_to(Own, P3, P4),
    cut_steps(P0, CutSteps),
    maplist(show_cut_event, CutEvents, CEs),
    conc(CEs, MetaEvents, Events),
    conc(CutSteps, MetaSteps, Steps).

cut_steps(P0, Steps) :-
    prog_order(P0, Order),
    prog_preds(P0, Preds),
    findall(comp(cut_elim, [KT]),
            ( member(K, Order), map_find(Preds, K, [], Cs),
              once_det(( member(clause(_, B, _), Cs), has_cut_(B) )),
              key_t(K, KT) ),
            Steps).

convert_program(Opts, P0, E) :-
    co_roots(Opts, Roots),
    roots_restrict(Roots, P0, P0a),
    co_external(Opts, Ext),
    prepare_program(Ext, P0a, PE),
    convert_prepared(PE, Opts, P0a, E).

roots_restrict(nothing, P, P).
roots_restrict(just(Roots), P0, P) :-
    restrict_to(Roots, P0, P).

convert_prepared(left(M), _, _, left(M)).
convert_prepared(right(P1-PrepEvents-PrepSteps), Opts, P0a, E) :-
    % member/2 that the program does not define itself is the Detlog
    % runtime's member_cp/2 packet, not a library predicate.
    prog_preds(P0a, Preds0),
    map_member(Preds0, member/2, UserMember),
    drop_member(UserMember, P1, P),
    co_external(Opts, Ext),
    prog_order(P, Order),
    sort(Order, OS),
    ord_union(OS, Ext, Defined),
    effectful_preds(P, Eff0),
    ord_union(Eff0, Ext, Eff),
    Env = env(Defined, Eff, Opts),
    program_clauses(P, KCs),
    catch(( foldl(convert_kc(Env, Ext), KCs, []-[]-[], Cls-Evs-Steps),
            program_from_clauses(Cls, CP),
            conc(PrepEvents, Evs, AllEvs),
            conc(PrepSteps, Steps, AllSteps),
            E = right(cres(CP, AllEvs, AllSteps)) ),
          gfail(M),
          E = left(M)).

drop_member(true, P, P).
drop_member(false, prog(Preds, Order, Ds), prog(Preds1, Order1, Ds)) :-
    del_assoc_det(member/2, Preds, Preds1),
    exclude(==(member/2), Order, Order1).

del_assoc_det(K, M0, M) :-
    if_commit(del_assoc(K, M0, _, M1), M = M1, M = M0).

convert_kc(Env, Ext, K-Cls, Cs0-E0-S0, Cs-E-S) :-
    if_commit(ord_memberchk(K, Ext),
              ( Cs = Cs0, E = E0, S = S0 ),
              ( convert_pred(Env, K, Cls, Cs1, E1, S1),
                conc(Cs0, Cs1, Cs), conc(E0, E1, E), conc(S0, S1, S) )).

gfail_throw(M) :-
    throw(gfail(M)).

% ---------------------------------------------------------------------------
% Helpers for generated code

nil_t(atom('[]')).

list_t(Xs, T) :-
    mk_list(Xs, atom('[]'), T).

eq_t(A, B, comp('=', [A, B])).

if_commit_t(C, T, E, comp(if_commit, [C, T, E])).

%  A derivation node: d(Rule, Source, Env, Out, Generated, Subderivations).
dnode(R, Src, Env, Out, Gen, Subs, comp(d, [atom(R), Src, Env, Out, GL, SL])) :-
    list_t(Gen, GL),
    list_t(Subs, SL).

gen_of(D, Gs) :-
    if_commit(D = comp(d, [_, _, _, _, GL, _]),
              ( static_list(GL, M), maybe_default(M, [], Gs) ),
              Gs = []).

static_list(atom(A), M) :-
    if_commit(A == '[]', M = just([]), M = nothing).
static_list(comp(F, As), M) :-
    if_commit(( F == '.', As = [H, T] ),
              ( static_list(T, MT), maybe_cons(MT, H, M) ),
              M = nothing).
static_list(var(_, _), nothing).
static_list(int(_), nothing).
static_list(flt(_), nothing).

%  A clause whose variables are counted from the term itself.
mk_clause(H, B, clause(H, B, NV)) :-
    max_var_id(comp(c, [H, B]), M),
    NV is M + 1.

clause_t(clause(H, B, _), comp(':-', [H, B])).

head_vars_a(N, Args) :-
    N1 is N - 1,
    findall(var(I, Name), ( between(0, N1, I), I1 is I + 1, format(atom(Name), "A~d", [I1]) ), Args).

% ---------------------------------------------------------------------------
% Predicates

convert_pred(Env, F/N, Cls, Cs, Evs, Steps) :-
    if_commit(( Cls \== [], all_facts(Cls) ),
              facts_pred(F/N, Cls, Cs, Evs, Steps),
              clauses_pred(Env, F/N, Cls, Cs, Evs, Steps)).

all_facts([]).
all_facts([clause(_, B, _)|Cs]) :-
    B == atom(true),
    all_facts(Cs).

facts_pred(F/N, Cls, [Cl], [Ev], [comp(facts_packet, [KT, CT])]) :-
    head_vars_a(N, Args),
    Off0 is N + 2,
    foldl(fact_row, Cls, []-Off0, Rows-_),
    PV = var(N, 'P'),
    N1 is N + 1,
    RV = var(N1, 'Rows'),
    cp_name(F, CF),
    conc(Args, [RV], HArgs),
    H = comp(CF, HArgs),
    list_t(Rows, RowsT),
    list_t(Args, ArgsT),
    mk_conj([comp(member_cp, [PV, RowsT]), comp(cp_filter, [PV, ArgsT, RV])], B),
    mk_clause(H, B, Cl),
    length(Cls, K),
    format(string(Ev), "facts_to_member_cp(~w/~d, ~d facts)", [F, N, K]),
    key_t(F/N, KT),
    clause_t(Cl, CT).

fact_row(clause(H, _, NV), Acc-Off, Acc1-Off1) :-
    rename_term(Off, H, H1),
    goal_args(H1, As),
    list_t(As, Row),
    conc(Acc, [Row], Acc1),
    Off1 is Off + NV.

clauses_pred(Env, F/N, Cls, [Top|PCs], [Ev|PEs], [Step|PSs]) :-
    numbered_list(Cls, 1, NCls),
    foldl(convert_clause_acc(Env, F/N), NCls, []-[]-[], PCs-PEs-PSs),
    head_vars_a(N, Args),
    length(Cls, L),
    findall(var(V, Name), ( between(1, L, I), V is N + I, format(atom(Name), "R~d", [I]) ), RowVars),
    RI is N + L + 1,
    RV = var(RI, 'Rows'),
    cp_name(F, CF),
    list_t(Args, ArgsT),
    findall(comp(CN, [ArgsT, R]),
            ( nth1(I, RowVars, R), format(atom(CN), "~w_c~d", [CF, I]) ),
            Calls),
    pred_body(Calls, RowVars, RV, B),
    conc(Args, [RV], HArgs),
    mk_clause(comp(CF, HArgs), B, Top),
    format(string(Ev), "predicate_to_packet(~w/~d, ~d clauses)", [F, N, L]),
    key_t(F/N, KT),
    clause_t(Top, TT),
    Step = comp(pred_packet, [KT, int(L), TT]).

pred_body(Calls, RowVars, RV, B) :-
    if_commit(Calls == [],
              eq_t(RV, atom('[]'), B),
              if_commit(Calls = [comp(G, [A, _])],
                        B = comp(G, [A, RV]),
                        ( list_t(RowVars, RVL),
                          conc(Calls, [comp(rows_concat, [RVL, RV])], Gs),
                          mk_conj(Gs, B) ))).

convert_clause_acc(Env, Key, I-C, Cs0-E0-S0, Cs-E-S) :-
    convert_clause(Env, Key, I, C, Cs1, E1, S1),
    conc(Cs0, Cs1, Cs),
    conc(E0, E1, E),
    conc(S0, S1, S).

%  Generator state: gs(Next, Aux, Count, Events, Base), Aux and Events
%  reversed.
convert_clause(Env, F/N, I, clause(H, B, NV), [Cl|AuxCls], Evs, [Step|AuxSteps]) :-
    term_vars_ordered(comp(c, [H, B]), Vs),
    list_t(Vs, EnvT),
    max_var_id(comp(c, [H, B]), M),
    Start is M + 1,
    cp_name(F, CF),
    format(atom(Name), "~w_c~d", [CF, I]),
    goal_args(H, HAs),
    list_t(HAs, HeadArgs),
    format(atom(Base), "~w_c~d", [F, I]),
    S0 = gs(Start, [], 0, [], Base),
    fresh_g('Args', ArgsV, S0, S1),
    fresh_g('Rows', RowsV, S1, S2),
    clause_body(B, Env, EnvT, HeadArgs, RowsV, Body, Deriv, S2, S3),
    mk_conj(Body, BodyC),
    mk_clause(comp(Name, [ArgsV, RowsV]),
              comp(if_commit, [comp(copy_term, [ArgsV, HeadArgs]), BodyC, comp('=', [RowsV, atom('[]')])]),
              Cl),
    S3 = gs(_, AuxR, _, EvsR, _),
    rev(AuxR, Auxes),
    rev(EvsR, Evs),
    aux_clauses(Auxes, AuxCls),
    maplist(aux_step(EnvT), Auxes, AuxSteps),
    key_t(F/N, KT),
    clause_t(clause(H, B, NV), ST),
    clause_t(Cl, CT),
    Step = comp(clause_packet, [KT, int(I), ST, CT, Deriv]).

clause_body(B, Env, EnvT, HeadArgs, RowsV, Body, Deriv, S0, S) :-
    if_commit(B == atom(true),
              ( list_t([HeadArgs], HL), Body = [comp('=', [RowsV, HL])], Deriv = atom(none), S = S0 ),
              ( fresh_g('Env', EnvRows, S0, S1),
                env_code(Env, B, EnvT, EnvRows, D, S1, S),
                gen_of(D, G),
                conc(G, [comp(splice_extend, [EnvRows, HeadArgs, EnvT, RowsV])], Body),
                Deriv = D )).

aux_clauses([], []).
aux_clauses([C1-C2-_|As], [C1, C2|Cs]) :-
    aux_clauses(As, Cs).

aux_step(EnvT, C1-C2-D, comp(aux, [atom(AN), EnvT, L, D])) :-
    C1 = clause(H, _, _),
    goal_key(H, MK),
    aux_name_of(MK, AN),
    clause_t(C1, T1),
    clause_t(C2, T2),
    list_t([T1, T2], L).

aux_name_of(just(F/_), F).
aux_name_of(nothing, '').

fresh_g(Name, var(I, Name), gs(I, A, C, E, B), gs(I1, A, C, E, B)) :-
    I1 is I + 1.

aux_name_g(Name, gs(I, A, C, E, B), gs(I, A, C1, E, B)) :-
    C1 is C + 1,
    cp_name(B, CB),
    format(atom(Name), "~w_~d", [CB, C1]).

emit_aux_g(C1, C2, D, gs(I, A, C, E, B), gs(I, [C1-C2-D|A], C, E, B)).

event_g(Ev, gs(I, A, C, E, B), gs(I, A, C, [Ev|E], B)).

% ---------------------------------------------------------------------------
% Goals.  Each returns a derivation node whose generated code computes Out
% from the single environment row Env (the clause variables).

env_code(Env, G, EnvT, Out, D, S0, S) :-
    goal_shape_c(G, Shape),
    env_code_(Shape, Env, G, EnvT, Out, D, S0, S).

goal_shape_c(G, Shape) :-
    if_commit(G == atom(true), Shape = true,
    if_commit(memberchk(G, [atom(fail), atom(false)]), Shape = fail,
    if_commit(G = comp(',', _), Shape = seq,
    if_commit(G = comp(';', [comp('->', [_, _]), _]), Shape = ite,
    if_commit(G = comp(';', [comp('*->', _), _]), Shape = soft,
    if_commit(G = comp('->', [_, _]), Shape = ifthen,
    if_commit(G = comp(if_commit, [_, _, _]), Shape = if_commit,
    if_commit(( G = comp(F1, [_]), memberchk(F1, [once, once_det]) ), Shape = once,
    if_commit(G = comp(ignore, [_]), Shape = ignore,
    if_commit(G = comp(';', [_, _]), Shape = disj,
    if_commit(( G = comp(F2, [_]), memberchk(F2, ['\\+', not]) ), Shape = neg,
    if_commit(G = comp(forall, [_, _]), Shape = forall,
    if_commit(G = comp(findall, [_, _, _]), Shape = findall,
    if_commit(G = comp(aggregate_all, [atom(count), _, _]), Shape = count,
    if_commit(G = comp(aggregate_all, [comp(bag, [_]), _, _]), Shape = bag,
    if_commit(G = comp(decision, [_, _]), Shape = decision,
    if_commit(G = comp(call, [_|_]), Shape = call,
    if_commit(G = var(_, _), Shape = var,
              Shape = atomic)))))))))))))))))).

env_code_(true, _, G, EnvT, Out, D, S, S) :-
    list_t([EnvT], L),
    dnode(true, G, EnvT, Out, [comp('=', [Out, L])], [], D).
env_code_(fail, _, G, EnvT, Out, D, S, S) :-
    dnode(fail, G, EnvT, Out, [comp('=', [Out, atom('[]')])], [], D).
env_code_(seq, Env, G, EnvT, Out, D, S0, S) :-
    env_seq(Env, G, EnvT, Out, D, S0, S).
env_code_(ite, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [comp(_, [C, T]), E]),
    commit_code(Env, G, C, T, E, EnvT, Out, D, S0, S).
env_code_(soft, _, _, _, _, _, _, _) :-
    gfail_throw("soft cut (*->) cannot be converted").
env_code_(ifthen, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [C, T]),
    commit_code(Env, G, C, T, atom(fail), EnvT, Out, D, S0, S).
env_code_(if_commit, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [C, T, E]),
    commit_code(Env, G, C, T, E, EnvT, Out, D, S0, S).
env_code_(once, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [X]),
    commit_code(Env, G, X, atom(true), atom(fail), EnvT, Out, D, S0, S).
env_code_(ignore, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [X]),
    commit_code(Env, G, X, atom(true), atom(true), EnvT, Out, D, S0, S).
env_code_(disj, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [A, B]),
    fresh_g('Ra', Ra, S0, S1),
    fresh_g('Rb', Rb, S1, S2),
    list_t([EnvT], Rin),
    rows_code(Env, A, Rin, EnvT, Ra, DA, S2, S3),
    rows_code(Env, B, Rin, EnvT, Rb, DB, S3, S4),
    event_g("disjunction_to_rows_concat", S4, S),
    gen_of(DA, GA),
    gen_of(DB, GB),
    list_t([Ra, Rb], RL),
    concat_lists([GA, GB, [comp(rows_concat, [RL, Out])]], Gen),
    dnode(disj, G, EnvT, Out, Gen, [DA, DB], D).
env_code_(neg, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [X]),
    neg_code(Env, G, X, EnvT, Out, D, S0, S).
env_code_(forall, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [C, A]),
    rewrite_to(Env, G, comp('\\+', [comp(',', [C, comp('\\+', [A])])]), EnvT, Out, D, S0, S).
env_code_(findall, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [T, X, L]),
    fresh_g('Found', Rg, S0, S1),
    fresh_g('Outs', Outs, S1, S2),
    fresh_g('Rows0', Rows0, S2, S3),
    fresh_g('L', Ls, S3, S4),
    list_t([EnvT], Rin),
    rows_code(Env, X, Rin, EnvT, Rg, DX, S4, S5),
    event_g("findall_to_packet", S5, S),
    gen_of(DX, GX),
    list_t([EnvT], EL),
    list_t([Outs, EL], OEL),
    conc(GX, [ comp(packet_split, [Rg, Outs, Rows0]),
               comp(splice_extend, [Rows0, T, EnvT, Ls]),
               comp(if_commit, [comp('=', [L, Ls]), comp(rows_concat, [OEL, Out]), comp('=', [Out, Outs])]) ],
         Gen),
    dnode(findall, G, EnvT, Out, Gen, [DX], D).
env_code_(count, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [_, X, R]),
    fresh_g('Found', Rg, S0, S1),
    fresh_g('Outs', Outs, S1, S2),
    fresh_g('Rows0', Rows0, S2, S3),
    fresh_g('Count', Cnt, S3, S4),
    list_t([EnvT], Rin),
    rows_code(Env, X, Rin, EnvT, Rg, DX, S4, S),
    gen_of(DX, GX),
    list_t([EnvT], EL),
    list_t([Outs, EL], OEL),
    conc(GX, [ comp(packet_split, [Rg, Outs, Rows0]),
               comp(length_det, [Rows0, Cnt]),
               comp(if_commit, [comp('=', [R, Cnt]), comp(rows_concat, [OEL, Out]), comp('=', [Out, Outs])]) ],
         Gen),
    dnode(count, G, EnvT, Out, Gen, [DX], D).
env_code_(bag, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [comp(_, [T]), X, R]),
    rewrite_to(Env, G, comp(findall, [T, X, R]), EnvT, Out, D, S0, S).
env_code_(decision, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [Cases, Def]),
    static_list(Cases, M),
    if_commit(( M = just(Cs), all_pairs(Cs) ),
              ( rev(Cs, RCs), foldl(decision_fold, RCs, Def, G1),
                rewrite_to(Env, G, G1, EnvT, Out, D, S0, S) ),
              gfail_throw("decision/2 needs a literal list of Condition-Goal pairs")).
env_code_(call, Env, G, EnvT, Out, D, S0, S) :-
    G = comp(_, [X|Extra]),
    if_commit(X = var(_, _),
              ( length(Extra, K), N is K + 1,
                format(string(M), "call/~d on a variable goal cannot be converted statically", [N]),
                gfail_throw(M) ),
              ( add_args(X, Extra, MG),
                if_commit(MG = just(G1),
                          rewrite_to(Env, G, G1, EnvT, Out, D, S0, S),
                          gfail_throw("call/N: not callable")) )).
env_code_(var, _, _, _, _, _, _, _) :-
    gfail_throw("a variable goal cannot be converted statically").
env_code_(atomic, Env, G, EnvT, Out, D, S0, S) :-
    atomic_goal(Env, G, EnvT, Out, D, S0, S).

all_pairs([]).
all_pairs([C|Cs]) :-
    C = comp('-', [_, _]),
    all_pairs(Cs).

decision_fold(C, E, comp(if_commit, [CC, BB, E])) :-
    C = comp('-', [CC, BB]).

rewrite_to(Env, G, G1, EnvT, Out, D, S0, S) :-
    env_code(Env, G1, EnvT, Out, D1, S0, S),
    gen_of(D1, Gen),
    dnode(rewrite, G, EnvT, Out, Gen, [D1], D).

commit_code(Env, Src, C, T, E, EnvT, Out, D, S0, S) :-
    if_commit(det_builtin_conj(Env, C),
              ( env_code(Env, T, EnvT, Out, DT, S0, S1),
                env_code(Env, E, EnvT, Out, DE, S1, S),
                gen_of(DT, GT), mk_conj(GT, CT),
                gen_of(DE, GE), mk_conj(GE, CE),
                dnode(ite_det, Src, EnvT, Out, [comp(if_commit, [C, CT, CE])], [DT, DE], D) ),
              ( fresh_g('Cond', Rc, S0, S1),
                fresh_g('Pre', Pre, S1, S2),
                fresh_g('Res', Res, S2, S3),
                fresh_g('First', FirstV, S3, S4),
                fresh_g('OutT', Ot, S4, S5),
                fresh_g('OutE', Oe, S5, S6),
                list_t([EnvT], Rin),
                rows_code(Env, C, Rin, EnvT, Rc, DC, S6, S7),
                list_t([FirstV], FL),
                rows_code(Env, T, FL, EnvT, Ot, DT, S7, S8),
                env_code(Env, E, EnvT, Oe, DE, S8, S9),
                event_g("if_then_else_to_if_commit", S9, S),
                gen_of(DC, GC), gen_of(DT, GT), gen_of(DE, GE),
                list_t([Pre, Oe], PreOe),
                list_t([Pre, Ot], PreOt),
                conc(GE, [comp(rows_concat, [PreOe, Out])], ElseGs),
                mk_conj(ElseGs, ElseC),
                concat_lists([[comp('=', [Res, comp(first, [FirstV])])], GT,
                               [comp(rows_concat, [PreOt, Out])]], ThenGs),
                mk_conj(ThenGs, ThenC),
                conc(GC, [ comp(packet_first, [Rc, Pre, Res]),
                           comp(if_commit, [comp('=', [Res, atom(none)]), ElseC, ThenC]) ], Gen),
                dnode(ite, Src, EnvT, Out, Gen, [DC, DT, DE], D) )).

neg_code(Env, G, X, EnvT, Out, D, S0, S) :-
    list_t([EnvT], EL),
    if_commit(det_builtin_conj(Env, X),
              ( S = S0,
                dnode(neg_det, G, EnvT, Out,
                      [comp(if_commit, [X, comp('=', [Out, atom('[]')]), comp('=', [Out, EL])])], [], D) ),
              ( fresh_g('Found', Rg, S0, S1),
                fresh_g('Pre', Pre, S1, S2),
                fresh_g('Res', Res, S2, S3),
                rows_code(Env, X, EL, EnvT, Rg, DX, S3, S),
                gen_of(DX, GX),
                list_t([Pre, EL], PreEL),
                conc(GX, [ comp(packet_first, [Rg, Pre, Res]),
                           comp(if_commit, [comp('=', [Res, atom(none)]),
                                            comp(rows_concat, [PreEL, Out]),
                                            comp('=', [Out, Pre])]) ], Gen),
                dnode(neg, G, EnvT, Out, Gen, [DX], D) )).

%  det_builtin_conj(+Env, +Goal): a conjunction of deterministic,
%  output-free built-ins (it can be a condition of if_commit/3 directly).
det_builtin_conj(Env, G) :-
    conj_list(G, Gs),
    all_det_b(Gs, Env).

all_det_b([], _).
all_det_b([X|Xs], Env) :-
    is_det_b(Env, X),
    all_det_b(Xs, Env).

is_det_b(env(Defined, _, _), X) :-
    goal_key(X, just(F/N)),
    key_atom(F, N, KA),
    is_builtin_key(KA, true),
    if_commit(ord_memberchk(F/N, Defined), fail, true),
    nondet_builtin_keys(ND),
    effect_keys(EK),
    if_commit(memberchk(KA, ['atom_concat/3'|ND]), fail, true),
    if_commit(memberchk(KA, EK), fail, true).

%  A conjunction in one environment.
env_seq(Env, G, EnvT, Out, D, S0, S) :-
    conj_list(G, Gs),
    length(Gs, Len),
    if_commit(Len =:= 0,
              env_code(Env, atom(true), EnvT, Out, D, S0, S),
              if_commit(Len =:= 1,
                        ( Gs = [X], env_code(Env, X, EnvT, Out, D, S0, S) ),
                        env_seq_many(Env, G, Gs, EnvT, Out, D, S0, S))).

env_seq_many(Env, G, Gs, EnvT, Out, D, S0, S) :-
    span_det(Gs, Env, Bs, Rest),
    Env = env(_, _, Opts),
    co_splice(Opts, Early),
    splice_group(Env, Gs, Grp, GRest),
    length(Grp, GLen),
    if_commit(Bs \== [],
              ( mk_conj(Rest, RC),
                env_seq(Env, RC, EnvT, Out, DR, S0, S),
                mk_conj(Bs, BC),
                gen_of(DR, GR), mk_conj(GR, GRC),
                dnode(det_prefix, G, EnvT, Out,
                      [comp(if_commit, [BC, GRC, comp('=', [Out, atom('[]')])])], [DR], D) ),
    if_commit(( Early == true, GLen >= 2 ),
              splice_seq(Env, G, Grp, GRest, EnvT, Out, D, S0, S),
              ( Gs = [X|Rest1],
                fresh_g('R', R1, S0, S1),
                env_code(Env, X, EnvT, R1, D1, S1, S2),
                mk_conj(Rest1, RC1),
                rows_code(Env, RC1, R1, EnvT, Out, DR, S2, S),
                gen_of(D1, G1), gen_of(DR, GR),
                conc(G1, GR, Gen),
                dnode(seq, G, EnvT, Out, Gen, [D1, DR], D) ))).

span_det([], _, [], []).
span_det([X|Xs], Env, Bs, Rest) :-
    if_commit(det_builtin_conj(Env, X),
              ( Bs = [X|Bs1], span_det(Xs, Env, Bs1, Rest) ),
              ( Bs = [], Rest = [X|Xs] )).

splice_seq(Env, G, Grp, Rest, EnvT, Out, D, S0, S) :-
    if_commit(Rest == [],
              ( R = Out, S1 = S0 ),
              fresh_g('Spliced', R, S0, S1)),
    splice_code(Env, Grp, EnvT, R, Chain, DSeq, S1, S2),
    if_commit(Rest == [],
              ( S = S2, dnode(splice, G, EnvT, Out, Chain, [DSeq], D) ),
              ( mk_conj(Rest, RC),
                rows_code(Env, RC, R, EnvT, Out, DRest, S2, S),
                gen_of(DRest, GRest),
                conc(Chain, GRest, Gen),
                dnode(splice, G, EnvT, Out, Gen, [DSeq, DRest], D) )).

%  Code mapping a packet of rows to the packet after Goal: an auxiliary
%  predicate iterates over the packet (first argument [] or [_|_]); output
%  items pass through unchanged.
rows_code(Env, G, Rin, EnvT, Out, D, S0, S) :-
    if_commit(G == atom(true),
              ( S = S0, dnode(rows_true, G, Rin, Out, [comp('=', [Out, Rin])], [], D) ),
              rows_code_aux(Env, G, Rin, EnvT, Out, D, S0, S)).

rows_code_aux(Env, G, Rin, EnvT, Out, D, S0, S) :-
    aux_name_g(Name, S0, S1),
    fresh_g('Row', RowV, S1, S2),
    fresh_g('Rows', RsV, S2, S3),
    fresh_g('Out1', O1, S3, S4),
    fresh_g('Out2', O2, S4, S5),
    fresh_g('Out', OutV, S5, S6),
    fresh_g('Text', Txt, S6, S7),
    env_code(Env, G, EnvT, O1, DG, S7, S8),
    mk_clause(comp(Name, [atom('[]'), atom('[]')]), atom(true), C1),
    gen_of(DG, GG),
    mk_conj([comp(copy_term, [RowV, EnvT])|GG], CopyC),
    list_t([comp(out, [Txt])], OL),
    list_t([O1, O2], O12),
    mk_conj([ comp(if_commit, [comp('=', [RowV, comp(out, [Txt])]), comp('=', [O1, OL]), CopyC]),
              comp(Name, [RsV, O2]),
              comp(rows_concat, [O12, OutV]) ], B2),
    mk_list([RowV], RsV, RowCons),
    mk_clause(comp(Name, [RowCons, OutV]), B2, C2),
    emit_aux_g(C1, C2, DG, S8, S),
    dnode(rows, G, Rin, Out, [comp(Name, [Rin, Out])], [atom(Name)], D).

%  A single goal that is not a control construct.
atomic_goal(Env, G, EnvT, Out, D, S0, S) :-
    goal_key(G, MK),
    if_commit(MK = just(F/N),
              atomic_key(F/N, Env, G, EnvT, Out, D, S0, S),
              ( show_term_q(G, GS), string_concat("not a callable goal: ", GS, M), gfail_throw(M) )).

atomic_key(F/N, Env, G, EnvT, Out, D, S0, S) :-
    Env = env(Defined, _, _),
    key_atom(F, N, KA),
    goal_args(G, As),
    list_t([EnvT], EL),
    nondet_builtin_keys(ND),
    effect_keys(EK),
    control_keys(CK),
    if_commit(ord_memberchk(F/N, Defined),
              ( fresh_g('Packet', Qr, S0, S),
                cp_name(F, CF), conc(As, [Qr], CAs), list_t(As, AL),
                dnode(call, G, EnvT, Out, [comp(CF, CAs), comp(splice_extend, [Qr, EnvT, AL, Out])], [], D) ),
    if_commit(KA == 'member/2',
              ( fresh_g('P', P, S0, S1), fresh_g('PRows', Pr, S1, S2),
                event_g("member_to_member_cp", S2, S),
                As = [X, L], list_t([X], XL),
                dnode(member_cp, G, EnvT, Out,
                      [comp(member_cp, [P, L]), comp(cp_rows, [P, Pr]), comp(splice_extend, [Pr, EnvT, XL, Out])], [], D) ),
    if_commit(KA == 'between/3',
              ( fresh_g('P', P, S0, S1), fresh_g('PRows', Pr, S1, S2),
                event_g("between_to_between_cp", S2, S),
                As = [Lo, Hi, X], list_t([X], XL),
                dnode(between_cp, G, EnvT, Out,
                      [comp(between_cp, [Lo, Hi, P]), comp(cp_rows, [P, Pr]), comp(splice_extend, [Pr, EnvT, XL, Out])], [], D) ),
    if_commit(KA == 'length/2',
              ( S = S0,
                dnode(length_det, G, EnvT, Out,
                      [comp(if_commit, [comp(length_det, As), comp('=', [Out, EL]), comp('=', [Out, atom('[]')])])], [], D) ),
    if_commit(memberchk(KA, ['atom_concat/3'|ND]),
              ( fresh_g('BRows', Br, S0, S), list_t([G], GL),
                dnode(builtin_rows, G, EnvT, Out,
                      [comp(builtin_rows, [G, Br]), comp(splice_extend, [Br, EnvT, GL, Out])], [], D) ),
    if_commit(memberchk(KA, EK),
              ( fresh_g('Text', T, S0, S), list_t([comp(out, [T]), EnvT], OL),
                dnode(effect, G, EnvT, Out, [comp(effect_text, [G, T]), comp('=', [Out, OL])], [], D) ),
    if_commit(is_builtin_key(KA, true),
              ( S = S0,
                dnode(det, G, EnvT, Out,
                      [comp(if_commit, [G, comp('=', [Out, EL]), comp('=', [Out, atom('[]')])])], [], D) ),
    if_commit(memberchk(KA, CK),
              ( format(string(M), "cannot convert control construct ~w/~d", [F, N]), gfail_throw(M) ),
              ( format(string(M), "unknown procedure ~w/~d", [F, N]), gfail_throw(M) ))))))))).

%  A leading run of independent, output-free generators.
splice_group(Env, Gs, Grp, Rest) :-
    splice_group_(Gs, Env, [], [], Grp, Rest).

splice_group_([], _, _, Acc, Grp, []) :-
    rev(Acc, Grp).
splice_group_([G|Gs], Env, Used, Acc, Grp, Rest) :-
    term_vars_ordered(G, Vs),
    var_ids(Vs, Ids),
    if_commit(( is_generator(Env, G), no_shared(Ids, Used) ),
              ( conc(Used, Ids, Used1), splice_group_(Gs, Env, Used1, [G|Acc], Grp, Rest) ),
              ( rev(Acc, Grp), Rest = [G|Gs] )).

no_shared(Ids, Used) :-
    if_commit(( member(I, Ids), memberchk(I, Used) ), fail, true).

is_generator(env(Defined, Eff, _), G) :-
    goal_key(G, just(F/N)),
    if_commit(ord_memberchk(F/N, Defined),
              if_commit(ord_memberchk(F/N, Eff), fail, true),
              memberchk(F/N, [member/2, between/3])).

%  Compute each generator's packet once and splice the packets, guarded by
%  splice_safe/1; the sequential code is the fallback.
splice_code(Env, Grp, EnvT, Out, [Code], DSeq, S0, S) :-
    foldl(splice_part(Env), Grp, []-S0, PartsR-S1),
    rev(PartsR, Parts),
    fresh_g('Combos', Combos, S1, S2),
    parts_pats(Parts, Pats),
    list_t(Pats, PatsT),
    parts_cps(Parts, Cps),
    list_t(Cps, CpsT),
    Final = [comp(splice, [CpsT, Combos]), comp(splice_extend, [Combos, EnvT, PatsT, Out])],
    chain(Parts, Final, Out, Chain),
    maplist(show_source_term, Grp, GSs),
    atomic_list_concat(GSs, ', ', GA),
    format(string(Ev), "splice_early(~w)", [GA]),
    event_g(Ev, S2, S3),
    Env = env(Def, Eff, copts(_, Ext, Roots)),
    mk_conj(Grp, GC),
    env_seq(env(Def, Eff, copts(false, Ext, Roots)), GC, EnvT, Out, DSeq, S3, S),
    mk_conj(Chain, ChainC),
    gen_of(DSeq, GS),
    mk_conj(GS, SeqC),
    Code = comp(if_commit, [comp(splice_safe, [PatsT]), ChainC, SeqC]).

splice_part(Env, G, Acc-S0, [Code-P-Pat|Acc]-S) :-
    fresh_g('P', P, S0, S1),
    goal_key(G, just(F/N)),
    goal_args(G, As),
    Env = env(Defined, _, _),
    if_commit(ord_memberchk(F/N, Defined),
              ( S = S1, cp_name(F, CF), conc(As, [P], CAs), Code = [comp(CF, CAs)], list_t(As, Pat) ),
    if_commit(F/N == member/2,
              ( fresh_g('M', M, S1, S), As = [X, L],
                Code = [comp(member_cp, [M, L]), comp(cp_rows, [M, P])], list_t([X], Pat) ),
    if_commit(F/N == between/3,
              ( fresh_g('M', M, S1, S), As = [Lo, Hi, X],
                Code = [comp(between_cp, [Lo, Hi, M]), comp(cp_rows, [M, P])], list_t([X], Pat) ),
              gfail_throw("internal: not a generator")))).

parts_pats([], []).
parts_pats([_-_-Pat|Ps], [Pat|Pats]) :-
    parts_pats(Ps, Pats).

parts_cps([], []).
parts_cps([_-P-_|Ps], [comp(cp, [P])|Cps]) :-
    parts_cps(Ps, Cps).

chain([], Final, _, Final).
chain([Code-P-_|More], Final, Out, Gs) :-
    chain(More, Final, Out, Rest),
    mk_conj(Rest, RestC),
    conc(Code, [comp(if_commit, [comp('=', [P, atom('[]')]), comp('=', [Out, atom('[]')]), RestC])], Gs).

% ---------------------------------------------------------------------------
% Analyses

%  effectful_preds(+Program, -Keys): predicates that (transitively) write
%  output.
effectful_preds(P, Set) :-
    program_clauses(P, KCs),
    maplist(kc_calls, KCs, Calls),
    effect_keys(EK),
    findall(K, ( member(K-Cs, Calls), once_det(( member(F/N, Cs), key_atom(F, N, KA), memberchk(KA, EK) )) ), D0),
    sort(D0, Direct),
    effect_fix(Direct, Calls, Set).

kc_calls(K-Cls, K-Calls) :-
    findall(C, ( member(clause(_, B, _), Cls), body_calls(B, BCs), member(C, BCs) ), Calls).

effect_fix(S0, Calls, S) :-
    findall(K, ( member(K-Cs, Calls), once_det(( member(C, Cs), ord_memberchk(C, S0) )) ), New0),
    sort(New0, New),
    ord_union(S0, New, S1),
    if_commit(S1 == S0, S = S0, effect_fix(S1, Calls, S)).

%  body_calls(+Body, -Keys)
body_calls(T, Ks) :-
    body_shape(T, Shape),
    body_calls_(Shape, T, Ks).

body_shape(T, Shape) :-
    if_commit(( T = comp(Op, [_, _]), memberchk(Op, [',', ';', '->', '*->']) ), Shape = pair,
    if_commit(( T = comp(F, [_]), memberchk(F, ['\\+', not, once, once_det, ignore, call]) ), Shape = one,
    if_commit(T = comp(if_commit, [_, _, _]), Shape = three,
    if_commit(T = comp(findall, [_, _, _]), Shape = findall,
    if_commit(T = comp(forall, [_, _]), Shape = forall,
    if_commit(T = comp(aggregate_all, [_, _, _]), Shape = findall,
    if_commit(( T = comp(call, [G|Extra]), G \= var(_, _), add_args(G, Extra, just(_)) ), Shape = call,
              Shape = goal))))))).

body_calls_(pair, comp(_, [A, B]), Ks) :-
    body_calls(A, KA),
    body_calls(B, KB),
    conc(KA, KB, Ks).
body_calls_(one, comp(_, [A]), Ks) :-
    body_calls(A, Ks).
body_calls_(three, comp(_, [A, B, C]), Ks) :-
    body_calls(A, KA),
    body_calls(B, KB),
    body_calls(C, KC),
    concat_lists([KA, KB, KC], Ks).
body_calls_(findall, comp(_, [_, G, _]), Ks) :-
    body_calls(G, Ks).
body_calls_(forall, comp(_, [A, B]), Ks) :-
    body_calls(A, KA),
    body_calls(B, KB),
    conc(KA, KB, Ks).
body_calls_(call, comp(_, [G|Extra]), Ks) :-
    add_args(G, Extra, just(G1)),
    body_calls(G1, Ks).
body_calls_(goal, T, Ks) :-
    goal_key(T, M),
    if_commit(M = just(K), Ks = [K], Ks = []).

%  restrict_to(+Roots, +Program, -Program): the predicates reachable from
%  the roots.
restrict_to(Roots, prog(Preds, Order, Ds), prog(Preds1, Order1, Ds)) :-
    findall(R, ( member(R, Roots), map_member(Preds, R, true) ), Rs0),
    sort(Rs0, Rs),
    reach_fix(Rs, Preds, Keep),
    map_pairs(Preds, Pairs),
    findall(K-V, ( member(K-V, Pairs), ord_memberchk(K, Keep) ), KPairs),
    list_to_assoc(KPairs, Preds1),
    findall(K, ( member(K, Order), ord_memberchk(K, Keep) ), Order1).

reach_fix(S0, Preds, S) :-
    findall(C, ( member(K, S0), map_find(Preds, K, [], Cls), member(clause(_, B, _), Cls),
                 body_calls(B, Cs), member(C, Cs), map_member(Preds, C, true) ), New0),
    sort(New0, New),
    ord_union(S0, New, S1),
    if_commit(S1 == S0, S = S0, reach_fix(S1, Preds, S)).

% ---------------------------------------------------------------------------
% Closure specialisation: maplist(succ, L, R) calls a copy of maplist/3 in
% which call(G, X, Y) has become succ(X, Y), so no meta-call remains.  Each
% new predicate is recorded as closure_spec(New/NewArity, Old/Arity,
% Position, Closure); the checker re-derives its clauses.

specialise_meta(P0, E) :-
    meta_positions(P0, MetaSet),
    prog_order(P0, Order),
    map_empty(Memo),
    catch(( spec_loop(Order, P0, Memo, MetaSet, [], [], P, Evs, Steps),
            E = right(P-Evs-Steps) ),
          spec_error(M),
          E = left(M)).

spec_loop([], P, _, _, Evs, Steps, P, Evs, Steps).
spec_loop([K|Ks], P0, Memo0, MS, Evs0, Steps0, P, Evs, Steps) :-
    prog_preds(P0, Preds0),
    map_find(Preds0, K, [], Cls),
    foldl(spec_clause(MS), Cls, []-Memo0-P0-[]-[]-[], ClsR-Memo1-P1-NewKeys-Evs1-Steps1),
    rev(ClsR, Cls1),
    P1 = prog(Preds1, Order1, Ds1),
    map_put(K, Cls1, Preds1, Preds2),
    conc(Evs0, Evs1, Evs2),
    conc(Steps0, Steps1, Steps2),
    conc(Ks, NewKeys, Ks1),
    spec_loop(Ks1, prog(Preds2, Order1, Ds1), Memo1, MS, Evs2, Steps2, P, Evs, Steps).

spec_clause(MS, clause(H, B, NV), Acc-M0-P0-K0-E0-S0, [clause(H, B1, NV)|Acc]-M1-P1-K1-E1-S1) :-
    spec_body(B, MS, M0, P0, B1, M1, P1, K, E, S),
    conc(K0, K, K1),
    conc(E0, E, E1),
    conc(S0, S, S1).

spec_body(T, MS, M0, P0, T1, M, P, Ks, Es, Ss) :-
    spec_shape(T, Shape),
    spec_body_(Shape, T, MS, M0, P0, T1, M, P, Ks, Es, Ss).

spec_shape(T, Shape) :-
    if_commit(( T = comp(Op, [_, _]), memberchk(Op, [',', ';', '->', '*->']) ), Shape = pair,
    if_commit(T = comp(if_commit, [_, _, _]), Shape = three,
    if_commit(( T = comp(F, [_]), memberchk(F, ['\\+', not, once, once_det, ignore]) ), Shape = one,
    if_commit(T = comp(findall, [_, _, _]), Shape = findall,
    if_commit(( T = comp(call, [G|Extra]), G \= var(_, _), add_args(G, Extra, just(_)) ), Shape = call,
              Shape = goal))))).

spec_body_(pair, comp(Op, [A, B]), MS, M0, P0, comp(Op, [A1, B1]), M, P, Ks, Es, Ss) :-
    spec_body(A, MS, M0, P0, A1, M1, P1, K1, E1, S1),
    spec_body(B, MS, M1, P1, B1, M, P, K2, E2, S2),
    conc(K1, K2, Ks),
    conc(E1, E2, Es),
    conc(S1, S2, Ss).
spec_body_(three, comp(if_commit, [A, B, C]), MS, M0, P0, comp(if_commit, [A1, B1, C1]), M, P, Ks, Es, Ss) :-
    spec_body(A, MS, M0, P0, A1, M1, P1, K1, E1, S1),
    spec_body(B, MS, M1, P1, B1, M2, P2, K2, E2, S2),
    spec_body(C, MS, M2, P2, C1, M, P, K3, E3, S3),
    concat_lists([K1, K2, K3], Ks),
    concat_lists([E1, E2, E3], Es),
    concat_lists([S1, S2, S3], Ss).
spec_body_(one, comp(F, [A]), MS, M0, P0, comp(F, [A1]), M, P, Ks, Es, Ss) :-
    spec_body(A, MS, M0, P0, A1, M, P, Ks, Es, Ss).
spec_body_(findall, comp(findall, [X, G, L]), MS, M0, P0, comp(findall, [X, G1, L]), M, P, Ks, Es, Ss) :-
    spec_body(G, MS, M0, P0, G1, M, P, Ks, Es, Ss).
spec_body_(call, comp(call, [G|Extra]), MS, M0, P0, T1, M, P, Ks, Es, Ss) :-
    add_args(G, Extra, just(G1)),
    spec_body(G1, MS, M0, P0, T1, M, P, Ks, Es, Ss).
spec_body_(goal, T, MS, M0, P0, T1, M, P, Ks, Es, Ss) :-
    goal_key(T, MK),
    if_commit(( MK = just(Key), meta_position(Key, MS, Pos), closure_at(T, Pos, Clo) ),
              specialise_call(P0, M0, Key, Pos, Clo, T, T1, M, P, Ks, Es, Ss),
              ( T1 = T, M = M0, P = P0, Ks = [], Es = [], Ss = [] )).

%  semidet: the first argument position of Key that is called as a closure
meta_position(F/N, MS, Pos) :-
    N1 is N - 1,
    once_det(( between(0, N1, Pos), ord_memberchk((F/N)-Pos, MS) )).

%  semidet: a callable, non-variable closure argument
closure_at(T, Pos, Clo) :-
    goal_args(T, As),
    P1 is Pos + 1,
    nth_det(P1, As, just(Clo)),
    is_callable_t(Clo, true).

specialise_call(P0, Memo, F/N, Pos, Clo, T, T1, Memo1, P, Ks, Es, Ss) :-
    term_vars_ordered(Clo, FreeVs),
    show_answer_term(comp(k, [atom(F), int(N), int(Pos), Clo]), Canon),
    goal_args(T, As),
    other_args(As, Pos, Others),
    conc(FreeVs, Others, CallArgs),
    map_get(Memo, Canon, MName),
    assoc_to_keys(Memo, MemoKeys),
    length(MemoKeys, Size),
    specialise_known(MName, Size, P0, Memo, F/N, Pos, Clo, CallArgs, T1, Memo1, P, Ks, Es, Ss, Canon, FreeVs).

specialise_known(just(Name), _, P, Memo, _, _, _, CallArgs, comp(Name, CallArgs), Memo, P, [], [], [], _, _).
specialise_known(nothing, Size, P0, Memo, F/N, Pos, Clo, CallArgs, comp(Name, CallArgs), Memo1, P,
                 [NewKey], [Ev], [Step], Canon, FreeVs) :-
    if_commit(Size >= 500,
              throw(spec_error("closure specialisation did not reach a fixpoint (closures keep growing)")),
              true),
    Size1 is Size + 1,
    format(atom(Name), "~w__m~d", [F, Size1]),
    length(FreeVs, NF),
    NA is NF + N - 1,
    NewKey = Name/NA,
    map_put(Canon, Name, Memo, Memo1),
    prog_preds(P0, Preds0),
    map_find(Preds0, F/N, [], Cls),
    maplist(spec_new_clause(Name, Pos, Clo, F/N), Cls, Cls1),
    P0 = prog(Preds, Order, Ds),
    map_put(NewKey, Cls1, Preds, Preds1),
    conc(Order, [NewKey], Order1),
    P = prog(Preds1, Order1, Ds),
    key_t(NewKey, NKT),
    key_t(F/N, KT),
    Step = comp(closure_spec, [NKT, KT, int(Pos), Clo]),
    show_term_q(Clo, CloS),
    format(string(Ev), "closure_specialised(~w/~d, ~s) as ~w", [F, N, CloS, Name]).

spec_new_clause(Name, Pos, Clo, F/N, clause(H, B, CNV), clause(H1, B1, NV1)) :-
    goal_args(H, HAs),
    P1 is Pos + 1,
    nth_det(P1, HAs, just(G)),
    rename_term(CNV, Clo, CloR),
    term_vars_ordered(CloR, CloVars),
    other_args(HAs, Pos, OthersH),
    maplist(subst_var(G, CloR), OthersH, OthersS),
    conc(CloVars, OthersS, NewArgs),
    H1 = comp(Name, NewArgs),
    if_commit(G = var(_, _),
              ( subst_var(G, CloR, B, B1),
                max_var_id(Clo, MC),
                NV1 is CNV + MC + 2 ),
              ( format(string(M), "closure argument of ~w/~d is not a variable in every clause", [F, N]),
                throw(spec_error(M)) )).

other_args(As, Pos, Others) :-
    numbered_list(As, 0, NAs),
    findall(A, ( member(J-A, NAs), J =\= Pos ), Others).

%  subst_var(+Var, +By, +Term, -Term)
subst_var(V, By, T, T1) :-
    if_commit(( T = var(_, _), same_term(T, V, true) ),
              T1 = By,
              if_commit(( T = comp(call, [G|Extra]), same_term(G, V, true), add_args(By, Extra, just(G1)) ),
                        T1 = G1,
                        if_commit(T = comp(Fn, As),
                                  ( maplist(subst_var(V, By), As, As1), T1 = comp(Fn, As1) ),
                                  T1 = T))).

%  meta_positions(+Program, -Set): (Key-ArgIndex) pairs whose argument is
%  called as a closure: directly by call/N, or by being passed to such a
%  position.
meta_positions(P, Set) :-
    program_clauses(P, KCs),
    findall(K-I, ( member(K-Cs, KCs), member(clause(H, B, _), Cs), head_var_pos(H, I, V),
                   called_in(V, B) ), D0),
    sort(D0, Direct),
    meta_fix(Direct, KCs, Set).

meta_fix(S0, KCs, S) :-
    findall(K-I, ( member(K-Cs, KCs), member(clause(H, B, _), Cs), head_var_pos(H, I, V),
                   passed_to(V, B, Ps), member(QJ, Ps), ord_memberchk(QJ, S0) ), New0),
    sort(New0, New),
    ord_union(S0, New, S1),
    if_commit(S1 == S0, S = S0, meta_fix(S1, KCs, S)).

%  generator: (I, V) for every head argument that is a variable
head_var_pos(H, I, V) :-
    goal_args(H, As),
    numbered_list(As, 0, NAs),
    member(I-V, NAs),
    V = var(_, _).

:- relation(head_var_pos/3).

%  semidet: V is called (call(V, ...)) somewhere in T
called_in(V, T) :-
    if_commit(( T = comp(call, [G|_]), same_term(G, V, true) ),
              true,
              ( T = comp(_, As), once_det(( member(A, As), called_in(V, A) )) )).

passed_to(V, T, Ps) :-
    if_commit(( T = comp(Op, [A, B]), memberchk(Op, [',', ';', '->', '*->']) ),
              ( passed_to(V, A, PA), passed_to(V, B, PB), conc(PA, PB, Ps) ),
    if_commit(T = comp(if_commit, As),
              ( maplist(passed_to(V), As, PLs), concat_lists(PLs, Ps) ),
    if_commit(( T = comp(F, [A]), memberchk(F, ['\\+', not, once, once_det, ignore]) ),
              passed_to(V, A, Ps),
    if_commit(T = comp(findall, [_, G, _]),
              passed_to(V, G, Ps),
              ( goal_key(T, MK),
                if_commit(MK = just(Q),
                          ( goal_args(T, As1), numbered_list(As1, 0, NAs),
                            findall(Q-J, ( member(J-A1, NAs), same_term(A1, V, true) ), Ps) ),
                          Ps = []) ))))).
