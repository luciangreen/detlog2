/*  proof_steps.pl - the step and derivation rules of the proof checker
    (proof.pl): PRED, FACTS, CLAUSE, ROWS, MEMO and the goal rules.

    The clause context is pcx(Defined, Effectful, UserMember, ConvKeys,
    AuxMap, Vs, ClauseVarIds).  A derivation node is read into
    n(Rule, Source, Env, Out, Generated, Subderivations).
*/

teq_list(As, Bs) :-
    list_t(As, A),
    list_t(Bs, B),
    teq(A, B).

distinct_vars(Ts) :-
    all_var_terms(Ts, Ids),
    sort(Ids, S),
    same_length(S, Ts).

all_var_terms([], []).
all_var_terms([var(I, _)|Ts], [I|Is]) :-
    all_var_terms(Ts, Is).

pairwise_disjoint(Sets) :-
    if_commit(( append(_, [S|Rest], Sets), member(T, Rest), member(I, S), memberchk(I, T) ), fail, true).

% ---------------------------------------------------------------------------
% Rules PRED and FACTS

check_pred_step(Inter, S, Cls) :-
    if_commit(S = comp(facts_packet, [KT, ClT]),
              check_facts_step(Inter, KT, ClT, Cls),
              if_commit(S = comp(pred_packet, [KT, int(K), ClT]),
                        check_pred_packet(Inter, KT, K, ClT, Cls),
                        pfail("bad predicate step"))).

check_facts_step(Inter, KT, ClT, [Cl]) :-
    term_key_or(KT, "facts_packet: bad key", F/N),
    show_key(F/N, KS),
    as_clause(ClT, Cl),
    map_get(Inter, F/N, MF),
    if_commit(MF = just(Facts), true, ( format(string(M0), "facts_packet: ~s", [KS]), pfail(M0) )),
    Cl = clause(H, B, _),
    conj_list(B, Gs),
    cp_name(F, CF),
    N1 is N + 1,
    if_commit(( H = comp(CF, HArgs), length(HArgs, N1),
                Gs = [comp(member_cp, [P, RowsT]), comp(cp_filter, [P1, ArgsT, RV])] ),
              ( take(N, HArgs, Args),
                last_of(HArgs, LastH),
                ensure(( teq(P, P1), is_var_t(P, true), teq(LastH, RV), is_var_t(RV, true) ),
                       "facts_packet: packet variables"),
                conc(Args, [P, RV], AV),
                ensure(distinct_vars(AV), "facts_packet: argument variables are not distinct"),
                list_of(ArgsT, ArgsL),
                ensure(teq_list(ArgsL, Args), "facts_packet: cp_filter pattern is not the arguments"),
                list_of(RowsT, Rows),
                length(Rows, LR),
                length(Facts, LFa),
                ensure(LR =:= LFa, "facts_packet: one row per fact"),
                maplist(row_is_fact, Rows, Facts),
                maplist(term_var_ids, Rows, RowIds),
                list_t(AV, AVT),
                term_var_ids(AVT, AVIds),
                conc(RowIds, [AVIds], AllIds),
                ensure(pairwise_disjoint(AllIds), "facts_packet: rows share variables") ),
              ( format(string(M), "facts_packet: wrong shape for ~s", [KS]), pfail(M) )).

row_is_fact(R, clause(H, _, _)) :-
    goal_args(H, As),
    list_t(As, AL),
    empty_state(0, St),
    ensure(variant_t(St, R, AL, true), "facts_packet: a row is not its fact").

last_of([X|Xs], L) :-
    last_of_(Xs, X, L).

last_of_([], X, X).
last_of_([Y|Ys], _, L) :-
    last_of_(Ys, Y, L).

init_of([X|Xs], I) :-
    init_of_(Xs, X, I).

init_of_([], _, []).
init_of_([Y|Ys], X, [X|I]) :-
    init_of_(Ys, Y, I).

check_pred_packet(Inter, KT, K, ClT, [Cl]) :-
    term_key_or(KT, "pred_packet: bad key", F/N),
    show_key(F/N, KS),
    as_clause(ClT, Cl),
    map_get(Inter, F/N, MC),
    if_commit(MC = just(Cls), true, ( format(string(M0), "pred_packet: ~s", [KS]), pfail(M0) )),
    length(Cls, LC),
    ensure(K =:= LC, "pred_packet: clause count"),
    Cl = clause(H, B, _),
    cp_name(F, CF),
    N1 is N + 1,
    if_commit(( H = comp(CF, HArgs), length(HArgs, N1) ),
              ( take(N, HArgs, Args),
                last_of(HArgs, RV),
                conj_list(B, Calls),
                conc(Args, [RV], AR),
                ensure(distinct_vars(AR), "pred_packet: head variables are not distinct"),
                pred_body_ok(K, Calls, CF, Args, RV) ),
              pfail("pred_packet: wrong head")).

pred_body_ok(K, Calls, CF, Args, RV) :-
    list_t(Args, AL),
    format(atom(C1), "~w_c1", [CF]),
    if_commit(( K =:= 0, Calls = [comp('=', [R, atom('[]')])], teq(R, RV) ), true,
    if_commit(( K =:= 1, Calls = [comp(C1, [A, R])], teq(R, RV), teq(A, AL) ), true,
    if_commit(K >= 2,
              ( init_of(Calls, Cs), last_of(Calls, LastG),
                length(Cs, LCs),
                ensure(LCs =:= K, "pred_packet: one call per clause"),
                numbered_list(Cs, 1, NCs),
                maplist(clause_call_row(CF, AL), NCs, Rs),
                list_t(Rs, RsL),
                ensure(teq(LastG, comp(rows_concat, [RsL, RV])), "pred_packet: rows_concat"),
                conc(Args, [RV|Rs], All),
                ensure(distinct_vars(All), "pred_packet: packet variables are not distinct") ),
              pfail("pred_packet: wrong body")))).

clause_call_row(CF, AL, I-C, R) :-
    format(atom(Nm), "~w_c~d", [CF, I]),
    if_commit(( C = comp(Nm, [A, R0]), teq(A, AL), is_var_t(R0, true) ),
              R = R0,
              pfail("pred_packet: clause call")).

% ---------------------------------------------------------------------------
% Rule CLAUSE

check_clause_step(Cx0, S, [Gen]) :-
    if_commit(S = comp(clause_packet, [KT, int(I), SrcT, GenT, Deriv]), true, pfail("bad clause step")),
    term_key_or(KT, "clause_packet: bad key", F/_),
    as_clause(SrcT, clause(H, B, _)),
    as_clause(GenT, Gen),
    term_vars_ordered(comp(c, [H, B]), VsL),
    list_t(VsL, Vs),
    term_var_ids(Vs, CVs),
    Cx0 = pcx(D, E, U, C, A, _, _),
    Cx = pcx(D, E, U, C, A, Vs, CVs),
    goal_args(H, HAs),
    list_t(HAs, HeadArgs),
    cp_name(F, CF),
    format(atom(Name), "~w_c~d", [CF, I]),
    format(string(Where), "~w: ", [Name]),
    Gen = clause(GH, GB, _),
    if_commit(( GH = comp(Name, [ArgsV, RowsV]),
                GB = comp(if_commit, [comp(copy_term, [A1, HA]), Body, comp('=', [R1, atom('[]')])]) ),
              ( wmsg(Where, "packet frame", M1),
                ensure(( teq(A1, ArgsV), teq(R1, RowsV), teq(HA, HeadArgs) ), M1),
                wmsg(Where, "Args/Rows are not fresh", M2),
                ensure(fresh_p(Cx, [ArgsV, RowsV]), M2),
                clause_intro(B, Cx, Where, Deriv, Body, RowsV, HeadArgs, Vs, Intro),
                var_term_ids([ArgsV, RowsV], AIds),
                conc(AIds, Intro, AllIds),
                wmsg(Where, "a fresh variable is introduced twice", M3),
                ensure(distinct_ids(AllIds), M3) ),
              ( wmsg(Where, "wrong clause shape", M), pfail(M) )).

wmsg(Where, Msg, M) :-
    string_concat(Where, Msg, M).

clause_intro(B, Cx, Where, Deriv, Body, RowsV, HeadArgs, Vs, Intro) :-
    if_commit(B == atom(true),
              ( list_t([HeadArgs], HL),
                wmsg(Where, "fact clause", M),
                ensure(( Deriv == atom(none), teq(Body, comp('=', [RowsV, HL])) ), M),
                Intro = [] ),
              ( node(Deriv, n(_, NSrc, NEnv, EnvRows, NGen, _)),
                conj_list(Body, Goals),
                wmsg(Where, "empty body", M1),
                ensure(Goals \== [], M1),
                wmsg(Where, "derivation is not of the clause body", M2),
                ensure(( teq(NSrc, B), teq(NEnv, Vs) ), M2),
                conc(NGen, [comp(splice_extend, [EnvRows, HeadArgs, Vs, RowsV])], Want),
                wmsg(Where, "body is not the derivation's code followed by the projection", M3),
                ensure(teq_list(Goals, Want), M3),
                wmsg(Where, "Env is not fresh", M4),
                ensure(fresh_p(Cx, [EnvRows]), M4),
                chk(Cx, Deriv, Xs),
                var_term_ids([EnvRows], EIds),
                conc(EIds, Xs, Intro) )).

var_term_ids(Ts, Ids) :-
    findall(I, member(var(I, _), Ts), Ids).

distinct_ids(Ids) :-
    sort(Ids, S),
    same_length(S, Ids).

fresh_p(pcx(_, _, _, _, _, _, CVs), Ts) :-
    if_commit(( member(T, Ts), if_commit(( T = var(I, _), if_commit(ord_memberchk(I, CVs), fail, true) ), fail, true) ),
              fail,
              true).

% ---------------------------------------------------------------------------
% Rule ROWS: iteration over a packet.

check_aux_step(Cx0, S, [C1, C2]) :-
    if_commit(S = comp(aux, [atom(Name), Vs, ClsT, Deriv]), true, pfail("bad aux step")),
    list_of(ClsT, CL),
    if_commit(CL = [C1T, C2T], true, pfail("aux: expected two clauses")),
    as_clause(C1T, C1),
    as_clause(C2T, C2),
    term_var_ids(Vs, CVs),
    Cx0 = pcx(D, E, U, C, A, _, _),
    Cx = pcx(D, E, U, C, A, Vs, CVs),
    format(string(Where), "~w: ", [Name]),
    C1 = clause(H1, B1, _),
    wmsg(Where, "empty-packet clause", M1),
    ensure(( teq(H1, comp(Name, [atom('[]'), atom('[]')])), B1 == atom(true) ), M1),
    node(Deriv, n(_, _, NEnv, NOut, NGen, _)),
    C2 = clause(H2, B2, _),
    conj_list(B2, G2),
    if_commit(( H2 = comp(Name, [comp('.', [Row, Rs]), Out]),
                G2 = [ comp(if_commit, [comp('=', [Row1, comp(out, [T])]), comp('=', [O1, OutItem]), Rest]),
                       comp(Name, [Rs1, O2]),
                       comp(rows_concat, [Lst, Out1]) ] ),
              ( list_t([comp(out, [T])], OIL),
                wmsg(Where, "frame", M2),
                ensure(( teq(Row1, Row), teq(Rs1, Rs), teq(Out1, Out), teq(OutItem, OIL) ), M2),
                list_t([O1, O2], O12),
                wmsg(Where, "rows_concat", M3),
                ensure(teq(Lst, O12), M3),
                conj_list(Rest, RestGs),
                wmsg(Where, "row body", M4),
                ensure(teq_list(RestGs, [comp(copy_term, [Row, Vs])|NGen]), M4),
                wmsg(Where, "derivation env/out", M5),
                ensure(( teq(NEnv, Vs), teq(NOut, O1) ), M5),
                Frame = [Row, Rs, Out, O1, O2, T],
                wmsg(Where, "frame variables are not fresh", M6),
                ensure(fresh_p(Cx, Frame), M6),
                chk(Cx, Deriv, Xs),
                var_term_ids(Frame, FIds),
                conc(FIds, Xs, All),
                wmsg(Where, "a fresh variable is introduced twice", M7),
                ensure(distinct_ids(All), M7) ),
              ( wmsg(Where, "wrong iteration clause", M), pfail(M) )).

% ---------------------------------------------------------------------------
% Rule MEMO, checked by evaluation: the memo clause is the lookup template,
% and every table entry is re-run on the original program with ordinary
% Prolog semantics and must give exactly the recorded packet.

check_memo_step(pctx(_, _, Orig), S, [Cl]) :-
    if_commit(S = comp(memo_table, [KT, CompleteT, ClT]), true, pfail("bad memo step")),
    term_key_or(KT, "memo_table: bad key", F/N),
    show_key(F/N, KS),
    as_clause(ClT, Cl),
    format(string(Here), "memo table for ~s: ", [KS]),
    Cl = clause(H, B, _),
    cp_name(F, CF),
    N1 is N + 1,
    if_commit(( H = comp(CF, HArgs), length(HArgs, N1),
                B = comp(if_commit, [comp(memo_lookup, [ArgsT, Table, Rows]), atom(true), Fallback]) ),
              ( take(N, HArgs, Args),
                last_of(HArgs, Last),
                conc(Args, [Last], AL),
                list_t(Args, ArgsL),
                wmsg(Here, "frame", M1),
                ensure(( distinct_vars(AL), teq(Rows, Last), teq(ArgsT, ArgsL) ), M1),
                if_commit(CompleteT == atom(true),
                          Want = comp(memo_miss, [comp('/', [atom(F), int(N)]), ArgsL]),
                          ( atom_concat(CF, '__compute', CFC), Want = comp(CFC, HArgs) )),
                wmsg(Here, "fallback", M2),
                ensure(teq(Fallback, Want), M2),
                list_of(Table, Entries),
                with_prelude(Orig, OP),
                maplist(check_memo_entry(Here, F, N, OP), Entries) ),
              ( wmsg(Here, "not a memo lookup clause", M), pfail(M) )).

check_memo_entry(Here, F, N, OP, Entry) :-
    list_of(Entry, EL),
    wmsg(Here, "bad table entry", M0),
    if_commit(EL = [Pat, Recorded], true, pfail(M0)),
    list_of(Pat, Pats),
    length(Pats, LP),
    wmsg(Here, "pattern arity", M1),
    ensure(LP =:= N, M1),
    if_commit(N =:= 0, Goal = atom(F), Goal = comp(F, Pats)),
    max_var_id(Goal, MV),
    NV is MV + 1,
    default_options(Opts),
    ref_run(Opts, OP, Goal, NV, Stream),
    stream_take_events(100001, Stream, Evs),
    findall(E, member(err(E), Evs), Errs),
    show_term_q(Goal, GS),
    if_commit(Errs = [E1|_], true, E1 = ""),
    format(string(M2), "~sre-running ~s raised ~s", [Here, GS, E1]),
    ensure(Errs == [], M2),
    maplist(actual_item(Pat), Evs, AItems),
    concat_lists(AItems, Actual),
    list_of(Recorded, Rec),
    format(string(M3), "~s~s: the recorded packet is not the program's answers", [Here, GS]),
    empty_state(0, St0),
    ensure(( same_length(Rec, Actual), maplist(variant_ok(St0), Rec, Actual) ), M3).

variant_ok(St, A, B) :-
    variant_t(St, A, B, true).

actual_item(Pat, ans(St), [R]) :-
    resolve(Pat, St, R).
actual_item(_, out(O), [comp(out, [atom(A)])]) :-
    atom_string(A, O).
actual_item(_, err(_), []).

stream_take_events(N, S, Evs) :-
    if_commit(N =< 0,
              Evs = [],
              ( force(S, F), take_events_f(F, N, Evs) )).

take_events_f([], _, []).
take_events_f([E|T], N, [E|Evs]) :-
    N1 is N - 1,
    stream_take_events(N1, T, Evs).

% ---------------------------------------------------------------------------
% Derivation nodes

node(T, n(R, Src, Env, Out, Gen, Subs)) :-
    if_commit(T = comp(d, [atom(R0), Src0, Env0, Out0, GenT, SubsT]),
              ( R = R0, Src = Src0, Env = Env0, Out = Out0, list_of(GenT, Gen), list_of(SubsT, Subs) ),
              ( show_term_q(T, TS), sub_string_det(TS, 200, TS1),
                format(string(M), "not a derivation node: ~s", [TS1]), pfail(M) )).

sub_string_det(S, N, T) :-
    string_length(S, L),
    K is min(N, L),
    sub_string(S, 0, K, _, T).

%  chk(+Cx, +Deriv, -FreshIds): check one derivation node; the fresh
%  variables it introduces.
chk(Cx, D, Xs) :-
    node(D, Nd),
    Nd = n(Rule, Src, _, _, _, _),
    show_term_q(Src, SS),
    sub_string_det(SS, 120, SS1),
    format(string(Here), "rule ~w for ~s: ", [Rule, SS1]),
    if_commit(rule_known(Rule), true, ( wmsg(Here, "unknown rule", M), pfail(M) )),
    chk_rule(Rule, Cx, Nd, Here, Xs).

rule_known(R) :-
    memberchk(R, [true, fail, det, effect, call, member_cp, between_cp, length_det,
                  builtin_rows, rewrite, det_prefix, seq, rows_true, rows, disj,
                  ite_det, ite, neg_det, neg, findall, count, splice]).

need(G, Here, Msg) :-
    wmsg(Here, Msg, M),
    ensure(G, M).

gen_is(Gen, Want, Here) :-
    need(teq_list(Gen, Want), Here, "generated code is not the rule's template").

fresh_is(Cx, Ts, Here, Ids) :-
    need(fresh_p(Cx, Ts), Here, "a new variable is not fresh"),
    need(distinct_vars(Ts), Here, "new variables are not distinct"),
    var_term_ids(Ts, Ids).

env_level(Cx, Env, Here) :-
    Cx = pcx(_, _, _, _, _, Vs, _),
    need(teq(Env, Vs), Here, "environment is not the clause variables").

sub_node(Subs, K, Here, T) :-
    K1 is K + 1,
    nth_det(K1, Subs, M),
    if_commit(M = just(T), true, ( wmsg(Here, "missing sub-derivation", Msg), pfail(Msg) )).

rows_sub(Cx, Subs, K, G, Rin, Out, Here, Xs) :-
    sub_node(Subs, K, Here, T),
    node(T, n(R, S, E, O, _, _)),
    need(( teq(S, G), teq(E, Rin), teq(O, Out) ), Here, "sub-derivation does not match"),
    need(memberchk(R, [rows, rows_true]), Here, "expected a packet iteration"),
    chk(Cx, T, Xs).

env_sub(Cx, Subs, K, G, Out, Here, Xs) :-
    Cx = pcx(_, _, _, _, _, Vs, _),
    sub_node(Subs, K, Here, T),
    node(T, n(_, S, E, O, _, _)),
    need(( teq(S, G), teq(E, Vs), teq(O, Out) ), Here, "sub-derivation does not match"),
    chk(Cx, T, Xs).

template_fail(Here) :-
    wmsg(Here, "template", M),
    pfail(M).

chk_rule(true, Cx, n(_, Src, E, O, Gen, _), Here, []) :-
    env_level(Cx, E, Here),
    need(Src == atom(true), Here, "source"),
    list_t([E], EL),
    gen_is(Gen, [comp('=', [O, EL])], Here).
chk_rule(fail, Cx, n(_, Src, E, O, Gen, _), Here, []) :-
    env_level(Cx, E, Here),
    need(memberchk(Src, [atom(fail), atom(false)]), Here, "source"),
    gen_is(Gen, [comp('=', [O, atom('[]')])], Here).
chk_rule(det, Cx, n(_, Src, E, O, Gen, _), Here, []) :-
    env_level(Cx, E, Here),
    need(is_det_goal_p(Cx, Src), Here, "not a deterministic, output-free built-in"),
    list_t([E], EL),
    gen_is(Gen, [comp(if_commit, [Src, comp('=', [O, EL]), comp('=', [O, atom('[]')])])], Here).
chk_rule(effect, Cx, n(_, Src, E, O, Gen, _), Here, Ids) :-
    env_level(Cx, E, Here),
    need(( goal_key(Src, just(F/N)), key_atom(F, N, KA), effect_keys(EK), memberchk(KA, EK),
           if_commit(defined_here(Cx, Src), fail, true) ),
         Here, "not an output built-in"),
    if_commit(( Gen = [comp(effect_text, [G1, T]), comp('=', [O1, Item])], teq(G1, Src), teq(O1, O),
                list_t([comp(out, [T]), E], IL), teq(Item, IL) ),
              fresh_is(Cx, [T], Here, Ids),
              template_fail(Here)).
chk_rule(call, Cx, n(_, Src, E, O, Gen, _), Here, Ids) :-
    env_level(Cx, E, Here),
    goal_key(Src, MK),
    if_commit(MK = just(F/K), true, ( wmsg(Here, "not callable", M), pfail(M) )),
    Cx = pcx(Defined, _, _, ConvKeys, _, _, _),
    need(ord_memberchk(F/K, Defined), Here, "callee is not a converted predicate"),
    cp_name(F, CF),
    K1 is K + 1,
    need(ord_memberchk(CF/K1, ConvKeys), Here, "callee packet missing from the program"),
    goal_args(Src, As),
    if_commit(( Gen = [comp(CF, QArgs), comp(splice_extend, [P, E1, Pat, O1])],
                conc(As, [P], Want), teq_list(QArgs, Want), teq(E1, E),
                list_t(As, AL), teq(Pat, AL), teq(O1, O) ),
              fresh_is(Cx, [P], Here, Ids),
              template_fail(Here)).
chk_rule(member_cp, Cx, n(_, Src, E, O, Gen, _), Here, Ids) :-
    env_level(Cx, E, Here),
    Cx = pcx(_, _, UM, _, _, _, _),
    need(UM == false, Here, "member/2 is user-defined"),
    if_commit(( Src = comp(member, [X, L]),
                Gen = [comp(member_cp, [P, L1]), comp(cp_rows, [P1, Pr]), comp(splice_extend, [Pr1, E1, Pat, O1])],
                teq(L1, L), teq(P1, P), teq(Pr1, Pr), teq(E1, E), list_t([X], XL), teq(Pat, XL), teq(O1, O) ),
              fresh_is(Cx, [P, Pr], Here, Ids),
              template_fail(Here)).
chk_rule(between_cp, Cx, n(_, Src, E, O, Gen, _), Here, Ids) :-
    env_level(Cx, E, Here),
    Cx = pcx(Defined, _, _, _, _, _, _),
    need(if_commit(ord_memberchk(between/3, Defined), fail, true), Here, "between/3 is user-defined"),
    if_commit(( Src = comp(between, [Lo, Hi, X]),
                Gen = [comp(between_cp, [Lo1, Hi1, P]), comp(cp_rows, [P1, Pr]), comp(splice_extend, [Pr1, E1, Pat, O1])],
                teq(Lo1, Lo), teq(Hi1, Hi), teq(P1, P), teq(Pr1, Pr), teq(E1, E),
                list_t([X], XL), teq(Pat, XL), teq(O1, O) ),
              fresh_is(Cx, [P, Pr], Here, Ids),
              template_fail(Here)).
chk_rule(length_det, Cx, n(_, Src, E, O, Gen, _), Here, []) :-
    env_level(Cx, E, Here),
    Cx = pcx(Defined, _, _, _, _, _, _),
    need(if_commit(ord_memberchk(length/2, Defined), fail, true), Here, "length/2 is user-defined"),
    if_commit(Src = comp(length, As), true, ( wmsg(Here, "source", M), pfail(M) )),
    list_t([E], EL),
    gen_is(Gen, [comp(if_commit, [comp(length_det, As), comp('=', [O, EL]), comp('=', [O, atom('[]')])])], Here).
chk_rule(builtin_rows, Cx, n(_, Src, E, O, Gen, _), Here, Ids) :-
    env_level(Cx, E, Here),
    nondet_builtin_keys(ND),
    need(( goal_key(Src, just(F/N)), key_atom(F, N, KA), memberchk(KA, ['atom_concat/3'|ND]),
           if_commit(defined_here(Cx, Src), fail, true) ),
         Here, "not a nondeterministic built-in"),
    if_commit(( Gen = [comp(builtin_rows, [G1, Br]), comp(splice_extend, [Br1, E1, Pat, O1])],
                teq(G1, Src), teq(Br1, Br), teq(E1, E), list_t([Src], SL), teq(Pat, SL), teq(O1, O) ),
              fresh_is(Cx, [Br], Here, Ids),
              template_fail(Here)).
chk_rule(rewrite, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    rewrite_of(Src, MG),
    if_commit(MG = just(G1), true, ( wmsg(Here, "no rewrite applies", M), pfail(M) )),
    sub_node(Subs, 0, Here, T),
    node(T, n(_, S1, E1, O1, Gen1, _)),
    Cx = pcx(_, _, _, _, _, Vs, _),
    need(( teq(S1, G1), teq(E1, Vs), teq(O1, O) ), Here, "rewritten goal"),
    gen_is(Gen, Gen1, Here),
    chk(Cx, T, Xs).
chk_rule(det_prefix, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    conj_list(Src, Gs),
    span_det_p(Gs, Cx, Bs, Rest),
    length(Gs, LG),
    need(( LG >= 2, Bs \== [] ), Here, "no deterministic prefix"),
    sub_node(Subs, 0, Here, T),
    node(T, n(_, S1, E1, O1, Gen1, _)),
    Cx = pcx(_, _, _, _, _, Vs, _),
    mk_conj(Rest, RC),
    need(( teq(S1, RC), teq(E1, Vs), teq(O1, O) ), Here, "rest derivation"),
    mk_conj(Bs, BC),
    mk_conj(Gen1, G1C),
    gen_is(Gen, [comp(if_commit, [BC, G1C, comp('=', [O, atom('[]')])])], Here),
    chk(Cx, T, Xs).
chk_rule(seq, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    conj_list(Src, Gs),
    if_commit(Gs = [G1, _|_], true, ( wmsg(Here, "not a conjunction of two or more goals", M), pfail(M) )),
    Gs = [_|Rest],
    sub_node(Subs, 0, Here, T1),
    sub_node(Subs, 1, Here, T2),
    node(T1, n(_, S1, E1, R1, Gen1, _)),
    node(T2, n(Rule2, S2, E2, O2, Gen2, _)),
    Cx = pcx(_, _, _, _, _, Vs, _),
    need(( teq(S1, G1), teq(E1, Vs) ), Here, "first goal"),
    mk_conj(Rest, RC),
    need(( teq(S2, RC), teq(E2, R1), teq(O2, O) ), Here, "rest"),
    need(memberchk(Rule2, [rows, rows_true]), Here, "rest must iterate the packet"),
    conc(Gen1, Gen2, Want),
    gen_is(Gen, Want, Here),
    fresh_is(Cx, [R1], Here, A),
    chk(Cx, T1, X1),
    chk(Cx, T2, X2),
    concat_lists([A, X1, X2], Xs).
chk_rule(rows_true, _, n(_, Src, E, O, Gen, _), Here, []) :-
    need(Src == atom(true), Here, "source"),
    gen_is(Gen, [comp('=', [O, E])], Here).
chk_rule(rows, Cx, n(_, Src, E, O, Gen, Subs), Here, []) :-
    if_commit(( Gen = [comp(Name, [Rin, O1])], Subs = [atom(Name1)], Name == Name1, teq(Rin, E), teq(O1, O) ),
              ( Cx = pcx(_, _, _, _, AuxMap, Vs, _),
                map_get(AuxMap, Name, MS),
                if_commit(MS = just(Step), true,
                          ( format(string(M), "~sno iteration step ~w", [Here, Name]), pfail(M) )),
                if_commit(Step = comp(aux, [_, Vs1, _, DAux]),
                          ( node(DAux, n(_, ASrc, _, _, _, _)),
                            need(( teq(Vs1, Vs), teq(ASrc, Src) ), Here, "iteration step is for another goal") ),
                          ( wmsg(Here, "bad iteration step", M2), pfail(M2) )) ),
              template_fail(Here)).
chk_rule(disj, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    if_commit(( Src = comp(';', [A, B]), if_commit(is_ite(A), fail, true) ),
              ( sub_node(Subs, 0, Here, TA), sub_node(Subs, 1, Here, TB),
                node(TA, n(_, _, _, Ra, GA, _)), node(TB, n(_, _, _, Rb, GB, _)),
                list_t([Ra, Rb], RL),
                concat_lists([GA, GB, [comp(rows_concat, [RL, O])]], Want),
                gen_is(Gen, Want, Here),
                list_t([E], EL),
                rows_sub(Cx, Subs, 0, A, EL, Ra, Here, XA),
                rows_sub(Cx, Subs, 1, B, EL, Rb, Here, XB),
                fresh_is(Cx, [Ra, Rb], Here, F),
                concat_lists([F, XA, XB], Xs) ),
              ( wmsg(Here, "not a disjunction", M), pfail(M) )).
chk_rule(ite_det, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    ite_parts(Src, MP),
    if_commit(MP = just(C-T-El), true, ( wmsg(Here, "not a commitment", M), pfail(M) )),
    conj_list(C, CGs),
    need(all_det_p(CGs, Cx), Here, "condition is not deterministic built-ins"),
    sub_node(Subs, 0, Here, DT),
    sub_node(Subs, 1, Here, DE),
    node(DT, n(_, _, _, _, GT, _)),
    node(DE, n(_, _, _, _, GE, _)),
    mk_conj(GT, CT),
    mk_conj(GE, CE),
    gen_is(Gen, [comp(if_commit, [C, CT, CE])], Here),
    env_sub(Cx, Subs, 0, T, O, Here, XT),
    env_sub(Cx, Subs, 1, El, O, Here, XE),
    conc(XT, XE, Xs).
chk_rule(ite, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    ite_parts(Src, MP),
    if_commit(MP = just(C-T-El), true, ( wmsg(Here, "not a commitment", M), pfail(M) )),
    sub_node(Subs, 0, Here, DC0),
    sub_node(Subs, 1, Here, DT0),
    sub_node(Subs, 2, Here, DE0),
    node(DC0, n(_, _, _, Rc, GC, _)),
    node(DT0, n(_, _, EnvT, Ot, GT, _)),
    node(DE0, n(_, _, _, Oe, GE, _)),
    if_commit(EnvT = comp('.', [FV, atom('[]')]), FirstV = FV, FirstV = EnvT),
    length(GC, LGC),
    drop(LGC, Gen, After),
    if_commit(( After = [comp(packet_first, [Rc1, Pre, Res]),
                         comp(if_commit, [comp('=', [Res1, atom(none)]), ElseG, ThenG])],
                teq(Rc1, Rc), teq(Res1, Res) ),
              ( take(LGC, Gen, Before),
                need(teq_list(Before, GC), Here, "condition code"),
                conj_list(ElseG, EGs),
                list_t([Pre, Oe], PreOe),
                conc(GE, [comp(rows_concat, [PreOe, O])], WantE),
                need(teq_list(EGs, WantE), Here, "else branch"),
                conj_list(ThenG, TGs),
                list_t([Pre, Ot], PreOt),
                concat_lists([[comp('=', [Res, comp(first, [FirstV])])], GT, [comp(rows_concat, [PreOt, O])]], WantT),
                need(teq_list(TGs, WantT), Here, "then branch"),
                list_t([E], EL),
                rows_sub(Cx, Subs, 0, C, EL, Rc, Here, XC),
                list_t([FirstV], FL),
                rows_sub(Cx, Subs, 1, T, FL, Ot, Here, XT),
                env_sub(Cx, Subs, 2, El, Oe, Here, XE),
                fresh_is(Cx, [Rc, Pre, Res, FirstV, Ot, Oe], Here, F),
                concat_lists([F, XC, XT, XE], Xs) ),
              template_fail(Here)).
chk_rule(neg_det, Cx, n(_, Src, E, O, Gen, _), Here, []) :-
    env_level(Cx, E, Here),
    neg_of(Src, MX),
    if_commit(MX = just(X), true, ( wmsg(Here, "not a negation", M), pfail(M) )),
    conj_list(X, XGs),
    need(all_det_p(XGs, Cx), Here, "negated goal is not deterministic built-ins"),
    list_t([E], EL),
    gen_is(Gen, [comp(if_commit, [X, comp('=', [O, atom('[]')]), comp('=', [O, EL])])], Here).
chk_rule(neg, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    neg_of(Src, MX),
    if_commit(MX = just(X), true, ( wmsg(Here, "not a negation", M), pfail(M) )),
    sub_node(Subs, 0, Here, DX0),
    node(DX0, n(_, _, _, Rg, GX, _)),
    length(GX, LGX),
    drop(LGX, Gen, After),
    list_t([E], EL),
    list_t([Pre, EL], PreEL),
    if_commit(( After = [comp(packet_first, [Rg1, Pre, Res]),
                         comp(if_commit, [comp('=', [Res1, atom(none)]), Yes, No])],
                teq(Rg1, Rg), teq(Res1, Res),
                teq(Yes, comp(rows_concat, [PreEL, O])), teq(No, comp('=', [O, Pre])) ),
              ( take(LGX, Gen, Before),
                need(teq_list(Before, GX), Here, "goal code"),
                rows_sub(Cx, Subs, 0, X, EL, Rg, Here, XS),
                fresh_is(Cx, [Rg, Pre, Res], Here, F),
                conc(F, XS, Xs) ),
              template_fail(Here)).
chk_rule(findall, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    if_commit(Src = comp(findall, [T, X, L]), true, ( wmsg(Here, "source", M), pfail(M) )),
    sub_node(Subs, 0, Here, DX0),
    node(DX0, n(_, _, _, Rg, GX, _)),
    length(GX, LGX),
    drop(LGX, Gen, After),
    list_t([E], EL),
    list_t([Outs, EL], OEL),
    if_commit(( After = [comp(packet_split, [Rg1, Outs, Rows0]),
                         comp(splice_extend, [Rows01, T1, E1, Ls]),
                         comp(if_commit, [comp('=', [L1, Ls1]), Yes, No])],
                teq(Rg1, Rg), teq(Rows01, Rows0), teq(T1, T), teq(E1, E), teq(L1, L), teq(Ls1, Ls),
                teq(Yes, comp(rows_concat, [OEL, O])), teq(No, comp('=', [O, Outs])) ),
              ( take(LGX, Gen, Before),
                need(teq_list(Before, GX), Here, "goal code"),
                rows_sub(Cx, Subs, 0, X, EL, Rg, Here, XS),
                fresh_is(Cx, [Rg, Outs, Rows0, Ls], Here, F),
                conc(F, XS, Xs) ),
              template_fail(Here)).
chk_rule(count, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    if_commit(Src = comp(aggregate_all, [atom(count), X, R]), true, ( wmsg(Here, "source", M), pfail(M) )),
    sub_node(Subs, 0, Here, DX0),
    node(DX0, n(_, _, _, Rg, GX, _)),
    length(GX, LGX),
    drop(LGX, Gen, After),
    list_t([E], EL),
    list_t([Outs, EL], OEL),
    if_commit(( After = [comp(packet_split, [Rg1, Outs, Rows0]),
                         comp(length_det, [Rows01, Cnt]),
                         comp(if_commit, [comp('=', [R1, Cnt1]), Yes, No])],
                teq(Rg1, Rg), teq(Rows01, Rows0), teq(R1, R), teq(Cnt1, Cnt),
                teq(Yes, comp(rows_concat, [OEL, O])), teq(No, comp('=', [O, Outs])) ),
              ( take(LGX, Gen, Before),
                need(teq_list(Before, GX), Here, "goal code"),
                rows_sub(Cx, Subs, 0, X, EL, Rg, Here, XS),
                fresh_is(Cx, [Rg, Outs, Rows0, Cnt], Here, F),
                conc(F, XS, Xs) ),
              template_fail(Here)).
chk_rule(splice, Cx, n(_, Src, E, O, Gen, Subs), Here, Xs) :-
    env_level(Cx, E, Here),
    sub_node(Subs, 0, Here, DSeq0),
    node(DSeq0, n(_, SSeq, ESeq, R, GSeq, _)),
    conj_list(Src, Gs),
    conj_list(SSeq, Grp),
    length(Grp, K),
    drop(K, Gs, Rest),
    take(K, Gs, Front),
    need(( K >= 2, teq_list(Front, Grp) ), Here, "group is not a prefix of the conjunction"),
    need(all_generators_p(Grp, Cx), Here, "a spliced goal is not an output-free generator"),
    maplist(term_var_ids, Grp, GIds),
    need(pairwise_disjoint(GIds), Here, "spliced goals share variables"),
    Cx = pcx(_, _, _, _, _, Vs, _),
    need(teq(ESeq, Vs), Here, "fallback derivation env"),
    if_commit(Gen = [comp(if_commit, [comp(splice_safe, [Pats]), ChainG, SeqG])|RestGen],
              ( conj_list(SeqG, SeqGs),
                need(teq_list(SeqGs, GSeq), Here, "fallback code"),
                conj_list(ChainG, ChainGs),
                check_chain(Cx, Here, Grp, Pats, R, ChainGs, ChainFresh),
                chk(Cx, DSeq0, XSeq),
                splice_rest(Rest, RestGen, Cx, Subs, R, O, Here, XRest),
                fresh_is(Cx, ChainFresh, Here, F2),
                concat_lists([F2, XSeq, XRest], Xs) ),
              template_fail(Here)).

splice_rest(Rest, RestGen, Cx, Subs, R, O, Here, Xs) :-
    if_commit(Rest == [],
              ( need(( teq(R, O), RestGen == [] ), Here, "output"), Xs = [] ),
              ( sub_node(Subs, 1, Here, DR0),
                node(DR0, n(_, _, _, _, GR, _)),
                need(teq_list(RestGen, GR), Here, "rest code"),
                mk_conj(Rest, RC),
                rows_sub(Cx, Subs, 1, RC, R, O, Here, XR),
                fresh_is(Cx, [R], Here, F),
                conc(F, XR, Xs) )).

%  The splice chain: each generator's packet, stop if empty, then splice/2
%  and splice_extend/4.
check_chain(Cx, Here, Grp, Pats, Out, Goals, Fresh) :-
    chain_go(Grp, Goals, [], [], Cx, Here, Pats, Out, Fresh).

chain_go([], Gs, Ps, PatsAcc, Cx, Here, Pats, Out, [Combos]) :-
    Cx = pcx(_, _, _, _, _, Vs, _),
    rev(Ps, RPs),
    findall(comp(cp, [P]), member(P, RPs), CPs),
    list_t(CPs, CPL),
    rev(PatsAcc, RPats),
    list_t(RPats, RPL),
    if_commit(( Gs = [comp(splice, [Cps, Combos]), comp(splice_extend, [Combos1, E1, Pats1, Out1])],
                teq(Cps, CPL), teq(Combos1, Combos), teq(E1, Vs), teq(Pats1, Pats), teq(Out1, Out),
                teq(Pats, RPL) ),
              true,
              ( wmsg(Here, "splice chain end", M), pfail(M) )).
chain_go([G|More], Gs, Ps, PatsAcc, Cx, Here, Pats, Out, Fresh) :-
    chain_step(G, Gs, Cx, Here, Consumed, P, Pat, NewVs),
    drop(Consumed, Gs, After),
    if_commit(( After = [comp(if_commit, [comp('=', [P1, atom('[]')]), comp('=', [Out1, atom('[]')]), Rest])],
                teq(P1, P), teq(Out1, Out) ),
              ( conj_list(Rest, RestGs),
                chain_go(More, RestGs, [P|Ps], [Pat|PatsAcc], Cx, Here, Pats, Out, More1),
                conc(NewVs, More1, Fresh) ),
              ( wmsg(Here, "splice chain test", M), pfail(M) )).

chain_step(G, Gs, Cx, Here, Consumed, P, Pat, NewVs) :-
    Cx = pcx(Defined, _, _, _, _, _, _),
    goal_key(G, MK),
    goal_args(G, As),
    if_commit(( MK = just(member/2), if_commit(ord_memberchk(member/2, Defined), fail, true),
                Gs = [comp(member_cp, [M, L]), comp(cp_rows, [M1, P0])|_],
                As = [X, L1], teq(L1, L), teq(M1, M) ),
              ( Consumed = 2, P = P0, list_t([X], Pat), NewVs = [M, P0] ),
    if_commit(( MK = just(between/3),
                Gs = [comp(between_cp, [Lo, Hi, M]), comp(cp_rows, [M1, P0])|_],
                As = [Lo1, Hi1, X], teq(Lo1, Lo), teq(Hi1, Hi), teq(M1, M) ),
              ( Consumed = 2, P = P0, list_t([X], Pat), NewVs = [M, P0] ),
    if_commit(( MK = just(F/N), ord_memberchk(F/N, Defined), cp_name(F, CF),
                Gs = [comp(CF, QArgs)|_], init_of(QArgs, QI), teq_list(QI, As) ),
              ( last_of(QArgs, LQ), Consumed = 1, P = LQ, list_t(As, Pat), NewVs = [LQ] ),
              ( show_term_q(G, GS), format(string(Msg), "~ssplice chain step for ~s", [Here, GS]), pfail(Msg) )))).

is_ite(T) :-
    if_commit(T = comp('->', [_, _]), true, T = comp('*->', [_, _])).

ite_parts(T, M) :-
    if_commit(T = comp(';', [comp('->', [C, X]), E]), M = just(C-X-E),
    if_commit(T = comp('->', [C, X]), M = just(C-X-atom(fail)),
    if_commit(T = comp(if_commit, [C, X, E]), M = just(C-X-E),
    if_commit(( T = comp(F, [X]), memberchk(F, [once, once_det]) ), M = just(X-atom(true)-atom(fail)),
    if_commit(T = comp(ignore, [X]), M = just(X-atom(true)-atom(true)),
              M = nothing))))).

neg_of(T, M) :-
    if_commit(( T = comp(F, [X]), memberchk(F, ['\\+', not]) ), M = just(X), M = nothing).

%  The fixed equivalences used by rule REWRITE.
rewrite_of(T, M) :-
    if_commit(T = comp(forall, [C, A]), M = just(comp('\\+', [comp(',', [C, comp('\\+', [A])])])),
    if_commit(T = comp(aggregate_all, [comp(bag, [X]), G, R]), M = just(comp(findall, [X, G, R])),
    if_commit(T = comp(decision, [Cases, D]),
              ( static_list(Cases, MC),
                if_commit(( MC = just(Cs), all_pairs(Cs) ),
                          ( rev(Cs, RCs), foldl(decision_fold, RCs, D, G1), M = just(G1) ),
                          M = nothing) ),
    if_commit(( T = comp(call, [G|Extra]), is_var_t(G, false) ), add_args(G, Extra, M),
              M = nothing)))).

defined_here(pcx(Defined, _, _, _, _, _, _), G) :-
    goal_key(G, just(K)),
    ord_memberchk(K, Defined).

is_det_goal_p(pcx(Defined, _, _, _, _, _, _), G) :-
    goal_key(G, just(F/N)),
    key_atom(F, N, KA),
    is_builtin_key(KA, true),
    if_commit(ord_memberchk(F/N, Defined), fail, true),
    nondet_builtin_keys(ND),
    effect_keys(EK),
    control_keys(CK),
    if_commit(memberchk(KA, ['atom_concat/3'|ND]), fail, true),
    if_commit(memberchk(KA, EK), fail, true),
    if_commit(memberchk(KA, CK), fail, true).

all_det_p([], _).
all_det_p([G|Gs], Cx) :-
    is_det_goal_p(Cx, G),
    all_det_p(Gs, Cx).

span_det_p([], _, [], []).
span_det_p([G|Gs], Cx, Bs, Rest) :-
    if_commit(is_det_goal_p(Cx, G),
              ( Bs = [G|Bs1], span_det_p(Gs, Cx, Bs1, Rest) ),
              ( Bs = [], Rest = [G|Gs] )).

is_generator_p(pcx(Defined, Eff, UM, _, _, _, _), G) :-
    goal_key(G, just(K)),
    if_commit(ord_memberchk(K, Defined),
              if_commit(ord_memberchk(K, Eff), fail, true),
              if_commit(K == member/2, UM == false, K == between/3)).

all_generators_p([], _).
all_generators_p([G|Gs], Cx) :-
    is_generator_p(Cx, G),
    all_generators_p(Gs, Cx).

%  effectful_of(+Intermediate, -Keys): predicates that (transitively) write
%  output, computed on the intermediate program.
effectful_of(Inter, Set) :-
    map_pairs(Inter, Pairs),
    maplist(goals_of_pred, Pairs, Calls),
    effect_keys(EK),
    findall(K, ( member(K-Cs, Calls), once_det(( member(F/N, Cs), key_atom(F, N, KA), memberchk(KA, EK) )) ), D0),
    sort(D0, Direct),
    effect_fix(Direct, Calls, Set).

goals_of_pred(K-Cls, K-Calls) :-
    findall(C, ( member(clause(_, B, _), Cls), goals_of(B, Cs), member(C, Cs) ), Calls).

goals_of(T, Ks) :-
    if_commit(( T = comp(Op, As), memberchk(Op, [',', ';', '->', '*->', if_commit, '\\+', not, once, once_det, ignore, forall]) ),
              ( maplist(goals_of, As, KLs), concat_lists(KLs, Ks) ),
    if_commit(T = comp(findall, [_, G, _]), goals_of(G, Ks),
    if_commit(T = comp(aggregate_all, [_, G, _]), goals_of(G, Ks),
    if_commit(( T = comp(call, [G|Extra]), is_var_t(G, false), add_args(G, Extra, just(G1)) ), goals_of(G1, Ks),
              ( goal_key(T, M), if_commit(M = just(K), Ks = [K], Ks = []) ))))).
