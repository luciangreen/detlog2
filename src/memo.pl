/*  memo.pl - memoisation: expand calls into answer tables, and the bridge
    to mnns's optimise.pl.

    For each memoised call, the source program (cuts and choicepoints
    included) is run once with the reference engine, and the complete answer
    packet is written into the converted program as data.  Output written by
    a memoised call is recorded as out(Text) items.  With complete, the
    table covers every call that will be made, the computing code is
    dropped, and a call outside the table is an error (memo_miss/2).

    A memo table maps a key F/N to a list of Pattern-Rows entries.
*/

%  memo_call(+Opts, +Max, +Source, +Goal, +NVars, +Table, -Either)
memo_call(Opts, Max, Src, Goal, NV, Table, E) :-
    goal_key(Goal, MK),
    if_commit(MK = just(F/N),
              ( prog_preds(Src, Preds),
                map_member(Preds, F/N, Has),
                if_commit(Has == true,
                          memo_run(Opts, Max, Src, Goal, NV, F/N, Table, E),
                          ( format(string(M), "memoise: ~w/~d is not defined by the program", [F, N]),
                            E = left(M) )) ),
              E = left("memoise: goal is not callable")).

memo_run(Opts, Max, Src, Goal, NV, Key, Table, E) :-
    goal_args(Goal, As),
    list_t(As, Args),
    with_prelude(Src, P),
    ref_run(Opts, P, Goal, NV, S),
    K is Max + 1,
    show_term_q(Goal, GS),
    memo_collect(K, S, Args, GS, R),
    memo_rows(R, Max, GS, Key, Args, Table, E).

memo_rows(left(M), _, _, _, _, _, left(M)).
memo_rows(right(Rows), Max, GS, Key, Args, Table, E) :-
    findall(x, ( member(Row, Rows), if_commit(Row = comp(out, [_]), fail, true) ), Xs),
    length(Xs, NR),
    if_commit(NR > Max,
              ( format(string(M), "memoise: ~s has more than ~d answers; raise --max-answers if the packet is finite", [GS, Max]),
                E = left(M) ),
              ( map_find(Table, Key, [], Old),
                conc(Old, [Args-Rows], New),
                map_put(Key, New, Table, Table1),
                E = right(Table1) )).

memo_collect(K, S, Args, GS, R) :-
    if_commit(K =:= 0,
              R = right([]),
              ( force(S, F), memo_collect_f(F, K, Args, GS, R) )).

memo_collect_f([], _, _, _, right([])).
memo_collect_f([Ev|T], K, Args, GS, R) :-
    memo_collect_ev(Ev, T, K, Args, GS, R).

memo_collect_ev(ans(St), T, K, Args, GS, R) :-
    resolve(Args, St, A),
    K1 is K - 1,
    memo_collect(K1, T, Args, GS, R1),
    memo_cons(R1, A, R).
memo_collect_ev(out(O), T, K, Args, GS, R) :-
    atom_string(OA, O),
    memo_collect(K, T, Args, GS, R1),
    memo_cons(R1, comp(out, [atom(OA)]), R).
memo_collect_ev(err(E), _, _, _, GS, left(M)) :-
    format(string(M), "memoise: ~s raised: ~s", [GS, E]).

memo_cons(left(M), _, left(M)).
memo_cons(right(Xs), X, right([X|Xs])).

%  add_memo_tables(+Complete, +Table, +Converted, -Program, -Steps)
add_memo_tables(Complete, Table, Conv, P, Steps) :-
    map_pairs(Table, Pairs),
    foldl(add_memo(Complete), Pairs, Conv-[], P-Steps).

add_memo(Complete, (F/N)-Entries, P0-Steps0, P-Steps) :-
    cp_name(F, CF),
    N1 is N + 1,
    Key = CF/N1,
    atom_concat(CF, '__compute', CN),
    ComputeKey = CN/N1,
    head_vars_a(N, Args),
    RowsV = var(N, 'Rows'),
    rename_entries(N1, Entries, TableT),
    list_t(Args, ArgsL),
    if_commit(Complete == true,
              Fallback = comp(memo_miss, [comp('/', [atom(F), int(N)]), ArgsL]),
              ( conc(Args, [RowsV], CArgs), Fallback = comp(CN, CArgs) )),
    conc(Args, [RowsV], HArgs),
    max_var_id(TableT, MT),
    NV is MT + N + 2,
    MemoClause = clause(comp(CF, HArgs),
                        comp(if_commit, [comp(memo_lookup, [ArgsL, TableT, RowsV]), atom(true), Fallback]),
                        NV),
    P0 = prog(Preds, Order, Ds),
    map_find(Preds, Key, [], Old),
    maplist(compute_head(CN), Old, Renamed),
    map_put(Key, [MemoClause], Preds, Preds1),
    if_commit(( Complete == false, Renamed \== [] ),
              ( map_put(ComputeKey, Renamed, Preds1, Preds2), KeepCompute = true ),
              ( Preds2 = Preds1, KeepCompute = false )),
    map_member(Preds, Key, Had),
    if_commit(Had == true, Order1 = Order, conc(Order, [Key], Order1)),
    if_commit(KeepCompute == true,
              foldl(insert_compute(Key, ComputeKey), Order1, [], Order2R),
              rev(Order1, Order2R)),
    rev(Order2R, Order2),
    P = prog(Preds2, Order2, Ds),
    if_commit(Complete == true, CA = atom(true), CA = atom(false)),
    MemoClause = clause(MH, MB, _),
    conc(Steps0, [comp(memo_table, [comp('/', [atom(F), int(N)]), CA, comp(':-', [MH, MB])])], Steps).

compute_head(CN, clause(H, B, NV), clause(H1, B, NV)) :-
    if_commit(H = comp(_, As), H1 = comp(CN, As), H1 = H).

insert_compute(Key, ComputeKey, K, Acc, Acc1) :-
    if_commit(K == Key, Acc1 = [ComputeKey, Key|Acc], Acc1 = [K|Acc]).

%  Give every entry its own variables, numbered from Start.
rename_entries(Start, Entries, T) :-
    empty_state(Start, St0),
    foldl(rename_entry, Entries, []-St0, Items-_),
    list_t(Items, T).

rename_entry(Pat-Rows, Acc-St, Acc1-St1) :-
    list_t(Rows, RL),
    list_t([Pat, RL], E),
    copy_term_st(St, E, C, St1),
    conc(Acc, [C], Acc1).

% ---------------------------------------------------------------------------
% The mnns bridge: mnns's optimise.pl runs its proof-checked stages (PLOp,
% AIOC simplification, its own Detlog stage) on a Prolog file; detlog2 then
% converts the result.

%  find_mnns_dir(+MaybeGiven, -Either): --mnns DIR, else $MNNS_DIR, else
%  ../mnns, else ./mnns.
find_mnns_dir(Given, E) :-
    if_commit(Given = just(G), C1 = [G], C1 = []),
    if_commit(getenv('MNNS_DIR', Env), C2 = [Env], C2 = []),
    concat_lists([C1, C2, ["../mnns", "mnns"]], Cands),
    if_commit(( member(D, Cands), format(atom(F), "~w/optimise.pl", [D]), exists_file(F) ),
              E = right(D),
              ( maplist(quoted_str, Cands, QCs), atomic_list_concat(QCs, ',', QA),
                format(string(M), "mnns not found (tried [~w]); clone https://github.com/luciangreen/mnns and pass --mnns DIR", [QA]),
                E = left(M) )).

quoted_str(S, Q) :-
    format(string(Q), "\"~w\"", [S]).

%  run_mnns_optimise(+Dir, +In, +Out, -Either): swipl optimise.pl -- IN OUT.
run_mnns_optimise(Dir, In, Out, E) :-
    format(atom(Opt), "~w/optimise.pl", [Dir]),
    catch(( process_create(path(swipl), [Opt, '--', In, Out],
                           [stdout(pipe(O)), stderr(pipe(Er)), process(Pid)]),
            read_string(O, _, OS), read_string(Er, _, ES), close(O), close(Er),
            process_wait(Pid, Status),
            mnns_result(Status, OS, ES, E) ),
          X,
          ( format(string(M), "could not run swipl (SWI-Prolog is needed for the mnns pass): ~w", [X]),
            E = left(M) )).

mnns_result(Status, OS, ES, E) :-
    if_commit(Status == exit(0),
              ( split_string(OS, "", " \n\r\t", [T]), E = right(T) ),
              ( string_concat(OS, ES, All), split_string(All, "", " \n\r\t", [T]), E = left(T) )).
