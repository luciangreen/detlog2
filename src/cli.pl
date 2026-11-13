/*  cli.pl - the detlog2 commands.

    Commands write to the current output and to user_error.  die/1 writes
    "detlog2: Message" to user_error and throws cli_exit(1); other exit
    codes are thrown as cli_exit(Code).
*/

usage_text(T) :-
    atomic_list_concat([
      "detlog2 - a choicepointless, cutless Prolog interpreter and a proof-carrying Detlog converter",
      "",
      "  detlog2 run FILE QUERY [--max N] [--det]      run on the cutless interpreter",
      "  detlog2 ref FILE QUERY [--max N]              run with ordinary cut semantics (reference)",
      "  detlog2 convert FILE [-o OUT] [--no-splice]   cuts -> if_commit, choicepoints -> splices;",
      "                                                writes OUT and its proof OUT.proof",
      "  detlog2 proof-check FILE OUT OUT.proof        check a conversion proof independently",
      "  detlog2 packets FILE QUERY                    convert, then run the query as one packet",
      "  detlog2 check FILE QUERY... [--max N]         convert, check the proof and choicepoint-freedom,",
      "                                                compare answers and output with the source",
      "  detlog2 memoise FILE --goal G ... [--complete] [-o OUT] [--check Q ...]",
      "                                                expand calls into answer tables",
      "  detlog2 unfold FILE [--max N] [-o OUT] [--check Q ...]",
      "                                                unfold every pure predicate into its answer table,",
      "                                                then replace each table by an S2A loop (no choicepoints)",
      "  detlog2 mnns FILE [--mnns DIR] [-o OUT] [--check Q ...]",
      "                                                rewrite with mnns optimise.pl, then convert",
      "",
      "Every conversion is proof-gated: nothing is written unless the proof checker accepts its proof.",
      ""], '\n', T).

die(Msg) :-
    format(user_error, "detlog2: ~w~n", [Msg]),
    throw(cli_exit(1)).

% ---------------------------------------------------------------------------
% Flags: flags(Max, Det, Out, Splice, Goals, Checks, Complete, Mnns, Positional)

default_flags(flags(50, false, nothing, true, [], [], false, nothing, [])).

fl_max(flags(M, _, _, _, _, _, _, _, _), M).
fl_det(flags(_, D, _, _, _, _, _, _, _), D).
fl_out(flags(_, _, O, _, _, _, _, _, _), O).
fl_splice(flags(_, _, _, S, _, _, _, _, _), S).
fl_goals(flags(_, _, _, _, G, _, _, _, _), G).
fl_checks(flags(_, _, _, _, _, C, _, _, _), C).
fl_complete(flags(_, _, _, _, _, _, C, _, _), C).
fl_mnns(flags(_, _, _, _, _, _, _, M, _), M).
fl_pos(flags(_, _, _, _, _, _, _, _, P), P).

parse_flags(Args, E) :-
    default_flags(F0),
    catch(( flags_go(Args, F0, F), E = right(F) ), flag_error(M), E = left(M)).

flags_go([], flags(M, D, O, S, G, C, Co, Mn, P),
         flags(M, D, O, S, G1, C1, Co, Mn, P1)) :-
    rev(G, G1),
    rev(C, C1),
    rev(P, P1).
flags_go([A|As], F0, F) :-
    atom_string(A, AS),
    flag_kind(AS, As, K),
    flag_step(K, AS, As, F0, F).

flag_kind(AS, As, K) :-
    if_commit(( memberchk(AS, ["--max", "--max-answers"]), As = [_|_] ), K = max,
    if_commit(AS == "--det", K = det,
    if_commit(( AS == "-o", As = [_|_] ), K = out,
    if_commit(AS == "--no-splice", K = nosplice,
    if_commit(( AS == "--goal", As = [_|_] ), K = goal,
    if_commit(( AS == "--check", As = [_|_] ), K = check,
    if_commit(AS == "--complete", K = complete,
    if_commit(( AS == "--mnns", As = [_|_] ), K = mnns,
    if_commit(sub_string(AS, 0, 2, _, "--"), K = unknown,
              K = positional))))))))).

flag_step(max, _, [N|R], flags(_, D, O, S, G, C, Co, Mn, P), F) :-
    atom_number(N, M),
    flags_go(R, flags(M, D, O, S, G, C, Co, Mn, P), F).
flag_step(det, _, R, flags(M, _, O, S, G, C, Co, Mn, P), F) :-
    flags_go(R, flags(M, true, O, S, G, C, Co, Mn, P), F).
flag_step(out, _, [X|R], flags(M, D, _, S, G, C, Co, Mn, P), F) :-
    atom_string(X, XS),
    flags_go(R, flags(M, D, just(XS), S, G, C, Co, Mn, P), F).
flag_step(nosplice, _, R, flags(M, D, O, _, G, C, Co, Mn, P), F) :-
    flags_go(R, flags(M, D, O, false, G, C, Co, Mn, P), F).
flag_step(goal, _, [X|R], flags(M, D, O, S, G, C, Co, Mn, P), F) :-
    atom_string(X, XS),
    flags_go(R, flags(M, D, O, S, [XS|G], C, Co, Mn, P), F).
flag_step(check, _, [X|R], flags(M, D, O, S, G, C, Co, Mn, P), F) :-
    atom_string(X, XS),
    flags_go(R, flags(M, D, O, S, G, [XS|C], Co, Mn, P), F).
flag_step(complete, _, R, flags(M, D, O, S, G, C, _, Mn, P), F) :-
    flags_go(R, flags(M, D, O, S, G, C, true, Mn, P), F).
flag_step(mnns, _, [X|R], flags(M, D, O, S, G, C, Co, _, P), F) :-
    atom_string(X, XS),
    flags_go(R, flags(M, D, O, S, G, C, Co, just(XS), P), F).
flag_step(unknown, AS, _, _, _) :-
    format(string(M), "unknown option ~s", [AS]),
    throw(flag_error(M)).
flag_step(positional, AS, R, flags(M, D, O, S, G, C, Co, Mn, P), F) :-
    flags_go(R, flags(M, D, O, S, G, C, Co, Mn, [AS|P]), F).

% ---------------------------------------------------------------------------

cli([]) :-
    usage_text(T),
    write(T).
cli([Cmd|Rest]) :-
    if_commit(Cmd == help,
              ( usage_text(T), write(T) ),
              ( parse_flags(Rest, E),
                cli_flags(E, Cmd) )).

cli_flags(left(M), _) :-
    die(M).
cli_flags(right(Fl), Cmd) :-
    fl_pos(Fl, Pos),
    atom_string(Cmd, CS),
    dispatch(CS, Pos, Fl).

load_program(Path, P) :-
    catch(read_file_to_string(Path, Src, []), _, fail_read(Path)),
    parse_program(Src, R),
    loaded(R, Path, P).

fail_read(Path) :-
    format(string(M), "~s: cannot read the file", [Path]),
    die(M).

loaded(right(P), _, P).
loaded(left(E), Path, _) :-
    format(string(M), "~s: ~s", [Path, E]),
    die(M).

parse_q(Q, G, Vs, NV) :-
    parse_query(Q, E),
    parsed_q(E, G, Vs, NV).

parsed_q(right(G-Vs-NV), G, Vs, NV).
parsed_q(left(E), _, _, _) :-
    format(string(M), "query: ~s", [E]),
    die(M).

dispatch(Cmd, Pos, Fl) :-
    length(Pos, N),
    format(atom(Key), "~s/~d", [Cmd, N]),
    if_commit(command(Key, Pos, Fl, Run),
              call(Run),
              if_commit(( Cmd == "check", N >= 2 ),
                        ( Pos = [File|Qs], check_command(File, Qs, Fl) ),
                        ( usage_text(U), string_concat("bad arguments\n", U, M), die(M) ))).

:- relation(command/4).

command('run/2', [File, Q], Fl, run_command(File, Q, Fl)).
command('ref/2', [File, Q], Fl, ref_command(File, Q, Fl)).
command('convert/1', [File], Fl, convert_command(File, Fl)).
command('proof-check/3', [File, Out, Proof], Fl, proof_check_command(File, Out, Proof, Fl)).
command('packets/2', [File, Q], Fl, packets_command(File, Q, Fl)).
command('memoise/1', [File], Fl, memoise_command(File, Fl)).
command('memoize/1', [File], Fl, memoise_command(File, Fl)).
command('mnns/1', [File], Fl, mnns_command(File, Fl)).
command('unfold/1', [File], Fl, unfold_command(File, Fl)).

run_command(File, Q, Fl) :-
    load_program(File, P),
    parse_q(Q, G, Vs, NV),
    fl_det(Fl, Det),
    fl_max(Fl, Max),
    with_prelude(P, P1),
    run_goal(opts(100000, Det, []), P1, G, NV, S),
    print_answers(Max, Vs, S).

ref_command(File, Q, Fl) :-
    load_program(File, P),
    parse_q(Q, G, Vs, NV),
    fl_max(Fl, Max),
    with_prelude(P, P1),
    default_options(Opts),
    ref_run(Opts, P1, G, NV, S),
    print_answers(Max, Vs, S).

show_bindings([], "true.").
show_bindings([B|Bs], S) :-
    maplist(binding_text, [B|Bs], Ts),
    atomic_list_concat(Ts, ', ', A),
    format(string(S), "~w.", [A]).

binding_text(N-T, S) :-
    show_term_q(T, TS),
    format(string(S), "~w = ~s", [N, TS]).

%  A query variable that is still unbound and unaliased is not shown.
unbound_self(V, T, B) :-
    test(( V = var(I, _), T = var(J, _), I =:= J ), B).

print_answers(Max, Vs, S) :-
    named_vars_only(Vs, Named),
    answers_loop(0, Max, Named, S).

named_vars_only([], []).
named_vars_only([N-V|Vs], Out) :-
    named_vars_only(Vs, Rest),
    if_commit(sub_atom(N, 0, 1, _, '_'), Out = Rest, Out = [N-V|Rest]).

answers_loop(K, Max, Named, S) :-
    if_commit(K >= Max,
              format("% stopped after ~d answers~n", [Max]),
              ( force(S, F), answers_f(F, K, Max, Named) )).

answers_f([], K, _, _) :-
    if_commit(K =:= 0, format("false.~n"), true).
answers_f([E|R], K, Max, Named) :-
    answers_ev(E, R, K, Max, Named).

answers_ev(out(T), R, K, Max, Named) :-
    write(T),
    flush_output,
    answers_loop(K, Max, Named, R).
answers_ev(err(E), _, _, _, _) :-
    format("error: ~s~n", [E]),
    throw(cli_exit(3)).
answers_ev(ans(St), R, K, Max, Named) :-
    shown_bindings(Named, St, Bs),
    show_bindings(Bs, Txt),
    format("~s~n", [Txt]),
    K1 is K + 1,
    answers_loop(K1, Max, Named, R).

shown_bindings([], _, []).
shown_bindings([N-V|Vs], St, Out) :-
    resolve(V, St, T),
    unbound_self(V, T, B),
    shown_bindings(Vs, St, Rest),
    shown_binding(B, N, T, Rest, Out).

shown_binding(true, _, _, Rest, Rest).
shown_binding(false, N, T, Rest, [N-T|Rest]).

% ---------------------------------------------------------------------------
% Conversion commands

conv_opts(Fl, copts(S, [], nothing)) :-
    fl_splice(Fl, S).

%  Convert and check the proof; nothing unproved is returned.
proved_conversion(Opts, Original, P, E) :-
    convert_program(Opts, P, CE),
    proved_(CE, Opts, Original, P, E).

proved_(left(M), _, _, _, left(S)) :-
    string_concat("conversion failed: ", M, S).
proved_(right(Conv), Opts, Original, P, E) :-
    Conv = cres(CP, _, Proof),
    co_external(Opts, Ext),
    check_proof(pctx(P, Ext, Original), Proof, CP, PE),
    proved_check(PE, Conv, E).

proved_check(left(M), _, left(S)) :-
    string_concat("proof rejected: ", M, S).
proved_check(right(Report), Conv, right(Conv-Report)).

either_or_die(left(M), _) :-
    die(M).
either_or_die(right(X), X).

convert_command(File, Fl) :-
    load_program(File, P),
    conv_opts(Fl, Opts),
    proved_conversion(Opts, P, P, E),
    either_or_die(E, cres(CP, Events, Proof)-Report),
    conc(Events, Report, Evs),
    write_converted(Fl, File, Evs, CP, Proof).

proof_check_command(File, Out, ProofFile, _) :-
    load_program(File, P),
    load_program(Out, Conv),
    read_file_to_string(ProofFile, Txt, []),
    proof_from_text(Txt, PE),
    if_commit(PE = right(Steps), true,
              ( PE = left(M0), format(string(M), "~s: ~s", [ProofFile, M0]), die(M) )),
    check_proof(pctx(P, [], P), Steps, Conv, CE),
    if_commit(CE = right(Report),
              forall_lines(Report),
              ( CE = left(M1), string_concat("proof rejected: ", M1, M2), die(M2) )).

forall_lines([]).
forall_lines([L|Ls]) :-
    format("~s~n", [L]),
    forall_lines(Ls).

report_check(Conv) :-
    check_deterministic(Conv, Problems),
    if_commit(Problems == [],
              true,
              ( format(user_error, "choicepoint check FAILED:~n", []),
                report_problem_lines(Problems),
                throw(cli_exit(2)) )).

report_problem_lines([]).
report_problem_lines([P|Ps]) :-
    format(user_error, "  ~s~n", [P]),
    report_problem_lines(Ps).

write_converted(Fl, Source, Events, Prog, Steps) :-
    report_check(Prog),
    findall(L, ( member(E, Events), format(string(L), "% ~s~n", [E]) ), ELs),
    atomic_list_concat(ELs, EA),
    show_program(Prog, PT),
    format(string(Text), "% Detlog code generated by detlog2 from ~s~n% No cuts and no choicepoints: every predicate succeeds exactly once and~n% returns its answer packet (rows and out(Text) items) in its last argument.~n% Run it with: detlog2 run --det FILE 'p__cp(Args..., Packet)'~n%~n~w~n~s",
           [Source, EA, PT]),
    fl_out(Fl, MO),
    write_converted_to(MO, Text, Steps).

write_converted_to(nothing, Text, _) :-
    write(Text).
write_converted_to(just(O), Text, Steps) :-
    write_file(O, Text),
    proof_to_text(Steps, PT),
    string_concat(O, ".proof", PO),
    write_file(PO, PT),
    format(user_error, "wrote ~s and ~s~n", [O, PO]).

write_file(Path, Text) :-
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]), write(S, Text), close(S)).

packets_command(File, Q, Fl) :-
    load_program(File, P),
    parse_q(Q, G, Vs, NV),
    pairs_values(Vs, Vars),
    add_query_clause(G, Vars, NV, P, P1, QK),
    conv_opts(Fl, copts(S, Ext, _)),
    proved_conversion(copts(S, Ext, just([QK])), P, P1, E),
    either_or_die(E, cres(CP, _, _)-Report),
    report_check(CP),
    forall_err_lines(Report),
    length(Vs, K),
    K1 is K - 1,
    findall(var(I, Nm), ( between(0, K1, I), format(atom(Nm), "V~d", [I]) ), QVars),
    RowsV = var(K, 'Rows'),
    conc(QVars, [RowsV], Args),
    cp_name('$query', QN),
    N1 is K + 1,
    run_goal(opts(100000, true, []), CP, comp(QN, Args), N1, Stream),
    pairs_keys(Vs, Names),
    packets_loop(Stream, RowsV, Names).

forall_err_lines([]).
forall_err_lines([L|Ls]) :-
    format(user_error, "~s~n", [L]),
    forall_err_lines(Ls).

packets_loop(S, RowsV, Names) :-
    force(S, F),
    packets_f(F, RowsV, Names).

packets_f([], _, _).
packets_f([E|R], RowsV, Names) :-
    packets_ev(E, RowsV, Names),
    packets_loop(R, RowsV, Names).

packets_ev(out(T), _, _) :-
    write(T).
packets_ev(err(E), _, _) :-
    format("error: ~s~n", [E]).
packets_ev(ans(St), RowsV, Names) :-
    resolve(RowsV, St, Items),
    show_term_q(Items, IS),
    format("packet: cp(~s)~n", [IS]),
    term_to_list(Items, St, MI),
    if_commit(MI = just(Is),
              ( maplist(resolve_in(St), Is, RIs),
                findall(R, ( member(R, RIs), if_commit(R = comp(out, [_]), fail, true) ), Rows),
                maplist(packet_item(St, Names), RIs),
                if_commit(Rows == [], format("false.~n"), true) ),
              format("false.~n")).

packet_item(St, Names, It) :-
    if_commit(It = comp(out, [atom(T)]),
              write(T),
              ( term_to_list(It, St, MV),
                if_commit(MV = just(Vals),
                          ( pairs_keys_values(Bs, Names, Vals), show_bindings(Bs, Txt), format("~s~n", [Txt]) ),
                          true) )).

check_command(File, Qs, Fl) :-
    load_program(File, P),
    maplist(check_query(Fl, P), Qs, Oks),
    if_commit(memberchk(false, Oks),
              throw(cli_exit(1)),
              format("all checks passed~n")).

check_query(Fl, P, Q, Ok) :-
    parse_q(Q, G, Vs, NV),
    pairs_values(Vs, Vars),
    add_query_clause(G, Vars, NV, P, P1, QK),
    conv_opts(Fl, copts(S, Ext, _)),
    proved_conversion(copts(S, Ext, just([QK])), P, P1, E),
    check_query_(E, Fl, P, G, Vars, NV, Q, Ok).

check_query_(left(M), _, _, _, _, _, Q, false) :-
    format("FAIL ~s~n  ~s~n", [Q, M]).
check_query_(right(cres(CP, _, _)-Report), Fl, P, G, Vars, NV, Q, Ok) :-
    fl_max(Fl, Max),
    default_options(Opts),
    source_outcome(Opts, Max, P, G, Vars, NV, Src),
    length(Vars, K),
    converted_outcome(Opts, Max, CP, K, Out),
    check_deterministic(CP, Problems),
    report_outcome(Q, Report, Problems, Src, Out, Ok).

report_outcome(Q, Report, Problems, Src, Out, Good) :-
    Src = outcome(SA, SO, SE, _),
    Out = outcome(OA, OO, OE, _),
    test(( SA == OA, OE == nothing ), SameAnswers),
    test(SO == OO, SameOutput),
    test(( Problems == [], SameAnswers == true, SameOutput == true, SE == nothing ), Good),
    if_commit(Good == true, Tag = "ok   ", Tag = "FAIL "),
    format("~s~s~n", [Tag, Q]),
    report_problems(Problems),
    if_commit(Good == true,
              ( forall_indented(Report),
                length(OA, NA),
                format("  ~d answer(s) and the output, identical and in the same order~n", [NA]) ),
              ( format(" source (cut semantics):~n"),
                show_outcome(Src, SS), write(SS),
                format(" converted (choicepoint-free):~n"),
                show_outcome(Out, OS), write(OS) )).

report_problems([]).
report_problems([P|Ps]) :-
    format("  choicepoint check: ~s~n", [P]),
    report_problems(Ps).

forall_indented([]).
forall_indented([L|Ls]) :-
    format("  ~s~n", [L]),
    forall_indented(Ls).

memoise_command(File, Fl) :-
    load_program(File, P),
    fl_goals(Fl, Goals),
    if_commit(Goals == [], die("memoise: give at least one --goal"), true),
    fl_max(Fl, Max),
    default_options(Opts),
    map_empty(T0),
    foldl(memo_goal(Opts, Max, P), Goals, T0, Table),
    map_keys(Table, MemoKeys),
    fl_complete(Fl, Complete),
    if_commit(Complete == true, Ext = MemoKeys, Ext = []),
    if_commit(Complete == true, drop_preds(MemoKeys, P, P1), P1 = P),
    memo_build(Fl, Complete, Ext, Table, P, MemoKeys, P1, E),
    either_or_die(E, cres(_, CEvs, _)-MemoProg-Steps-Report),
    map_pairs(Table, TPairs),
    findall(L, ( member((F/N)-Es, TPairs), length(Es, LE),
                 if_commit(Complete == true, Sfx = ", complete", Sfx = ""),
                 format(string(L), "memoised(~w/~d, ~d call pattern(s)~s)", [F, N, LE, Sfx]) ), MEvs),
    concat_lists([CEvs, MEvs, Report], Events),
    write_converted(Fl, File, Events, MemoProg, Steps),
    fl_checks(Fl, Checks),
    maplist(memo_check(Fl, Complete, Ext, Table, P, MemoKeys, P1), Checks, Oks),
    if_commit(memberchk(false, Oks), throw(cli_exit(1)), true).

memo_goal(Opts, Max, P, GS, T0, T) :-
    parse_q(GS, G, _, NV),
    memo_call(Opts, Max, P, G, NV, T0, E),
    either_or_die(E, T).

memo_build(Fl, Complete, Ext, Table, Orig, Roots, Prog, E) :-
    fl_splice(Fl, S),
    convert_program(copts(S, Ext, just(Roots)), Prog, CE),
    if_commit(CE = right(Conv),
              ( Conv = cres(CP, _, Proof),
                add_memo_tables(Complete, Table, CP, MemoProg, MemoSteps),
                conc(Proof, MemoSteps, Steps),
                check_proof(pctx(Prog, Ext, Orig), Steps, MemoProg, PE),
                if_commit(PE = right(Report),
                          E = right(Conv-MemoProg-Steps-Report),
                          ( PE = left(M), string_concat("proof rejected: ", M, M1), E = left(M1) )) ),
              ( CE = left(M), string_concat("conversion failed: ", M, M1), E = left(M1) )).

memo_check(Fl, Complete, Ext, Table, P, MemoKeys, P1, Q, Ok) :-
    parse_q(Q, G, Vs, NV),
    pairs_values(Vs, Vars),
    add_query_clause(G, Vars, NV, P1, PQ, QK),
    memo_build(Fl, Complete, Ext, Table, P, [QK|MemoKeys], PQ, E),
    if_commit(E = right(_-Prog-_-Rep),
              ( fl_max(Fl, Max), default_options(Opts),
                source_outcome(Opts, Max, P, G, Vars, NV, Src),
                length(Vars, K),
                converted_outcome(Opts, Max, Prog, K, Out),
                check_deterministic(Prog, Problems),
                report_outcome(Q, Rep, Problems, Src, Out, Ok) ),
              ( E = left(M), format("FAIL ~s: ~s~n", [Q, M]), Ok = false )).

drop_preds(Keys, P, P1) :-
    program_clauses(P, KCs),
    findall(C, ( member(K-Cs, KCs), if_commit(memberchk(K, Keys), fail, true), member(C, Cs) ), Cls),
    program_from_clauses(Cls, P1).

mnns_command(File, Fl) :-
    fl_mnns(Fl, MG),
    find_mnns_dir(MG, DE),
    either_or_die(DE, Dir),
    tmp_file(detlog2_mnns, Tmp),
    string_concat(Tmp, "_out.pl", Mid),
    load_program(File, Orig),
    run_mnns_optimise(Dir, File, Mid, R),
    mnns_input(R, Mid, Orig, P, Events),
    conv_opts(Fl, Opts),
    proved_conversion(Opts, P, P, E),
    either_or_die(E, cres(CP, CEvs, Proof)-Report),
    concat_lists([Events, CEvs, Report], AllEvs),
    write_converted(Fl, File, AllEvs, CP, Proof),
    fl_checks(Fl, Checks),
    maplist(mnns_check(Fl, Orig, P), Checks, Oks),
    if_commit(memberchk(false, Oks), throw(cli_exit(1)), true).

mnns_input(right(Report), Mid, _, P, [E1, "detlog2's proof below is relative to the mnns output"]) :-
    format(user_error, "mnns: ~s~n", [Report]),
    load_program(Mid, P),
    delete_file(Mid),
    format(string(E1), "mnns optimise.pl (its rewrites are proved by mnns's own checker): ~s", [Report]).
mnns_input(left(Err), _, Orig, Orig, [E1]) :-
    format(user_error, "mnns pass not applied: ~s~n", [Err]),
    split_string(Err, "\n", "", [First|_]),
    format(string(E1), "mnns optimise.pl not applied: ~s", [First]).

mnns_check(Fl, Orig, P, Q, Ok) :-
    parse_q(Q, G, Vs, NV),
    pairs_values(Vs, Vars),
    add_query_clause(G, Vars, NV, P, PQ, QK),
    conv_opts(Fl, copts(S, Ext, _)),
    proved_conversion(copts(S, Ext, just([QK])), P, PQ, E),
    if_commit(E = right(cres(CP, _, _)-Rep),
              ( fl_max(Fl, Max), default_options(Opts),
                source_outcome(Opts, Max, Orig, G, Vars, NV, Src),
                length(Vars, K),
                converted_outcome(Opts, Max, CP, K, Out),
                check_deterministic(CP, Problems),
                report_outcome(Q, Rep, Problems, Src, Out, Ok) ),
              ( E = left(M), format("FAIL ~s: ~s~n", [Q, M]), Ok = false )).

% ---------------------------------------------------------------------------
% unfold: answer tables of pure predicates, as S2A loops (src/unfold.pl)

unfold_command(File, Fl) :-
    load_program(File, P),
    unfold_max(Fl, Max),
    unfold_tables(P, Max, Entries, UEvs),
    pairs_keys(Entries, Keys0),
    sort(Keys0, Keys),
    drop_preds(Keys, P, P1),
    unfold_build(Fl, Keys, Entries, P, P1, E),
    either_or_die(E, cres(_, CEvs, _)-Prog-Steps-Report),
    concat_lists([UEvs, CEvs, Report], Events),
    write_converted(Fl, File, Events, Prog, Steps),
    fl_checks(Fl, Checks),
    maplist(unfold_check(Fl, Keys, Entries, P, P1), Checks, Oks),
    if_commit(memberchk(false, Oks), throw(cli_exit(1)), true).

%  The row limit: --max N, or 1000 when --max is not given.
unfold_max(Fl, Max) :-
    fl_max(Fl, M0),
    default_flags(D),
    fl_max(D, MD),
    if_commit(M0 =:= MD, Max = 1000, Max = M0).

%  unfold_tables(+Program, +Max, -Entries, -Events): Key-Spec for every pure
%  predicate whose most general goal is a finite table of ground answers.
unfold_tables(P, Max, Entries, Events) :-
    pure_preds(P, Pure),
    prog_order(P, Order),
    foldl(unfold_pred(P, Max, Pure), Order, []-[], Entries-Events).

unfold_pred(P, Max, Pure, F/N, E0-V0, E-V) :-
    if_commit(ord_memberchk(F/N, Pure),
              ( general_table(P, Max, F/N, TE), unfold_table(TE, F/N, E0-V0, E-V) ),
              ( format(string(L), "kept ~w/~d: not pure (a cut, negation, if-then-else, type test or output, or a call to such a predicate)", [F, N]),
                E = E0, conc(V0, [L], V) )).

unfold_table(left(Why), F/N, E0-V0, E0-V) :-
    format(string(L), "kept ~w/~d: not unfolded: ~s", [F, N, Why]),
    conc(V0, [L], V).
unfold_table(right(Rows), F/N, E0-V0, E-V) :-
    s2a_spec(N, Rows, Spec),
    length(Rows, K),
    spec_text(N, Spec, T),
    if_commit(K =:= 1, RW = "row", RW = "rows"),
    format(string(L), "unfolded ~w/~d: ~d ~s; S2A loop ~s", [F, N, K, RW, T]),
    conc(E0, [(F/N)-Spec], E),
    conc(V0, [L], V).

unfold_build(Fl, Keys, Entries, Orig, Prog, E) :-
    fl_splice(Fl, S),
    convert_program(copts(S, Keys, nothing), Prog, CE),
    if_commit(CE = right(Conv),
              ( Conv = cres(CP, _, Proof),
                add_s2a_tables(Entries, CP, UProg, S2ASteps),
                conc(Proof, S2ASteps, Steps),
                check_proof(pctx(Prog, Keys, Orig), Steps, UProg, PE),
                if_commit(PE = right(Report),
                          E = right(Conv-UProg-Steps-Report),
                          ( PE = left(M), string_concat("proof rejected: ", M, M1), E = left(M1) )) ),
              ( CE = left(M), string_concat("conversion failed: ", M, M1), E = left(M1) )).

unfold_check(Fl, Keys, Entries, P, P1, Q, Ok) :-
    parse_q(Q, G, Vs, NV),
    pairs_values(Vs, Vars),
    add_query_clause(G, Vars, NV, P1, PQ, _),
    unfold_build(Fl, Keys, Entries, P, PQ, E),
    if_commit(E = right(_-Prog-_-Rep),
              ( fl_max(Fl, Max), default_options(Opts),
                source_outcome(Opts, Max, P, G, Vars, NV, Src),
                length(Vars, K),
                converted_outcome(Opts, Max, Prog, K, Out),
                check_deterministic(Prog, Problems),
                report_outcome(Q, Rep, Problems, Src, Out, Ok) ),
              ( E = left(M), format("FAIL ~s: ~s~n", [Q, M]), Ok = false )).
