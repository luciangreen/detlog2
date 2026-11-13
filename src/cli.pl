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
