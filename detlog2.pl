/*  detlog2.pl - the detlog2 command line, in cut-free, choicepoint-free
    Prolog.

    swipl detlog2.pl COMMAND ARGS...          run from source
    swipl -o build/detlog2 -c detlog2.pl      build a saved state, then
    build/detlog2 COMMAND ARGS...

    The Haskell version this was ported from is in haskell/.
*/

:- use_module(src/detlog_runtime).

relation(_).            % :- relation(Name/Arity) marks a relation (tools/cutfree.pl)

:- ensure_loaded(src/term).
:- ensure_loaded(src/stream).
:- ensure_loaded(src/reader).
:- ensure_loaded(src/pretty).
:- ensure_loaded(src/builtins).
:- ensure_loaded(src/prelude).
:- ensure_loaded(src/interp).
:- ensure_loaded(src/reference).
:- ensure_loaded(src/cli).

:- initialization(main, main).

main :-
    set_stream(user_output, encoding(utf8)),
    current_prolog_flag(argv, Argv),
    drop_dashdash(Argv, Args),
    catch(( cli(Args), flush_output ),
          cli_exit(Code),
          ( flush_output, halt(Code) )).

drop_dashdash([], []).
drop_dashdash([A|As], Out) :-
    if_commit(A == '--', Out = As, Out = [A|As]).
