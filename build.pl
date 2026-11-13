/*  build.pl - build and test detlog2.

    swipl build.pl            build build/detlog2 (a saved state)
    swipl build.pl test       build, check that every Prolog source is
                              cut-free and choicepoint-free, then run the
                              runtime tests, the end-to-end tests and the
                              converted examples on plain SWI-Prolog
    swipl build.pl ci         as test, fetching mnns first if MNNS_DIR is not
                              set, then check the 200 recorded inputs and
                              outputs
    swipl build.pl ios        run the 200 inputs and write io/ios.txt
    swipl build.pl check-ios  run them again and fail if any output changed

    The Haskell version is built with runghc haskell/Build.hs.
*/

:- use_module(src/detlog_runtime).
:- use_module(library(process)).

:- initialization(main, main).

main :-
    current_prolog_flag(argv, Argv),
    drop_dashes(Argv, Args),
    make_directory_path(build),
    swipl(['-o', 'build/detlog2', '-c', 'detlog2.pl']),
    mode(Args).

drop_dashes([], []).
drop_dashes([A|As], Fs) :-
    if_commit(A == '--', Fs = Fs1, Fs = [A|Fs1]),
    drop_dashes(As, Fs1).

mode(Args) :-
    if_commit(Args = [ci|_], ( fetch_mnns, tests, ios(check) ),
    if_commit(Args = [test|_], tests,
    if_commit(Args = [ios|_], ios(make),
    if_commit(Args = ['check-ios'|_], ios(check),
              true)))).

sources(['detlog2.pl', 'build.pl', 'src/detlog_runtime.pl', 'src/term.pl', 'src/stream.pl',
         'src/reader.pl', 'src/pretty.pl', 'src/builtins.pl', 'src/prelude.pl', 'src/interp.pl',
         'src/reference.pl', 'src/cut_elim.pl', 'src/convert.pl', 'src/check.pl', 'src/proof.pl',
         'src/proof_steps.pl', 'src/memo.pl', 'src/cli.pl', 'tools/cutfree.pl',
         'tests/runtime_tests.pl', 'tests/native_tests.pl', 'tests/cli.pl', 'io/ios.pl',
         'docs/examples/splice.pl', 'docs/examples/cuts.pl', 'docs/examples/sample_program.pl',
         'docs/examples/output.pl', 'docs/examples/memo.pl']).

tests :-
    sources(Ss),
    swipl(['tools/cutfree.pl', '--'|Ss]),
    swipl(['tests/runtime_tests.pl']),
    swipl(['tests/cli.pl']),
    converted_examples,
    swipl(['tests/native_tests.pl', '--', 'build/conv']),
    swipl(['tests/native_tests.pl', '--', 'docs/examples', sketch]).

converted_examples :-
    make_directory_path('build/conv'),
    maplist(convert_example, [splice, cuts, output, sample_program]),
    run('./build/detlog2', [memoise, 'examples/memo.pl', '--goal', 'pick(2, X)', '--goal', 'pick(5, X)',
                            '--complete', '-o', 'build/conv/memo.pl']).

convert_example(E) :-
    format(atom(In), "examples/~w.pl", [E]),
    format(atom(Out), "build/conv/~w.pl", [E]),
    run('./build/detlog2', [convert, In, '-o', Out]).

ios(Mode) :-
    swipl(['io/ios.pl', Mode]).

%  CI: use $MNNS_DIR, or clone mnns next to the build.
fetch_mnns :-
    if_commit(getenv('MNNS_DIR', _),
              true,
              ( if_commit(exists_directory('build/mnns'),
                          true,
                          run(path(git), [clone, '--depth', '1', 'https://github.com/luciangreen/mnns', 'build/mnns'])),
                absolute_file_name('build/mnns', Abs),
                setenv('MNNS_DIR', Abs) )).

swipl(Args) :-
    run(path(swipl), Args).

run(Exe, Args) :-
    process_create(Exe, Args, [process(P)]),
    process_wait(P, Status),
    if_commit(Status == exit(0), true, ( exit_code(Status, C), halt(C) )).

exit_code(Status, C) :-
    if_commit(Status = exit(C0), C = C0, C = 1).
