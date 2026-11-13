/*  builtins.pl - built-in predicates shared by both engines, and the
    Detlog runtime (member_cp/2, splice/2, splice_extend/4, ...) over
    object terms.

    A built-in returns an answer stream (stream.pl).  A deterministic
    built-in returns at most one answer; generators such as between/3
    return several, lazily.  Streams are data, never choicepoints.

    Keys are atoms 'Name/Arity'.
*/

:- set_prolog_flag(float_zero_div, infinity).
:- set_prolog_flag(float_overflow, infinity).
:- set_prolog_flag(float_undefined, nan).

key_atom(F, N, K) :-
    format(atom(K), "~w/~w", [F, N]).

control_keys([',/2', ';/2', '->/2', '*->/2', '\\+/1', 'call/1',
              'true/0', 'fail/0', 'false/0', '!/0', 'once/1',
              'ignore/1', 'findall/3', 'findall/4', 'forall/2',
              'if_commit/3', 'once_det/1', 'decision/2', 'not/1',
              'aggregate_all/3', 'bagof/3', 'setof/3',
              'call/2', 'call/3', 'call/4', 'call/5', 'call/6', 'call/7', 'call/8']).

detlog_runtime_keys(['member_cp/2', 'between_cp/3', 'cp_rows/2', 'splice/2',
                     'splice_first/2', 'splice_extend/4', 'rows_concat/2',
                     'cp_filter/3', 'splice_safe/1', 'memo_lookup/3', 'memo_miss/2',
                     's2a_rows/3', 'length_det/2', 'builtin_rows/2',
                     'effect_text/2', 'packet_first/3', 'packet_split/3']).

effect_keys(['write/1', 'print/1', 'writeln/1', 'writeq/1',
             'write_canonical/1', 'nl/0', 'tab/1', 'format/1', 'format/2',
             'put_char/1']).

var_sensitive_keys(['var/1', 'nonvar/1', '==/2', '\\==/2', '@</2', '@>/2',
                    '@=</2', '@>=/2', 'compare/3', 'copy_term/2', '\\=/2',
                    'ground/1', '=@=/2', '\\=@=/2', 'msort/2', 'sort/2',
                    'atom/1', 'number/1', 'integer/1', 'float/1', 'atomic/1',
                    'compound/1', 'callable/1', 'is_list/1']).

nondet_builtin_keys(['between/3', 'length/2', 'sub_atom/5', 'arg/3',
                     'atomic_list_concat/3', 'clause/2']).

builtin_keys(['=/2', '\\=/2', '==/2', '\\==/2', '@</2', '@>/2', '@=</2', '@>=/2',
              '=@=/2', '\\=@=/2', 'compare/3', 'is/2', '=:=/2', '=\\=/2', '</2',
              '>/2', '=</2', '>=/2', 'succ/2', 'plus/3', 'var/1', 'nonvar/1',
              'atom/1', 'number/1', 'integer/1', 'float/1', 'atomic/1',
              'compound/1', 'callable/1', 'is_list/1', 'ground/1', 'functor/3',
              'arg/3', '=../2', 'copy_term/2', 'atom_chars/2', 'atom_codes/2',
              'char_code/2', 'atom_length/2', 'number_codes/2', 'number_chars/2',
              'atom_number/2', 'atom_string/2', 'string_chars/2',
              'string_concat/3', 'atom_concat/3', 'upcase_atom/2',
              'downcase_atom/2', 'sub_atom/5', 'atomic_list_concat/2',
              'atomic_list_concat/3', 'term_to_atom/2', 'length/2',
              'between/3', 'msort/2', 'sort/2', 'write/1', 'print/1',
              'writeq/1', 'write_canonical/1', 'writeln/1', 'nl/0', 'tab/1',
              'put_char/1', 'format/1', 'format/2', 'format/3',
              'member_cp/2', 'between_cp/3', 'cp_rows/2', 'splice/2',
              'splice_first/2', 'splice_extend/4', 'rows_concat/2',
              'cp_filter/3', 'splice_safe/1', 'length_det/2', 'effect_text/2',
              'packet_first/3', 'packet_split/3', 'builtin_rows/2',
              'memo_lookup/3', 'memo_miss/2', 's2a_rows/3']).

key_in(Table, K, B) :-
    call(Table, L),
    test(memberchk(K, L), B).

is_builtin_key(K, B) :-
    key_in(builtin_keys, K, B).

%  builtin(+Name, +Args, +State, -MaybeStream)
builtin(F, As, St, M) :-
    length(As, N),
    key_atom(F, N, K),
    is_builtin_key(K, B),
    builtin_(B, K, As, St, M).

builtin_(false, _, _, _, nothing).
builtin_(true, K, As, St, just(S)) :-
    bi(K, As, St, S).

% ---------------------------------------------------------------------------
% Errors

inst_err(Ctx, [err(M)]) :-
    format(string(M), "instantiation error in ~w", [Ctx]).

type_err(Ty, T, [err(M)]) :-
    show_term_q(T, TS),
    format(string(M), "type error: expected ~w, got ~s", [Ty, TS]).

err_s(M, [err(M)]).

% ---------------------------------------------------------------------------
% The table

bi('=/2', [A, B], St, S) :-
    unify(A, B, St, M),
    maybe_stream(M, S).
bi('\\=/2', [A, B], St, S) :-
    unify(A, B, St, M),
    not_unifiable(M, St, S).
bi('==/2', [A, B], St, S) :-
    identical(St, A, B, Bo),
    bool_stream(Bo, St, S).
bi('\\==/2', [A, B], St, S) :-
    identical(St, A, B, Bo),
    bool_not(Bo, NBo),
    bool_stream(NBo, St, S).
bi('@</2', [A, B], St, S) :-
    cmp_std_s([<], A, B, St, S).
bi('@>/2', [A, B], St, S) :-
    cmp_std_s([>], A, B, St, S).
bi('@=</2', [A, B], St, S) :-
    cmp_std_s([<, =], A, B, St, S).
bi('@>=/2', [A, B], St, S) :-
    cmp_std_s([>, =], A, B, St, S).
bi('=@=/2', [A, B], St, S) :-
    variant_t(St, A, B, Bo),
    bool_stream(Bo, St, S).
bi('\\=@=/2', [A, B], St, S) :-
    variant_t(St, A, B, Bo),
    bool_not(Bo, NBo),
    bool_stream(NBo, St, S).
bi('compare/3', [O, A, B], St, S) :-
    compare_std(St, A, B, Ord),
    same_vars(St, A, B, Same),
    compare_symbol(Ord, Same, R),
    unify(O, atom(R), St, M),
    maybe_stream(M, S).
bi('is/2', [R, E], St, S) :-
    with_num(St, E, unify_num(R, St), S).
bi('=:=/2', [A, B], St, S) :-
    arith_cmp([=], A, B, St, S).
bi('=\\=/2', [A, B], St, S) :-
    arith_cmp([<, >], A, B, St, S).
bi('</2', [A, B], St, S) :-
    arith_cmp([<], A, B, St, S).
bi('>/2', [A, B], St, S) :-
    arith_cmp([>], A, B, St, S).
bi('=</2', [A, B], St, S) :-
    arith_cmp([<, =], A, B, St, S).
bi('>=/2', [A, B], St, S) :-
    arith_cmp([>, =], A, B, St, S).
bi('succ/2', [A, B], St, S) :-
    succ_b(A, B, St, S).
bi('plus/3', [A, B, C], St, S) :-
    plus_b(A, B, C, St, S).
bi('var/1', [A], St, S) :-
    type_test(is_var_t, A, St, S).
bi('nonvar/1', [A], St, S) :-
    type_test(is_nonvar_t, A, St, S).
bi('atom/1', [A], St, S) :-
    type_test(is_atom_t, A, St, S).
bi('number/1', [A], St, S) :-
    type_test(is_number_t, A, St, S).
bi('integer/1', [A], St, S) :-
    type_test(is_integer_t, A, St, S).
bi('float/1', [A], St, S) :-
    type_test(is_float_t, A, St, S).
bi('atomic/1', [A], St, S) :-
    type_test(is_atomic_t, A, St, S).
bi('compound/1', [A], St, S) :-
    type_test(is_compound_t, A, St, S).
bi('callable/1', [A], St, S) :-
    type_test(is_callable_t, A, St, S).
bi('is_list/1', [A], St, S) :-
    term_to_list(A, St, M),
    is_just(M, Bo),
    bool_stream(Bo, St, S).
bi('ground/1', [A], St, S) :-
    resolve(A, St, R),
    term_vars_ordered(R, Vs),
    test(Vs == [], Bo),
    bool_stream(Bo, St, S).
bi('functor/3', [T, N, A], St, S) :-
    functor_b(T, N, A, St, S).
bi('arg/3', [N, T, A], St, S) :-
    arg_b(N, T, A, St, S).
bi('=../2', [T, L], St, S) :-
    univ_b(T, L, St, S).
bi('copy_term/2', [A, B], St, S) :-
    copy_term_st(St, A, C, St1),
    unify(B, C, St1, M),
    maybe_stream(M, S).
bi('atom_chars/2', [A, L], St, S) :-
    text_b(atom_chars, enc_chars, dec_char, A, L, St, S).
bi('atom_codes/2', [A, L], St, S) :-
    text_b(atom_codes, enc_codes, dec_code, A, L, St, S).
bi('char_code/2', [C, K], St, S) :-
    char_code_b(C, K, St, S).
bi('atom_length/2', [A, N], St, S) :-
    atom_length_b(A, N, St, S).
bi('number_codes/2', [N, L], St, S) :-
    number_text_b(enc_codes, dec_code, N, L, St, S).
bi('number_chars/2', [N, L], St, S) :-
    number_text_b(enc_chars, dec_char, N, L, St, S).
bi('atom_number/2', [A, N], St, S) :-
    atom_number_b(A, N, St, S).
bi('atom_string/2', [A, Str], St, S) :-
    text_b(atom_string, enc_chars, dec_char, A, Str, St, S).
bi('string_chars/2', [Str, Cs], St, S) :-
    unify(Str, Cs, St, M),
    maybe_stream(M, S).
bi('string_concat/3', [A, B, C], St, S) :-
    append_text(St, A, B, C, S).
bi('atom_concat/3', [A, B, C], St, S) :-
    atom_concat_b(St, A, B, C, S).
bi('upcase_atom/2', [A, B], St, S) :-
    case_b(upcase, A, B, St, S).
bi('downcase_atom/2', [A, B], St, S) :-
    case_b(downcase, A, B, St, S).
bi('sub_atom/5', [A, B, L, Af, Sub], St, S) :-
    sub_atom_b(A, B, L, Af, Sub, St, S).
bi('atomic_list_concat/2', [L, A], St, S) :-
    atomic_list_concat_b(St, L, atom(''), A, S).
bi('atomic_list_concat/3', [L, Sep, A], St, S) :-
    atomic_list_concat_b(St, L, Sep, A, S).
bi('term_to_atom/2', [T, A], St, S) :-
    resolve(T, St, R),
    show_term_q(R, Txt),
    atom_string(At, Txt),
    unify(A, atom(At), St, M),
    maybe_stream(M, S).
bi('length/2', [L, N], St, S) :-
    length_b(L, N, St, S).
bi('between/3', [Lo, Hi, X], St, S) :-
    between_b(Lo, Hi, X, St, S).
bi('msort/2', [L, Out], St, S) :-
    sort_b(false, St, L, Out, S).
bi('sort/2', [L, Out], St, S) :-
    sort_b(true, St, L, Out, S).
bi('write/1', [A], St, [out(T), ans(St)]) :-
    resolve(A, St, R),
    show_term(R, T).
bi('print/1', [A], St, [out(T), ans(St)]) :-
    resolve(A, St, R),
    show_term_q(R, T).
bi('writeq/1', [A], St, [out(T), ans(St)]) :-
    resolve(A, St, R),
    show_term_q(R, T).
bi('write_canonical/1', [A], St, [out(T), ans(St)]) :-
    resolve(A, St, R),
    show_term_q(R, T).
bi('writeln/1', [A], St, [out(T), ans(St)]) :-
    resolve(A, St, R),
    show_term(R, T0),
    string_concat(T0, "\n", T).
bi('nl/0', [], St, [out("\n"), ans(St)]).
bi('tab/1', [N], St, S) :-
    with_num(St, N, tab_out(N, St), S).
bi('put_char/1', [C], St, S) :-
    walk(C, St, W),
    put_char_b(W, St, S).
bi('format/1', [F], St, S) :-
    format_b(St, F, atom('[]'), S).
bi('format/2', [F, As], St, S) :-
    format_b(St, F, As, S).
bi('format/3', [Sink, F, As], St, S) :-
    format_to_b(Sink, F, As, St, S).
% Detlog runtime ------------------------------------------------------------
bi('member_cp/2', [X, L], St, S) :-
    term_to_list(L, St, M),
    member_cp_b(M, X, L, St, S).
bi('between_cp/3', [Lo, Hi, P], St, S) :-
    between_cp_b(Lo, Hi, P, St, S).
bi('cp_rows/2', [P, Rows], St, S) :-
    cp_rows_b(P, Rows, St, S).
bi('splice/2', [Ts, Rows], St, S) :-
    splice_rows(St, Ts, E),
    splice_b(E, Rows, St, S).
bi('splice_first/2', [Ts, Row], St, S) :-
    splice_rows(St, Ts, E),
    splice_first_b(E, Row, St, S).
bi('splice_extend/4', [Rows, Env, Pat, Out], St, S) :-
    splice_extend_b(Rows, Env, Pat, Out, St, S).
bi('rows_concat/2', [Ls, Out], St, S) :-
    rows_concat_b(Ls, Out, St, S).
bi('cp_filter/3', [P, Pat, Out], St, S) :-
    walk(P, St, W),
    cp_filter_b(W, Pat, Out, St, S).
bi('splice_safe/1', [Gs], St, S) :-
    splice_safe_b(Gs, St, S).
bi('length_det/2', [L, N], St, S) :-
    length_det_b(L, N, St, S).
bi('effect_text/2', [G, T], St, S) :-
    effect_text_b(G, T, St, S).
bi('packet_first/3', [P, Pre, Res], St, S) :-
    packet_first_b(P, Pre, Res, St, S).
bi('packet_split/3', [P, Outs, Rows], St, S) :-
    packet_split_b(P, Outs, Rows, St, S).
bi('builtin_rows/2', [G, Rows], St, S) :-
    walk(G, St, W),
    builtin_rows_b(W, Rows, St, S).
bi('memo_lookup/3', [Args, Table, Rows], St, S) :-
    memo_lookup_b(Args, Table, Rows, St, S).
bi('s2a_rows/3', [Spec, Args, Rows], St, S) :-
    s2a_rows_b(Spec, Args, Rows, St, S).
bi('memo_miss/2', [K, A], St, [err(M)]) :-
    resolve(K, St, RK),
    resolve(A, St, RA),
    show_term_q(RK, KS),
    show_term_q(RA, AS),
    format(string(M), "memo_miss: ~s was memoised as complete, but has no entry for ~s", [KS, AS]).

% ---------------------------------------------------------------------------
% Helpers

not_unifiable(nothing, St, [ans(St)]).
not_unifiable(just(_), _, []).

bool_stream(true, St, [ans(St)]).
bool_stream(false, _, []).

same_vars(St, A, B, Bo) :-
    resolve(A, St, RA),
    resolve(B, St, RB),
    same_term(RA, RB, Bo).

identical(St, A, B, Bo) :-
    compare_std(St, A, B, O),
    same_vars(St, A, B, Same),
    test(( O == (=), Same == true ), Bo).

compare_symbol(<, _, '<').
compare_symbol(>, _, '>').
compare_symbol(=, Same, R) :-
    eq_symbol(Same, R).

eq_symbol(true, '=').
eq_symbol(false, '<').

cmp_std_s(Os, A, B, St, S) :-
    compare_std(St, A, B, O),
    test(memberchk(O, Os), Bo),
    bool_stream(Bo, St, S).

type_test(P, A, St, S) :-
    walk(A, St, W),
    call(P, W, Bo),
    bool_stream(Bo, St, S).

is_nonvar_t(T, B) :-
    is_var_t(T, V),
    bool_not(V, B).

is_atom_t(var(_, _), false).
is_atom_t(atom(_), true).
is_atom_t(int(_), false).
is_atom_t(flt(_), false).
is_atom_t(comp(_, _), false).

is_number_t(var(_, _), false).
is_number_t(atom(_), false).
is_number_t(int(_), true).
is_number_t(flt(_), true).
is_number_t(comp(_, _), false).

is_integer_t(var(_, _), false).
is_integer_t(atom(_), false).
is_integer_t(int(_), true).
is_integer_t(flt(_), false).
is_integer_t(comp(_, _), false).

is_float_t(var(_, _), false).
is_float_t(atom(_), false).
is_float_t(int(_), false).
is_float_t(flt(_), true).
is_float_t(comp(_, _), false).

is_atomic_t(var(_, _), false).
is_atomic_t(atom(_), true).
is_atomic_t(int(_), true).
is_atomic_t(flt(_), true).
is_atomic_t(comp(_, _), false).

is_compound_t(var(_, _), false).
is_compound_t(atom(_), false).
is_compound_t(int(_), false).
is_compound_t(flt(_), false).
is_compound_t(comp(_, _), true).

% ---------------------------------------------------------------------------
% Arithmetic: values ni(Integer) and nf(Float)

num_term(ni(I), int(I)).
num_term(nf(F), flt(F)).

to_d(ni(I), D) :-
    D is float(I).
to_d(nf(D), D).

%  with_num(+State, +Expr, +K, -Stream): call(K, Value, Stream).
with_num(St, E, K, S) :-
    eval_arith(St, E, R),
    with_num_(R, K, S).

with_num_(left(M), _, [err(M)]).
with_num_(right(V), K, S) :-
    call(K, V, S).

unify_num(R, St, V, S) :-
    num_term(V, T),
    unify(R, T, St, M),
    maybe_stream(M, S).

arith_cmp(Os, A, B, St, S) :-
    eval_arith(St, A, RA),
    eval_arith(St, B, RB),
    arith_cmp_(RA, RB, Os, St, S).

arith_cmp_(left(M), _, _, _, [err(M)]).
arith_cmp_(right(X), RB, Os, St, S) :-
    arith_cmp_r(RB, X, Os, St, S).

arith_cmp_r(left(M), _, _, _, [err(M)]).
arith_cmp_r(right(Y), X, Os, St, S) :-
    cmp_num(X, Y, O),
    test(memberchk(O, Os), Bo),
    bool_stream(Bo, St, S).

cmp_num(ni(A), Y, O) :-
    cmp_num_i(Y, A, O).
cmp_num(nf(A), Y, O) :-
    to_d(Y, B),
    float_order(A, B, O).

cmp_num_i(ni(B), A, O) :-
    compare(O, A, B).
cmp_num_i(nf(B), A, O) :-
    AD is float(A),
    float_order(AD, B, O).

%  eval_arith(+State, +Expr, -Either): right(Value) or left(Message).
eval_arith(St, T, R) :-
    walk(T, St, W),
    eval_w(W, St, R).

eval_w(int(I), _, right(ni(I))).
eval_w(flt(D), _, right(nf(D))).
eval_w(var(_, _), _, left("instantiation error in arithmetic")).
eval_w(atom(A), _, R) :-
    eval_atom(A, R).
eval_w(comp(F, As), St, R) :-
    length(As, N),
    eval_comp(N, F, As, St, R).

eval_atom(A, R) :-
    if_commit(eval_const(A, V),
              R = right(V),
              ( atom_length(A, L),
                if_commit(L =:= 1,
                          ( char_code(A, C), R = right(ni(C)) ),
                          ( format(string(M), "type error: evaluable ~w/0", [A]),
                            R = left(M) )) )).

eval_const(pi, nf(D)) :-
    D is pi.
eval_const(e, nf(D)) :-
    D is e.
eval_const(inf, nf(D)) :-
    D is inf.
eval_const(max_tagged_integer, ni(I)) :-
    I is 2 ** 60 - 1.

eval_comp(N, F, As, St, R) :-
    if_commit(( F == '.', As = [X, atom('[]')] ),
              eval_arith(St, X, R),
              eval_comp_n(N, F, As, St, R)).

eval_comp_n(N, F, As, St, R) :-
    if_commit(N =:= 1,
              ( As = [X], eval_arith(St, X, RX), eval_un(RX, F, R) ),
              if_commit(N =:= 2,
                        ( As = [X, Y], eval_arith(St, X, RX), eval_arith(St, Y, RY),
                          eval_bin(RX, RY, F, R) ),
                        ( show_term_q(comp(F, As), TS),
                          format(string(M), "type error: evaluable ~s", [TS]),
                          R = left(M) ))).

eval_un(left(M), _, left(M)).
eval_un(right(V), F, R) :-
    if_commit(un_op(F, V, R0), R = R0,
              ( format(string(M), "type error: evaluable ~w/1", [F]), R = left(M) )).

%  un_op(+Name, +Value, -Either): semidet; fails for an unknown operation.
%  un_case/3 and bin_case/4 are relations, called only as if_commit/3
%  conditions: the first matching clause wins, as in a Haskell case.
un_op(F, V, R) :-
    un_case(F, V, R).

:- relation(un_case/3).
:- relation(bin_case/4).

un_case('-', ni(A), right(ni(B))) :- B is -A.
un_case('-', nf(A), right(nf(B))) :- B is -A.
un_case('+', V, right(V)).
un_case(abs, ni(A), right(ni(B))) :- B is abs(A).
un_case(abs, nf(A), right(nf(B))) :- B is abs(A).
un_case(sign, ni(A), right(ni(B))) :- B is sign(A).
un_case(sign, nf(A), right(nf(B))) :- B is sign(A).
un_case(min, _, left("min/1")).
un_case(float, V, right(nf(D))) :- to_d(V, D).
un_case(integer, ni(A), right(ni(A))).
un_case(integer, nf(A), right(ni(B))) :- hround(A, B).
un_case(float_integer_part, V, right(nf(D))) :- to_d(V, X), T is truncate(X), D is float(T).
un_case(truncate, V, right(ni(B))) :- to_d(V, X), B is truncate(X).
un_case(floor, V, right(ni(B))) :- to_d(V, X), B is floor(X).
un_case(ceiling, V, right(ni(B))) :- to_d(V, X), B is ceiling(X).
un_case(round, V, right(ni(B))) :- to_d(V, X), hround(X, B).
un_case(sqrt, V, right(nf(B))) :- to_d(V, X), B is sqrt(X).
un_case(exp, V, right(nf(B))) :- to_d(V, X), B is exp(X).
un_case(log, V, right(nf(B))) :- to_d(V, X), B is log(X).
un_case(log2, V, right(nf(B))) :- to_d(V, X), B is log(X) / log(2.0).
un_case(sin, V, right(nf(B))) :- to_d(V, X), B is sin(X).
un_case(cos, V, right(nf(B))) :- to_d(V, X), B is cos(X).
un_case(tan, V, right(nf(B))) :- to_d(V, X), B is tan(X).
un_case(atan, V, right(nf(B))) :- to_d(V, X), B is atan(X).
un_case('\\', ni(A), right(ni(B))) :- B is \ A.
un_case(msb, ni(A), right(ni(B))) :- A > 0, B is msb(A).
un_case(succ, ni(A), right(ni(B))) :- B is A + 1.

%  Haskell's round: halves go to the even neighbour.
hround(X, I) :-
    F is floor(X),
    D is X - F,
    if_commit(D =:= 0.5,
              if_commit(F mod 2 =:= 0, I = F, I is F + 1),
              I is round(X)).

eval_bin(left(M), _, _, left(M)).
eval_bin(right(A), RB, F, R) :-
    eval_bin_r(RB, A, F, R).

eval_bin_r(left(M), _, _, left(M)).
eval_bin_r(right(B), A, F, R) :-
    if_commit(bin_case(F, A, B, R0), R = R0,
              ( format(string(M), "type error: evaluable ~w/2", [F]), R = left(M) )).

bin_case('+', ni(X), ni(Y), right(ni(Z))) :- Z is X + Y.
bin_case('-', ni(X), ni(Y), right(ni(Z))) :- Z is X - Y.
bin_case('*', ni(X), ni(Y), right(ni(Z))) :- Z is X * Y.
bin_case('+', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X + Y.
bin_case('-', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X - Y.
bin_case('*', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X * Y.
bin_case('/', ni(X), ni(Y), R) :- int_div(X, Y, R).
bin_case('/', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X / Y.
bin_case('//', ni(X), ni(Y), R) :- int_op(Y, X, //, R).
bin_case(div, ni(X), ni(Y), R) :- int_op(Y, X, div, R).
bin_case(mod, ni(X), ni(Y), R) :- int_op(Y, X, mod, R).
bin_case(rem, ni(X), ni(Y), R) :- int_op(Y, X, rem, R).
bin_case(min, A, B, right(V)) :- cmp_num(A, B, O), min_of(O, A, B, V).
bin_case(max, A, B, right(V)) :- cmp_num(A, B, O), max_of(O, A, B, V).
bin_case('**', ni(X), ni(Y), right(ni(Z))) :- Y >= 0, Z is X ^ Y.
bin_case('**', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X ** Y.
bin_case('^', ni(X), ni(Y), R) :- int_pow(X, Y, R).
bin_case('^', A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is X ** Y.
bin_case('>>', ni(X), ni(Y), right(ni(Z))) :- Z is X >> Y.
bin_case('<<', ni(X), ni(Y), right(ni(Z))) :- Z is X << Y.
bin_case('/\\', ni(X), ni(Y), right(ni(Z))) :- Z is X /\ Y.
bin_case('\\/', ni(X), ni(Y), right(ni(Z))) :- Z is X \/ Y.
bin_case(xor, ni(X), ni(Y), right(ni(Z))) :- Z is X xor Y.
bin_case(gcd, ni(X), ni(Y), right(ni(Z))) :- Z is gcd(X, Y).
bin_case(atan2, A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is atan2(X, Y).
bin_case(atan, A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is atan2(X, Y).
bin_case(log, A, B, right(nf(Z))) :- to_d(A, X), to_d(B, Y), Z is log(Y) / log(X).
bin_case(truncate, _, _, left("truncate/2")).

int_div(X, Y, R) :-
    if_commit(Y =:= 0,
              R = left("evaluation error: zero_divisor"),
              if_commit(X mod Y =:= 0,
                        ( Z is X div Y, R = right(ni(Z)) ),
                        ( Z is X / Y, Z1 is float(Z), R = right(nf(Z1)) ))).

int_op(Y, X, Op, R) :-
    if_commit(Y =:= 0,
              R = left("evaluation error: zero_divisor"),
              ( E =.. [Op, X, Y], Z is E, R = right(ni(Z)) )).

int_pow(X, Y, R) :-
    if_commit(Y >= 0, ( Z is X ^ Y, R = right(ni(Z)) ),
    if_commit(X =:= 1, R = right(ni(1)),
    if_commit(X =:= -1, ( Z is (-1) ^ (-Y), R = right(ni(Z)) ),
              R = left("^/2: negative exponent")))).

min_of(>, _, B, B).
min_of(<, A, _, A).
min_of(=, A, _, A).

max_of(<, _, B, B).
max_of(>, A, _, A).
max_of(=, A, _, A).

succ_b(A, B, St, S) :-
    walk(A, St, WA),
    walk(B, St, WB),
    if_commit(( WA = int(X), X >= 0 ),
              ( X1 is X + 1, unify(B, int(X1), St, M), maybe_stream(M, S) ),
    if_commit(( WA = var(_, _), WB = int(Y) ),
              if_commit(Y > 0,
                        ( Y1 is Y - 1, unify(A, int(Y1), St, M), maybe_stream(M, S) ),
                        S = []),
    if_commit(( WA = var(_, _), WB = var(_, _) ),
              inst_err("succ/2", S),
              type_err(not_less_than_zero, WA, S)))).

plus_b(A, B, C, St, S) :-
    walk(A, St, WA),
    walk(B, St, WB),
    walk(C, St, WC),
    if_commit(( WA = int(X), WB = int(Y) ),
              ( Z is X + Y, unify(C, int(Z), St, M), maybe_stream(M, S) ),
    if_commit(( WA = int(X), WC = int(Z) ),
              ( Y is Z - X, unify(B, int(Y), St, M), maybe_stream(M, S) ),
    if_commit(( WB = int(Y), WC = int(Z) ),
              ( X is Z - Y, unify(A, int(X), St, M), maybe_stream(M, S) ),
              inst_err("plus/3", S)))).

tab_out(N, St, V, S) :-
    if_commit(V = ni(K),
              ( length(Cs, K), maplist(=(0' ), Cs), string_codes(T, Cs), S = [out(T), ans(St)] ),
              type_err(integer, N, S)).

put_char_b(W, St, S) :-
    if_commit(( W = atom(A), atom_length(A, 1) ),
              ( atom_string(A, T), S = [out(T), ans(St)] ),
              type_err(character, W, S)).

% ---------------------------------------------------------------------------
% Term construction

functor_b(T, N, A, St, S) :-
    walk(T, St, W),
    functor_w(W, T, N, A, St, S).

functor_w(var(_, _), T, N, A, St, S) :-
    walk(N, St, WN),
    walk(A, St, WA),
    is_var_t(WN, NV),
    if_commit(( WA = int(0), NV == false ),
              ( unify(T, WN, St, M), maybe_stream(M, S) ),
              if_commit(( WN = atom(Name), WA = int(K), K > 0 ),
                        ( fresh_vars(K, St, Vs, St1),
                          unify(T, comp(Name, Vs), St1, M), maybe_stream(M, S) ),
                        inst_err("functor/3", S))).
functor_w(atom(X), _, N, A, St, S) :-
    functor_atomic(atom(X), N, A, St, S).
functor_w(int(X), _, N, A, St, S) :-
    functor_atomic(int(X), N, A, St, S).
functor_w(flt(X), _, N, A, St, S) :-
    functor_atomic(flt(X), N, A, St, S).
functor_w(comp(F, As), _, N, A, St, S) :-
    length(As, K),
    unify(N, atom(F), St, M1),
    unify_then(A, int(K), M1, M),
    maybe_stream(M, S).

functor_atomic(X, N, A, St, S) :-
    unify(N, X, St, M1),
    unify_then(A, int(0), M1, M),
    maybe_stream(M, S).

arg_b(N, T, A, St, S) :-
    walk(T, St, W),
    if_commit(W = comp(_, As),
              ( walk(N, St, WN), arg_n(WN, As, N, A, St, S) ),
              type_err(compound, W, S)).

arg_n(int(K), As, _, A, St, S) :-
    length(As, L),
    if_commit(( K >= 1, K =< L ),
              ( nth_det(K, As, just(X)), unify(A, X, St, M), maybe_stream(M, S) ),
              S = []).
arg_n(var(I, Nm), As, _, A, St, S) :-
    arg_all(As, 1, var(I, Nm), A, St, S).
arg_n(atom(X), _, _, _, _, S) :-
    type_err(integer, atom(X), S).
arg_n(flt(X), _, _, _, _, S) :-
    type_err(integer, flt(X), S).
arg_n(comp(F, Xs), _, _, _, _, S) :-
    type_err(integer, comp(F, Xs), S).

arg_all([], _, _, _, _, []).
arg_all([X|Xs], I, N, A, St, S) :-
    unify(N, int(I), St, M1),
    unify_then(A, X, M1, M),
    maybe_stream(M, S1),
    I1 is I + 1,
    arg_all(Xs, I1, N, A, St, S2),
    conc(S1, S2, S).

univ_b(T, L, St, S) :-
    walk(T, St, W),
    univ_w(W, L, St, S).

univ_w(comp(F, As), L, St, S) :-
    mk_list([atom(F)|As], atom('[]'), LT),
    unify(L, LT, St, M),
    maybe_stream(M, S).
univ_w(var(I, N), L, St, S) :-
    term_to_list(L, St, ML),
    if_commit(ML = just([X]),
              ( unify(var(I, N), X, St, M), maybe_stream(M, S) ),
              if_commit(ML = just([atom(F)|As]),
                        ( unify(var(I, N), comp(F, As), St, M), maybe_stream(M, S) ),
                        inst_err("=../2", S))).
univ_w(atom(X), L, St, S) :-
    univ_atomic(atom(X), L, St, S).
univ_w(int(X), L, St, S) :-
    univ_atomic(int(X), L, St, S).
univ_w(flt(X), L, St, S) :-
    univ_atomic(flt(X), L, St, S).

univ_atomic(X, L, St, S) :-
    mk_list([X], atom('[]'), LT),
    unify(L, LT, St, M),
    maybe_stream(M, S).

% ---------------------------------------------------------------------------
% Text (as code lists)

%  text_of(+State, +Term, -MaybeCodes): the text of an atomic term or of a
%  list of characters or codes.
text_of(St, T, M) :-
    walk(T, St, W),
    text_of_w(W, St, M).

text_of_w(atom(A), _, just(Cs)) :-
    atom_codes(A, Cs).
text_of_w(int(I), _, just(Cs)) :-
    number_codes(I, Cs).
text_of_w(flt(D), _, just(Cs)) :-
    show_term(flt(D), S),
    string_codes(S, Cs).
text_of_w(var(I, N), St, M) :-
    text_of_list(var(I, N), St, M).
text_of_w(comp(F, As), St, M) :-
    text_of_list(comp(F, As), St, M).

text_of_list(X, St, M) :-
    term_to_list(X, St, ML),
    text_items(ML, M).

text_items(nothing, nothing).
text_items(just(Items), M) :-
    char_items(Items, M).

char_items([], just([])).
char_items([I|Is], M) :-
    char_of(I, MC),
    char_items_(MC, Is, M).

char_items_(nothing, _, nothing).
char_items_(just(C), Is, M) :-
    char_items(Is, M1),
    maybe_cons(M1, C, M).

char_of(I, M) :-
    if_commit(( I = atom(A), atom_length(A, 1) ),
              ( char_code(A, C), M = just(C) ),
              if_commit(I = int(C), M = just(C), M = nothing)).

nonvar_t(St, T, B) :-
    walk(T, St, W),
    is_var_t(W, V),
    bool_not(V, B).

text_nonvar(St, T, M) :-
    nonvar_t(St, T, NV),
    text_nonvar_(NV, St, T, M).

text_nonvar_(false, _, _, nothing).
text_nonvar_(true, St, T, M) :-
    text_of(St, T, M).

enc_chars(Cs, Ts) :-
    maplist(code_atom_term, Cs, Ts).

code_atom_term(C, atom(A)) :-
    char_code(A, C).

enc_codes(Cs, Ts) :-
    maplist(code_int_term, Cs, Ts).

code_int_term(C, int(C)).

dec_char(St, T, M) :-
    walk(T, St, W),
    if_commit(( W = atom(A), atom_length(A, 1) ), ( char_code(A, C), M = just(C) ), M = nothing).

dec_code(St, T, M) :-
    walk(T, St, W),
    if_commit(W = int(C), M = just(C), M = nothing).

decode_all(Dec, St, Ts, M) :-
    decode_all_(Ts, Dec, St, M).

decode_all_([], _, _, just([])).
decode_all_([T|Ts], Dec, St, M) :-
    call(Dec, St, T, MC),
    decode_more(MC, Dec, St, Ts, M).

decode_more(nothing, _, _, _, nothing).
decode_more(just(C), Dec, St, Ts, M) :-
    decode_all(Dec, St, Ts, M1),
    maybe_cons(M1, C, M).

codes_list_term(Enc, Cs, T) :-
    call(Enc, Cs, Ts),
    mk_list(Ts, atom('[]'), T).

text_b(Name, Enc, Dec, A, L, St, S) :-
    walk(A, St, W),
    is_var_t(W, V),
    text_b_(V, Name, Enc, Dec, A, L, St, S).

text_b_(true, Name, _, Dec, A, L, St, S) :-
    term_to_list(L, St, ML),
    if_commit(ML = just(Items),
              ( decode_list(Dec, St, Items, MS),
                if_commit(MS = just(Cs),
                          ( atom_codes(At, Cs), unify(A, atom(At), St, M), maybe_stream(M, S) ),
                          inst_err(Name, S)) ),
              inst_err(Name, S)).
text_b_(false, _, Enc, _, A, L, St, S) :-
    text_of(St, A, MT),
    if_commit(MT = just(Cs),
              ( codes_list_term(Enc, Cs, LT), unify(L, LT, St, M), maybe_stream(M, S) ),
              ( resolve(A, St, RA), type_err(atomic, RA, S) )).

decode_list(Dec, St, Items, M) :-
    decode_all(Dec, St, Items, M).

number_text_b(Enc, Dec, N, L, St, S) :-
    walk(N, St, W),
    number_text_w(W, Enc, Dec, N, L, St, S).

number_text_w(var(_, _), _, Dec, N, L, St, S) :-
    term_to_list(L, St, ML),
    if_commit(( ML = just(Items), decode_list(Dec, St, Items, just(Cs)) ),
              ( parse_number(Cs, MN),
                if_commit(MN = just(V),
                          ( unify(N, V, St, M), maybe_stream(M, S) ),
                          ( atom_codes(TA, Cs), format(string(E), "syntax error: illegal number ~q", [TA]),
                            S = [err(E)] )) ),
              inst_err("number_codes/2", S)).
number_text_w(int(I), Enc, _, _, L, St, S) :-
    number_codes(I, Cs),
    codes_list_term(Enc, Cs, LT),
    unify(L, LT, St, M),
    maybe_stream(M, S).
number_text_w(flt(D), Enc, _, _, L, St, S) :-
    show_term(flt(D), Txt),
    string_codes(Txt, Cs),
    codes_list_term(Enc, Cs, LT),
    unify(L, LT, St, M),
    maybe_stream(M, S).
number_text_w(atom(X), _, _, _, _, _, S) :-
    type_err(number, atom(X), S).
number_text_w(comp(F, As), _, _, _, _, _, S) :-
    type_err(number, comp(F, As), S).

%  parse_number(+Codes, -MaybeTerm): the numbers detlog2 reads from text.
parse_number(Cs0, M) :-
    span_codes(is_space_c, Cs0, _, Cs),
    if_commit(Cs = [0'-|Rest],
              ( parse_number(Rest, M1), negate_num(M1, M) ),
              if_commit(( Cs \== [], all_digits(Cs) ),
                        ( number_codes(I, Cs), M = just(int(I)) ),
                        if_commit(( append(A, [0'.|B], Cs), A \== [], all_digits(A),
                                    B \== [], all_digits(B) ),
                                  ( number_codes(F, Cs), M = just(flt(F)) ),
                                  M = nothing))).

all_digits([]).
all_digits([C|Cs]) :-
    is_digit_c(C),
    all_digits(Cs).

negate_num(nothing, nothing).
negate_num(just(T), just(N)) :-
    negate_term(T, N).

negate_term(int(I), int(J)) :-
    J is -I.
negate_term(flt(F), flt(G)) :-
    G is -F.
negate_term(atom(A), atom(A)).
negate_term(var(I, N), var(I, N)).
negate_term(comp(F, As), comp(F, As)).

atom_number_b(A, N, St, S) :-
    walk(A, St, W),
    atom_number_w(W, N, St, S).

atom_number_w(atom(X), N, St, S) :-
    atom_codes(X, Cs),
    parse_number(Cs, MN),
    if_commit(MN = just(V), ( unify(N, V, St, M), maybe_stream(M, S) ), S = []).
atom_number_w(var(I, Nm), N, St, S) :-
    walk(N, St, WN),
    if_commit(WN = int(K),
              ( atom_number(At, K), unify(var(I, Nm), atom(At), St, M), maybe_stream(M, S) ),
              if_commit(WN = flt(D),
                        ( show_term(flt(D), Txt), atom_string(At, Txt),
                          unify(var(I, Nm), atom(At), St, M), maybe_stream(M, S) ),
                        inst_err("atom_number/2", S))).
atom_number_w(int(X), _, _, S) :-
    type_err(atom, int(X), S).
atom_number_w(flt(X), _, _, S) :-
    type_err(atom, flt(X), S).
atom_number_w(comp(F, As), _, _, S) :-
    type_err(atom, comp(F, As), S).

char_code_b(C, K, St, S) :-
    walk(C, St, WC),
    walk(K, St, WK),
    if_commit(( WC = atom(A), atom_length(A, 1) ),
              ( char_code(A, Code), unify(K, int(Code), St, M), maybe_stream(M, S) ),
              if_commit(( WC = var(_, _), WK = int(I) ),
                        ( char_code(Ch, I), unify(C, atom(Ch), St, M), maybe_stream(M, S) ),
                        inst_err("char_code/2", S))).

atom_length_b(A, N, St, S) :-
    text_nonvar(St, A, MT),
    if_commit(MT = just(Cs),
              ( length(Cs, L), unify(N, int(L), St, M), maybe_stream(M, S) ),
              inst_err("atom_length/2", S)).

append_text(St, A, B, C, S) :-
    text_nonvar(St, A, MA),
    text_nonvar(St, B, MB),
    if_commit(( MA = just(X), MB = just(Y) ),
              ( conc(X, Y, XY), atom_codes(At, XY), char_list(At, T),
                unify(C, T, St, M), maybe_stream(M, S) ),
              inst_err("string_concat/3", S)).

atom_concat_b(St, A, B, C, S) :-
    nonvar_t(St, A, NA),
    nonvar_t(St, B, NB),
    if_commit(( NA == true, NB == true ),
              ( text_of(St, A, MA), text_of(St, B, MB),
                if_commit(( MA = just(X), MB = just(Y) ),
                          ( conc(X, Y, XY), atom_codes(At, XY), unify(C, atom(At), St, M),
                            maybe_stream(M, S) ),
                          ( walk(A, St, WA), type_err(atomic, WA, S) )) ),
              ( text_nonvar(St, C, MC),
                if_commit(MC = just(Cs),
                          ( length(Cs, L), splits(0, L, Cs, A, B, St, S) ),
                          inst_err("atom_concat/3", S)) )).

splits(I, L, Cs, A, B, St, S) :-
    if_commit(I > L,
              S = [],
              ( take(I, Cs, P), drop(I, Cs, Q),
                atom_codes(PA, P), atom_codes(QA, Q),
                unify(A, atom(PA), St, M1), unify_then(B, atom(QA), M1, M),
                maybe_stream(M, S1),
                I1 is I + 1,
                splits(I1, L, Cs, A, B, St, S2),
                conc(S1, S2, S) )).

case_b(Dir, A, B, St, S) :-
    text_nonvar(St, A, MT),
    if_commit(MT = just(Cs),
              ( atom_codes(At, Cs), case_atom(Dir, At, At1),
                unify(B, atom(At1), St, M), maybe_stream(M, S) ),
              inst_err("upcase_atom/2", S)).

case_atom(upcase, A, B) :-
    upcase_atom(A, B).
case_atom(downcase, A, B) :-
    downcase_atom(A, B).

sub_atom_b(A, B, L, Af, Sub, St, S) :-
    text_nonvar(St, A, MT),
    if_commit(MT = just(Cs),
              ( length(Cs, N),
                text_nonvar(St, Sub, MS),
                sub_candidates(MS, Cs, N, Cands),
                sub_answers(Cands, Cs, N, B, L, Af, Sub, St, S) ),
              inst_err("sub_atom/5", S)).

sub_candidates(just(T), Cs, N, Cands) :-
    length(T, LT),
    Max is N - LT,
    findall(I-LT, ( between(0, Max, I), drop(I, Cs, D), append(T, _, D) ), Cands).
sub_candidates(nothing, _, N, Cands) :-
    findall(I-K, ( between(0, N, I), M is N - I, between(0, M, K) ), Cands).

sub_answers([], _, _, _, _, _, _, _, []).
sub_answers([I-K|Cs], Text, N, B, L, Af, Sub, St, S) :-
    After is N - I - K,
    drop(I, Text, D),
    take(K, D, SubCs),
    atom_codes(SubA, SubCs),
    unify(B, int(I), St, M1),
    unify_then(L, int(K), M1, M2),
    unify_then(Af, int(After), M2, M3),
    unify_then(Sub, atom(SubA), M3, M),
    maybe_stream(M, S1),
    sub_answers(Cs, Text, N, B, L, Af, Sub, St, S2),
    conc(S1, S2, S).

atomic_list_concat_b(St, L, Sep, A, S) :-
    term_to_list(L, St, ML),
    parts_texts(ML, St, MParts),
    if_commit(MParts = just(Parts),
              ( text_of(St, Sep, MSep),
                if_commit(MSep = just(SepCs),
                          ( join_codes(Parts, SepCs, J), atom_codes(At, J),
                            unify(A, atom(At), St, M), maybe_stream(M, S) ),
                          inst_err("atomic_list_concat/3", S)) ),
              ( text_of(St, Sep, MSep), text_nonvar(St, A, MW),
                if_commit(( MSep = just(SepCs), SepCs \== [], MW = just(Whole) ),
                          ( split_on(SepCs, Whole, Pieces),
                            maplist(codes_atom_term, Pieces, Ts),
                            mk_list(Ts, atom('[]'), LT),
                            unify(L, LT, St, M), maybe_stream(M, S) ),
                          inst_err("atomic_list_concat/3", S)) )).

codes_atom_term(Cs, atom(A)) :-
    atom_codes(A, Cs).

parts_texts(nothing, _, nothing).
parts_texts(just(Items), St, M) :-
    part_texts(Items, St, M).

part_texts([], _, just([])).
part_texts([X|Xs], St, M) :-
    text_nonvar(St, X, MX),
    part_texts_(MX, Xs, St, M).

part_texts_(nothing, _, _, nothing).
part_texts_(just(T), Xs, St, M) :-
    part_texts(Xs, St, M1),
    maybe_cons(M1, T, M).

join_codes([], _, []).
join_codes([P|Ps], Sep, Out) :-
    join_rest(Ps, Sep, Rest),
    conc(P, Rest, Out).

join_rest([], _, []).
join_rest([P|Ps], Sep, Out) :-
    join_rest(Ps, Sep, Rest),
    conc(P, Rest, PR),
    conc(Sep, PR, Out).

split_on(Sep, S, Pieces) :-
    split_go(S, Sep, [], Pieces).

split_go([], _, Acc, [P]) :-
    rev(Acc, P).
split_go([C|Cs], Sep, Acc, Pieces) :-
    if_commit(append(Sep, After, [C|Cs]),
              ( rev(Acc, P), Pieces = [P|Ps], split_go(After, Sep, [], Ps) ),
              split_go(Cs, Sep, [C|Acc], Pieces)).

% ---------------------------------------------------------------------------
% Lists and generators

length_b(L, N, St, S) :-
    partial_list(L, St, Items, End),
    length(Items, Len),
    length_end(End, Len, N, St, S).

length_end(atom(A), Len, N, St, S) :-
    if_commit(A == '[]',
              ( unify(N, int(Len), St, M), maybe_stream(M, S) ),
              type_err(list, atom(A), S)).
length_end(var(I, Nm), Len, N, St, S) :-
    walk(N, St, WN),
    length_open(WN, var(I, Nm), Len, N, St, S).
length_end(int(X), _, _, _, S) :-
    type_err(list, int(X), S).
length_end(flt(X), _, _, _, S) :-
    type_err(list, flt(X), S).
length_end(comp(F, As), _, _, _, S) :-
    type_err(list, comp(F, As), S).

length_open(int(K), End, Len, _, St, S) :-
    if_commit(K >= Len,
              ( Extra is K - Len, fresh_vars(Extra, St, Vs, St1),
                mk_list(Vs, atom('[]'), T), unify(End, T, St1, M), maybe_stream(M, S) ),
              S = []).
length_open(var(_, _), End, Len, N, St, lz(length_gen(Len, Len, End, N, St))).
length_open(atom(X), _, _, _, _, S) :-
    type_err(integer, atom(X), S).
length_open(flt(X), _, _, _, _, S) :-
    type_err(integer, flt(X), S).
length_open(comp(F, As), _, _, _, _, S) :-
    type_err(integer, comp(F, As), S).

%  The lengths k, k+1, ... of an open list: an infinite, lazy stream.
length_gen(K, Len, End, N, St, S) :-
    Extra is K - Len,
    fresh_vars(Extra, St, Vs, St1),
    mk_list(Vs, atom('[]'), T),
    unify(End, T, St1, M1),
    unify_then(N, int(K), M1, M),
    K1 is K + 1,
    length_gen_ans(M, lz(length_gen(K1, Len, End, N, St)), S).

length_gen_ans(nothing, Rest, Rest).
length_gen_ans(just(St), Rest, [ans(St)|Rest]).

between_b(Lo, Hi, X, St, S) :-
    eval_arith(St, Lo, RL),
    walk(Hi, St, WH),
    if_commit(RL = right(ni(L)),
              if_commit(memberchk(WH, [atom(inf), atom(infinite)]),
                        between_gen(L, inf, X, St, S),
                        ( eval_arith(St, Hi, RH),
                          if_commit(RH = right(ni(H)),
                                    ( walk(X, St, WX), between_x(WX, L, H, X, St, S) ),
                                    inst_err("between/3", S)) )),
              inst_err("between/3", S)).

between_x(int(V), L, H, _, St, S) :-
    test(( L =< V, V =< H ), B),
    bool_stream(B, St, S).
between_x(var(_, _), L, H, X, St, S) :-
    between_gen(L, H, X, St, S).
between_x(atom(A), _, _, _, _, S) :-
    type_err(integer, atom(A), S).
between_x(flt(F), _, _, _, _, S) :-
    type_err(integer, flt(F), S).
between_x(comp(F, As), _, _, _, _, S) :-
    type_err(integer, comp(F, As), S).

between_gen(L, H, X, St, S) :-
    walk(X, St, WX),
    if_commit(WX = int(V),
              ( test(( L =< V, in_upper(H, V) ), B), bool_stream(B, St, S) ),
              S = lz(between_step(L, H, X, St))).

in_upper(H, V) :-
    if_commit(H == inf, true, V =< H).

between_step(V, H, X, St, S) :-
    if_commit(( H \== inf, V > H ),
              S = [],
              ( unify(X, int(V), St, M),
                V1 is V + 1,
                length_gen_ans(M, lz(between_step(V1, H, X, St)), S) )).

sort_b(Dedup, St, L, Out, S) :-
    term_to_list(L, St, ML),
    if_commit(ML = just(Items),
              ( predsort_std(St, Items, Sorted),
                dedup_std(Dedup, St, Sorted, Res),
                mk_list(Res, atom('[]'), T),
                unify(Out, T, St, M), maybe_stream(M, S) ),
              inst_err("sort/2", S)).

%  A stable merge sort by the standard order.
predsort_std(St, Items, Sorted) :-
    length(Items, N),
    msort_std(N, St, Items, Sorted).

msort_std(N, St, Items, Sorted) :-
    if_commit(N =< 1,
              Sorted = Items,
              ( H is N // 2, take(H, Items, A), drop(H, Items, B), N2 is N - H,
                msort_std(H, St, A, SA), msort_std(N2, St, B, SB),
                merge_std(SA, SB, St, Sorted) )).

merge_std([], B, _, B).
merge_std([X|Xs], B, St, Out) :-
    merge_std_(B, X, Xs, St, Out).

merge_std_([], X, Xs, _, [X|Xs]).
merge_std_([Y|Ys], X, Xs, St, Out) :-
    compare_std(St, X, Y, O),
    merge_pick(O, X, Xs, Y, Ys, St, Out).

merge_pick(>, X, Xs, Y, Ys, St, [Y|Out]) :-
    merge_std_(Ys, X, Xs, St, Out).
merge_pick(<, X, Xs, Y, Ys, St, [X|Out]) :-
    merge_std(Xs, [Y|Ys], St, Out).
merge_pick(=, X, Xs, Y, Ys, St, [X|Out]) :-
    merge_std(Xs, [Y|Ys], St, Out).

dedup_std(false, _, L, L).
dedup_std(true, St, L, D) :-
    dedup_adj(L, St, D).

dedup_adj([], _, []).
dedup_adj([X|Xs], St, Out) :-
    dedup_adj_(Xs, X, St, Out).

dedup_adj_([], X, _, [X]).
dedup_adj_([Y|Ys], X, St, Out) :-
    compare_std(St, X, Y, O),
    if_commit(O == (=),
              dedup_adj_(Ys, X, St, Out),
              ( Out = [X|Out1], dedup_adj_(Ys, Y, St, Out1) )).

% ---------------------------------------------------------------------------
% format/2

format_b(St, F, As, S) :-
    format_string(St, F, As, E),
    format_out(E, St, S).

format_out(left(M), _, [err(M)]).
format_out(right(T), St, [out(T), ans(St)]).

format_to_b(Sink, F, As, St, S) :-
    format_string(St, F, As, E),
    if_commit(E = left(M),
              S = [err(M)],
              ( E = right(T), walk(Sink, St, W), format_sink(W, T, St, S) )).

format_sink(W, T, St, S) :-
    string_codes(T, Cs),
    atom_codes(A, Cs),
    if_commit(W = comp(atom, [X]), ( unify(X, atom(A), St, M), maybe_stream(M, S) ),
    if_commit(W = comp(string, [X]), ( char_list(A, L), unify(X, L, St, M), maybe_stream(M, S) ),
    if_commit(W = comp(chars, [X]), ( char_list(A, L), unify(X, L, St, M), maybe_stream(M, S) ),
    if_commit(W = comp(codes, [X]),
              ( enc_codes(Cs, Ts), mk_list(Ts, atom('[]'), L), unify(X, L, St, M), maybe_stream(M, S) ),
              type_err('format sink', W, S))))).

%  format_string(+State, +Format, +Args, -Either)
format_string(St, F, As, E) :-
    text_of(St, F, MF),
    if_commit(MF = just(Fmt),
              ( term_to_list(As, St, ML),
                if_commit(ML = just(Args), true, Args = [As]),
                catch(( fmt_go(Fmt, Args, St, Out), string_codes(T, Out), E = right(T) ),
                      fmt_error(M), E = left(M)) ),
              E = left("format/2: bad format")).

fmt_go([], _, _, []).
fmt_go([C|Cs], Args, St, Out) :-
    if_commit(( C =:= 0'~, Cs = [D|Rest] ),
              fmt_directive(D, Rest, Args, St, Out),
              ( Out = [C|Out1], fmt_go(Cs, Args, St, Out1) )).

fmt_directive(D, Rest, Args, St, Out) :-
    if_commit(memberchk(D, `wad`), fmt_arg(show_term, Rest, Args, St, Out),
    if_commit(memberchk(D, `pq`), fmt_arg(show_term_q, Rest, Args, St, Out),
    if_commit(D =:= 0's, fmt_text_arg(Rest, Args, St, Out),
    if_commit(D =:= 0'n, ( Out = [0'\n|Out1], fmt_go(Rest, Args, St, Out1) ),
    if_commit(D =:= 0'~, ( Out = [0'~|Out1], fmt_go(Rest, Args, St, Out1) ),
              ( format(string(M), "format/2: unsupported directive ~~~c", [D]),
                throw(fmt_error(M)) )))))).

fmt_arg(Show, Rest, Args, St, Out) :-
    fmt_take(Args, X, Args1),
    resolve(X, St, R),
    call(Show, R, T),
    string_codes(T, TC),
    fmt_go(Rest, Args1, St, Out1),
    conc(TC, Out1, Out).

fmt_text_arg(Rest, Args, St, Out) :-
    fmt_take(Args, X, Args1),
    text_of(St, X, MT),
    maybe_default(MT, [], TC),
    fmt_go(Rest, Args1, St, Out1),
    conc(TC, Out1, Out).

fmt_take([], _, _) :-
    throw(fmt_error("format/2: not enough arguments")).
fmt_take([X|Xs], X, Xs).

% ---------------------------------------------------------------------------
% The Detlog runtime

member_cp_b(just(_), X, L, St, S) :-
    unify(X, comp(cp, [L]), St, M),
    maybe_stream(M, S).
member_cp_b(nothing, _, L, St, [err(M)]) :-
    resolve(L, St, R),
    show_term_q(R, T),
    format(string(M), "member_cp/2: not a proper list: ~s", [T]).

between_cp_b(Lo, Hi, P, St, S) :-
    eval_arith(St, Lo, RL),
    eval_arith(St, Hi, RH),
    if_commit(( RL = right(ni(L)), RH = right(ni(H)) ),
              ( numlist_det(L, H, Ns), maplist(code_int_term, Ns, Ts),
                mk_list(Ts, atom('[]'), LT), unify(P, comp(cp, [LT]), St, M), maybe_stream(M, S) ),
              S = [err("between_cp/3: needs integer bounds (an infinite packet cannot be spliced)")]).

numlist_det(L, H, Ns) :-
    if_commit(L > H, Ns = [], ( L1 is L + 1, numlist_det(L1, H, Ns1), Ns = [L|Ns1] )).

cp_rows_b(P, Rows, St, S) :-
    walk(P, St, W),
    if_commit(W = comp(cp, [L]),
              ( term_to_list(L, St, ML),
                if_commit(ML = just(Xs),
                          ( flatten_cp(St, Xs, Fs), one_column_t(Fs, Rs),
                            mk_list(Rs, atom('[]'), RT), unify(Rows, RT, St, M), maybe_stream(M, S) ),
                          ( resolve(L, St, RL), type_err(list, RL, S) )) ),
              type_err('choice packet cp/1', W, S)).

one_column_t([], []).
one_column_t([X|Xs], [R|Rs]) :-
    mk_list([X], atom('[]'), R),
    one_column_t(Xs, Rs).

%  Nested packets are spliced inline: cp([1, cp([2,3])]) offers 1, 2, 3.
flatten_cp(St, Xs, Out) :-
    flatten_cp_(Xs, St, Out).

flatten_cp_([], _, []).
flatten_cp_([X|Xs], St, Out) :-
    walk(X, St, W),
    if_commit(( W = comp(cp, [L]), term_to_list(L, St, just(Ys)) ),
              flatten_cp(St, Ys, F),
              F = [W]),
    flatten_cp(St, Xs, Rest),
    conc(F, Rest, Out).

choices_of(St, T, E) :-
    walk(T, St, W),
    if_commit(W = comp(cp, [L]),
              ( term_to_list(L, St, ML),
                if_commit(ML = just(Xs),
                          ( flatten_cp(St, Xs, Fs), E = right(Fs) ),
                          ( resolve(L, St, RL), show_term_q(RL, TS),
                            format(string(M), "splice/2: packet is not a proper list: ~s", [TS]),
                            E = left(M) )) ),
              E = right([W])).

splice_rows(St, Ts, E) :-
    term_to_list(Ts, St, ML),
    if_commit(ML = just(Positions),
              ( choices_all(Positions, St, EC),
                if_commit(EC = right(Cs),
                          ( product_t(Cs, Rows0), maplist(row_term, Rows0, Rows), E = right(Rows) ),
                          E = EC) ),
              E = left("splice/2: first argument must be a proper list")).

choices_all([], _, right([])).
choices_all([P|Ps], St, E) :-
    choices_of(St, P, E1),
    if_commit(E1 = right(C),
              ( choices_all(Ps, St, E2),
                if_commit(E2 = right(Cs), E = right([C|Cs]), E = E2) ),
              E = E1).

row_term(Row, T) :-
    mk_list(Row, atom('[]'), T).

product_t([], [[]]).
product_t([C|Cs], Rows) :-
    product_t(Cs, Rest),
    findall([X|R], ( member(X, C), member(R, Rest) ), Rows).

splice_b(left(M), _, _, [err(M)]).
splice_b(right(Rs), Rows, St, S) :-
    mk_list(Rs, atom('[]'), T),
    unify(Rows, T, St, M),
    maybe_stream(M, S).

splice_first_b(left(M), _, _, [err(M)]).
splice_first_b(right(Rs), Row, St, S) :-
    if_commit(Rs = [R|_], ( unify(Row, R, St, M), maybe_stream(M, S) ), S = []).

%  splice_extend(+Rows, +Env, +Pattern, -Out): for every row, a fresh copy
%  of Env-Pattern; when the Pattern copy unifies with the row, the Env copy
%  (resolved) is kept.  out(Text) items are kept in place.
splice_extend_b(Rows, Env, Pat, Out, St, S) :-
    term_to_list(Rows, St, ML),
    if_commit(ML = just(Rs),
              ( foldl(extend_step(Env, Pat), Rs, []-St, OutsRev-St1),
                rev(OutsRev, Outs),
                mk_list(Outs, atom('[]'), T),
                unify(Out, T, St1, M), maybe_stream(M, S) ),
              ( resolve(Rows, St, RR), show_term_q(RR, TS),
                format(string(M), "splice_extend/4: rows are not a proper list: ~s", [TS]),
                S = [err(M)] )).

extend_step(Env, Pat, R, Acc-St, Acc1-St1) :-
    walk(R, St, W),
    if_commit(W = comp(out, [_]),
              ( resolve(R, St, RR), Acc1 = [RR|Acc], St1 = St ),
              ( copy_term_st(St, comp('-', [Env, Pat]), C, Sa),
                C = comp('-', [E1, P1]),
                unify(P1, R, Sa, M),
                extend_keep(M, E1, Acc, Sa, Acc1, St1) )).

extend_keep(nothing, _, Acc, Sa, Acc, Sa).
extend_keep(just(S2), E1, Acc, Sa, [RE|Acc], St1) :-
    resolve(E1, S2, RE),
    st_next(S2, N),
    st_set_next(N, Sa, St1).

rows_concat_b(Ls, Out, St, S) :-
    term_to_list(Ls, St, ML),
    if_commit(( ML = just(Parts0), lists_all(Parts0, St, Parts) ),
              ( concat_lists(Parts, All), mk_list(All, atom('[]'), T),
                unify(Out, T, St, M), maybe_stream(M, S) ),
              ( resolve(Ls, St, RL), show_term_q(RL, TS),
                format(string(M), "rows_concat/2: expected a list of proper lists: ~s", [TS]),
                S = [err(M)] )).

%  semidet: every element is a proper list
lists_all([], _, []).
lists_all([P|Ps], St, [L|Ls]) :-
    term_to_list(P, St, just(L)),
    lists_all(Ps, St, Ls).

cp_filter_b(W, Pat, Out, St, S) :-
    if_commit(W = comp(cp, [Rows]),
              splice_extend_b(Rows, Pat, Pat, Out, St, S),
              type_err('choice packet cp/1', W, S)).

%  True when the argument groups share no unbound variables.
splice_safe_b(Gs, St, S) :-
    term_to_list(Gs, St, ML),
    if_commit(ML = just(Groups),
              ( maplist(group_var_ids(St), Groups, Sets),
                disjoint_sets_b(Sets, B),
                bool_stream(B, St, S) ),
              S = []).

group_var_ids(St, G, Ids) :-
    resolve(G, St, R),
    term_vars_ordered(R, Vs),
    var_ids(Vs, Ids).

disjoint_sets_b([], true).
disjoint_sets_b([S|Ss], B) :-
    test(( member(T, Ss), member(I, S), memberchk(I, T) ), Shared),
    bool_not(Shared, B1),
    disjoint_sets_b(Ss, B2),
    bool_and(B1, B2, B).

memo_lookup_b(Args, Table, Rows, St, S) :-
    term_to_list(Table, St, ML),
    if_commit(ML = just(Entries),
              memo_go(Entries, Args, Rows, St, S),
              ( resolve(Table, St, RT), type_err('memo table', RT, S) )).

memo_go([], _, _, _, []).
memo_go([E|Es], Args, Rows, St, S) :-
    term_to_list(E, St, ME),
    if_commit(( ME = just([Pat, Rs]), variant_t(St, Pat, Args, true) ),
              ( copy_term_st(St, Rs, C, St1), unify(Rows, C, St1, M), maybe_stream(M, S) ),
              memo_go(Es, Args, Rows, St, S)).

%  s2a_rows(+Spec, ?Args, -Rows): the rows of an S2A loop (unfold.pl) that
%  unify with Args.
s2a_rows_b(Spec, Args, Rows, St, S) :-
    resolve(Spec, St, RS),
    resolve(Args, St, RA),
    if_commit(( spec_parts(RS, just(K-Cols)), static_list(RA, just(AL)) ),
              ( spec_select(K, Cols, AL, Sel),
                maplist(list_t, Sel, SelTs),
                mk_list(SelTs, atom('[]'), T),
                splice_extend_b(T, Args, Args, Rows, St, S) ),
              type_err('S2A spec s2a(K, Columns) and an argument list', RS, S)).

%  length/2 restricted to its deterministic modes.
length_det_b(L, N, St, S) :-
    partial_list(L, St, _, End),
    walk(N, St, WN),
    if_commit(( End = var(_, _), WN = var(_, _) ),
              S = [err("length_det/2: list and length both unbound (that mode needs a choicepoint)")],
              length_b(L, N, St, S)).

%  builtin_rows(+Goal, -Rows): all answers of a built-in goal as one packet
%  [[Goal1], [Goal2], ...].
builtin_rows_b(W, Rows, St, S) :-
    if_commit(W = comp(F, As),
              ( builtin(F, As, St, MB),
                if_commit(MB = just(BS),
                          ( stream_list(BS, Evs),
                            if_commit(memberchk(err(E), Evs),
                                      S = [err(E)],
                                      ( answers_of(Evs, Sts),
                                        maplist(goal_row(comp(F, As)), Sts, Rs),
                                        copy_all(St, Rs, Copies, St1),
                                        outs_of(Evs, Outs),
                                        mk_list(Copies, atom('[]'), T),
                                        unify(Rows, T, St1, M), maybe_stream(M, S1),
                                        conc(Outs, S1, S) )) ),
                          ( format(string(M), "builtin_rows/2: not a built-in: ~w", [F]), S = [err(M)] )) ),
              type_err('built-in goal', W, S)).

goal_row(G, St, Row) :-
    resolve(G, St, R),
    mk_list([R], atom('[]'), Row).

outs_of([], []).
outs_of([E|Es], Out) :-
    outs_of(Es, Rest),
    out_ev(E, Rest, Out).

out_ev(out(O), Rest, [out(O)|Rest]).
out_ev(ans(_), Rest, Rest).
out_ev(err(_), Rest, Rest).

%  effect_text(+Goal, -Text): the text an output built-in would write.
effect_text_b(G, Txt, St, S) :-
    walk(G, St, W),
    goal_key(W, MK),
    effect_keys(EK),
    if_commit(( MK = just(F/N), key_atom(F, N, K), memberchk(K, EK) ),
              ( goal_args(W, As), builtin(F, As, St, just(BS)), stream_list(BS, Evs),
                if_commit(memberchk(err(E), Evs),
                          S = [err(E)],
                          ( outs_of(Evs, Outs), out_texts(Outs, Ts),
                            atomic_list_concat(Ts, A),
                            unify(Txt, atom(A), St, M), maybe_stream(M, S) )) ),
              type_err('output built-in', W, S)).

out_texts([], []).
out_texts([out(T)|Os], [T|Ts]) :-
    out_texts(Os, Ts).

is_out_item(St, T, B) :-
    walk(T, St, W),
    test(W = comp(out, [_]), B).

%  packet_first(+Packet, -OutsBefore, -Result)
packet_first_b(P, Pre, Res, St, S) :-
    term_to_list(P, St, ML),
    if_commit(ML = just(Items),
              ( span_out(Items, St, Outs, Rest),
                if_commit(Rest = [Row|_], R = comp(first, [Row]), R = atom(none)),
                mk_list(Outs, atom('[]'), OT),
                unify(Pre, OT, St, M1), unify_then(Res, R, M1, M), maybe_stream(M, S) ),
              ( resolve(P, St, RP), type_err(packet, RP, S) )).

span_out([], _, [], []).
span_out([X|Xs], St, Outs, Rest) :-
    is_out_item(St, X, B),
    span_out_(B, X, Xs, St, Outs, Rest).

span_out_(false, X, Xs, _, [], [X|Xs]).
span_out_(true, X, Xs, St, [X|Outs], Rest) :-
    span_out(Xs, St, Outs, Rest).

%  packet_split(+Packet, -Outs, -Rows)
packet_split_b(P, Outs, Rows, St, S) :-
    term_to_list(P, St, ML),
    if_commit(ML = just(Items),
              ( partition_out(Items, St, Os, Rs),
                mk_list(Os, atom('[]'), OT), mk_list(Rs, atom('[]'), RT),
                unify(Outs, OT, St, M1), unify_then(Rows, RT, M1, M), maybe_stream(M, S) ),
              ( resolve(P, St, RP), type_err(packet, RP, S) )).

partition_out([], _, [], []).
partition_out([X|Xs], St, Os, Rs) :-
    is_out_item(St, X, B),
    partition_out_(B, X, Os, Rs, Os1, Rs1),
    partition_out(Xs, St, Os1, Rs1).

partition_out_(true, X, [X|Os], Rs, Os, Rs).
partition_out_(false, X, Os, [X|Rs], Os, Rs).
