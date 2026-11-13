/*  reader.pl - a small standard-Prolog reader: tokens, operator-precedence
    parsing, and programs as ordered clause lists.

    Strings ("...") are character lists, back-quoted text is a code list.
    Errors are thrown as parse_error(Message) and turned into left(Message)
    by parse_program/2, parse_term_string/2 and parse_query/2.

    A program is prog(Preds, Order, Directives): Preds maps Name/Arity to
    its clauses clause(Head, Body, NVars) (variables numbered 0..NVars-1),
    and Order lists the keys in order of first appearance.
*/

% ---------------------------------------------------------------------------
% Operators

infix_op(':-', 1200, xfx).
infix_op('-->', 1200, xfx).
infix_op(';', 1100, xfy).
infix_op('|', 1100, xfy).
infix_op('->', 1050, xfy).
infix_op('*->', 1050, xfy).
infix_op(',', 1000, xfy).
infix_op('=', 700, xfx).
infix_op('\\=', 700, xfx).
infix_op('==', 700, xfx).
infix_op('\\==', 700, xfx).
infix_op('@<', 700, xfx).
infix_op('@>', 700, xfx).
infix_op('@=<', 700, xfx).
infix_op('@>=', 700, xfx).
infix_op('=..', 700, xfx).
infix_op(is, 700, xfx).
infix_op('=:=', 700, xfx).
infix_op('=\\=', 700, xfx).
infix_op('<', 700, xfx).
infix_op('>', 700, xfx).
infix_op('=<', 700, xfx).
infix_op('>=', 700, xfx).
infix_op('=@=', 700, xfx).
infix_op('\\=@=', 700, xfx).
infix_op(':', 200, xfy).
infix_op('+', 500, yfx).
infix_op('-', 500, yfx).
infix_op('/\\', 500, yfx).
infix_op('\\/', 500, yfx).
infix_op(xor, 500, yfx).
infix_op('*', 400, yfx).
infix_op('/', 400, yfx).
infix_op('//', 400, yfx).
infix_op(mod, 400, yfx).
infix_op(rem, 400, yfx).
infix_op('<<', 400, yfx).
infix_op('>>', 400, yfx).
infix_op(div, 400, yfx).
infix_op('**', 200, xfx).
infix_op('^', 200, xfy).

prefix_op(':-', 1200, fx).
prefix_op('?-', 1200, fx).
prefix_op('\\+', 900, fy).
prefix_op('-', 200, fy).
prefix_op('+', 200, fy).
prefix_op('\\', 200, fy).
prefix_op(dynamic, 1150, fx).
prefix_op(discontiguous, 1150, fx).

%  infix_lookup(+Name, -Maybe): just(Priority-Assoc) or nothing.
infix_lookup(N, M) :-
    if_commit(infix_op(N, P, A), M = just(P-A), M = nothing).

prefix_lookup(N, M) :-
    if_commit(prefix_op(N, P, A), M = just(P-A), M = nothing).

is_infix(N, B) :-
    test(infix_op(N, _, _), B).

is_prefix(N, B) :-
    test(prefix_op(N, _, _), B).

% ---------------------------------------------------------------------------
% Characters

is_space_c(C) :-
    code_type(C, space).

is_lower_c(C) :-
    code_type(C, lower(_)).

is_upper_c(C) :-
    code_type(C, upper(_)).

is_digit_c(C) :-
    C >= 0'0,
    C =< 0'9.

is_alnum_u(C) :-
    code_type(C, csym).

is_hex_c(C) :-
    code_type(C, xdigit(_)).

is_sym_c(C) :-
    memberchk(C, `+-*/\\^<>=~:.?@#&$`).

%  span_codes(:Test, +Codes, -Prefix, -Rest)
span_codes(_, [], [], []).
span_codes(P, [C|Cs], Pre, Rest) :-
    test(call(P, C), B),
    span_b(B, C, Cs, P, Pre, Rest).

span_b(false, C, Cs, _, [], [C|Cs]).
span_b(true, C, Cs, P, [C|Pre], Rest) :-
    span_codes(P, Cs, Pre, Rest).

% ---------------------------------------------------------------------------
% Lexer: tokens tok(Token, Line)
%   name(N) funct(N) var(N) int(I) flt(F) str(Codes) backq(Codes) punct(P) end

lex([], _, []).
lex([C|Cs], Ln, Toks) :-
    char_class(C, Cs, Class),
    lex_class(Class, C, Cs, Ln, Toks).

char_class(C, Cs, Class) :-
    if_commit(C =:= 0'\n, Class = newline,
    if_commit(is_space_c(C), Class = space,
    if_commit(C =:= 0'%, Class = comment,
    if_commit(( C =:= 0'/, Cs = [0'*|_] ), Class = block,
    if_commit(is_lower_c(C), Class = lower,
    if_commit(upper_or_us(C), Class = upper,
    if_commit(is_digit_c(C), Class = digit,
    if_commit(C =:= 0'\', Class = squote,
    if_commit(C =:= 0'", Class = dquote,
    if_commit(C =:= 0'`, Class = bquote,
    if_commit(memberchk(C, `()[]{},|`), Class = punct,
    if_commit(C =:= 0'!, Class = bang,
    if_commit(C =:= 0';, Class = semi,
    if_commit(( C =:= 0'., end_follows(Cs) ), Class = end,
    if_commit(is_sym_c(C), Class = sym,
              Class = other))))))))))))))).

end_follows([]).
end_follows([D|_]) :-
    if_commit(D =:= 0'%, true, is_space_c(D)).

upper_or_us(C) :-
    if_commit(C =:= 0'_, true, is_upper_c(C)).

lex_class(newline, _, Cs, Ln, Toks) :-
    Ln1 is Ln + 1,
    lex(Cs, Ln1, Toks).
lex_class(space, _, Cs, Ln, Toks) :-
    lex(Cs, Ln, Toks).
lex_class(comment, _, Cs, Ln, Toks) :-
    span_codes(not_newline, Cs, _, Rest),
    lex(Rest, Ln, Toks).
lex_class(block, _, [_|Cs], Ln, Toks) :-
    skip_block(Cs, Ln, Toks).
lex_class(lower, C, Cs, Ln, Toks) :-
    span_codes(is_alnum_u, [C|Cs], W, Rest),
    atom_codes(N, W),
    name_tok(N, Rest, Ln, Ln, Toks).
lex_class(upper, C, Cs, Ln, [tok(var(N), Ln)|Toks]) :-
    span_codes(is_alnum_u, [C|Cs], W, Rest),
    atom_codes(N, W),
    lex(Rest, Ln, Toks).
lex_class(digit, C, Cs, Ln, Toks) :-
    lex_number([C|Cs], Ln, Toks).
lex_class(squote, _, Cs, Ln, Toks) :-
    quoted(0'\', Ln, Cs, Str, Rest, Ln1),
    atom_codes(N, Str),
    name_tok(N, Rest, Ln1, Ln1, Toks).
lex_class(dquote, _, Cs, Ln, [tok(str(Str), Ln)|Toks]) :-
    quoted(0'", Ln, Cs, Str, Rest, Ln1),
    lex(Rest, Ln1, Toks).
lex_class(bquote, _, Cs, Ln, [tok(backq(Str), Ln)|Toks]) :-
    quoted(0'`, Ln, Cs, Str, Rest, Ln1),
    lex(Rest, Ln1, Toks).
lex_class(punct, C, Cs, Ln, [tok(punct(P), Ln)|Toks]) :-
    char_code(P, C),
    lex(Cs, Ln, Toks).
lex_class(bang, _, Cs, Ln, Toks) :-
    name_tok('!', Cs, Ln, Ln, Toks).
lex_class(semi, _, Cs, Ln, Toks) :-
    name_tok(';', Cs, Ln, Ln, Toks).
lex_class(end, _, Cs, Ln, [tok(end, Ln)|Toks]) :-
    lex(Cs, Ln, Toks).
lex_class(sym, C, Cs, Ln, Toks) :-
    span_codes(is_sym_c, [C|Cs], W, Rest),
    atom_codes(N, W),
    name_tok(N, Rest, Ln, Ln, Toks).
lex_class(other, C, _, Ln, _) :-
    format(string(M), "line ~d: unexpected character ~w", [Ln, C]),
    parse_fail_raw(M).

not_newline(C) :-
    C =\= 0'\n.

%  A name followed directly by "(" is a functor.
name_tok(N, Rest, L, Ln, [tok(T, L)|Toks]) :-
    if_commit(Rest = [0'(|_], T = funct(N), T = name(N)),
    lex(Rest, Ln, Toks).

skip_block([], Ln, _) :-
    format(string(M), "line ~d: unterminated block comment", [Ln]),
    parse_fail_raw(M).
skip_block([C|Cs], Ln, Toks) :-
    if_commit(( C =:= 0'*, Cs = [0'/|Rest] ),
              lex(Rest, Ln, Toks),
              if_commit(C =:= 0'\n,
                        ( Ln1 is Ln + 1, skip_block(Cs, Ln1, Toks) ),
                        skip_block(Cs, Ln, Toks))).

lex_number(Str, Ln, Toks) :-
    if_commit(Str = [0'0, 0'\'|Rest],
              char_code_tok(Rest, Ln, Toks),
              if_commit(( Str = [0'0, 0'x|Rest], Rest = [H|_], is_hex_c(H) ),
                        ( span_codes(is_hex_c, Rest, Hs, Rest1),
                          atom_codes(HA, [0'0, 0'x|Hs]),
                          atom_number(HA, I),
                          Toks = [tok(int(I), Ln)|Toks1],
                          lex(Rest1, Ln, Toks1) ),
                        decimal(Str, Ln, Toks))).

decimal(Str, Ln, Toks) :-
    span_codes(is_digit_c, Str, Ds, Rest),
    if_commit(( Rest = [0'., D|Rest2], is_digit_c(D) ),
              ( span_codes(is_digit_c, [D|Rest2], Fs, Rest3),
                expo(Rest3, Ex, Rest4),
                concat_lists([Ds, `.`, Fs, Ex], FC),
                number_codes(F, FC),
                Toks = [tok(flt(F), Ln)|Toks1],
                lex(Rest4, Ln, Toks1) ),
              ( number_codes(I, Ds),
                Toks = [tok(int(I), Ln)|Toks1],
                lex(Rest, Ln, Toks1) )).

expo(Cs, Ex, Rest) :-
    if_commit(( Cs = [E, S, D|More], memberchk(E, `eE`), memberchk(S, `+-`), is_digit_c(D) ),
              ( span_codes(is_digit_c, [D|More], Ds, Rest),
                sign_part(S, SP),
                concat_lists([`e`, SP, Ds], Ex) ),
              if_commit(( Cs = [E, D|More], memberchk(E, `eE`), is_digit_c(D) ),
                        ( span_codes(is_digit_c, [D|More], Ds, Rest),
                          conc(`e`, Ds, Ex) ),
                        ( Ex = [], Rest = Cs ))).

sign_part(S, SP) :-
    if_commit(S =:= 0'-, SP = `-`, SP = []).

char_code_tok(Rest, Ln, Toks) :-
    if_commit(Rest = [0'\\, E|More],
              ( escape(E, C), Toks = [tok(int(C), Ln)|Toks1], lex(More, Ln, Toks1) ),
              if_commit(Rest = [0'\', 0'\'|More],
                        ( Toks = [tok(int(39), Ln)|Toks1], lex(More, Ln, Toks1) ),
                        if_commit(Rest = [Ch|More],
                                  ( Toks = [tok(int(Ch), Ln)|Toks1], lex(More, Ln, Toks1) ),
                                  ( format(string(M), "line ~d: bad character code", [Ln]),
                                    parse_fail_raw(M) )))).

escape(E, C) :-
    if_commit(escape_code(E, C0), C = C0, C = E).

escape_code(0'n, 10).
escape_code(0't, 9).
escape_code(0'r, 13).
escape_code(0'a, 7).
escape_code(0'b, 8).
escape_code(0'f, 12).
escape_code(0'v, 11).
escape_code(0'0, 0).
escape_code(0's, 32).
escape_code(0'e, 27).

%  quoted(+Quote, +Line, +Codes, -Text, -Rest, -Line)
quoted(Q, Ln, Cs, Str, Rest, Ln1) :-
    quoted_(Cs, Q, Ln, [], Str, Rest, Ln1).

quoted_([], _, Ln, _, _, _, _) :-
    format(string(M), "line ~d: unterminated quoted item", [Ln]),
    parse_fail_raw(M).
quoted_([C|Cs], Q, Ln, Acc, Str, Rest, Ln1) :-
    if_commit(( C =:= Q, Cs = [D|Cs1], D =:= Q ),
              quoted_(Cs1, Q, Ln, [Q|Acc], Str, Rest, Ln1),
    if_commit(C =:= Q,
              ( rev(Acc, Str), Rest = Cs, Ln1 = Ln ),
    if_commit(( C =:= 0'\\, Cs = [0'\n|Cs1] ),
              ( L2 is Ln + 1, quoted_(Cs1, Q, L2, Acc, Str, Rest, Ln1) ),
    if_commit(( C =:= 0'\\, Cs = [E|Cs1] ),
              ( escape(E, EC), quoted_(Cs1, Q, Ln, [EC|Acc], Str, Rest, Ln1) ),
    if_commit(C =:= 0'\n,
              ( L2 is Ln + 1, quoted_(Cs, Q, L2, [C|Acc], Str, Rest, Ln1) ),
              quoted_(Cs, Q, Ln, [C|Acc], Str, Rest, Ln1)))))).

% ---------------------------------------------------------------------------
% Parser.  The state is ps(Tokens, Vars, Next): the remaining tokens, the
% named variables of the clause (a map from name to id) and the next id.

parse_fail_raw(M) :-
    throw(parse_error(M)).

parse_fail(M, ps(Toks, _, _)) :-
    fail_where(Toks, W),
    string_concat(W, M, Msg),
    throw(parse_error(Msg)).

fail_where([], "end of input: ").
fail_where([tok(_, L)|_], W) :-
    format(string(W), "line ~d: ", [L]).

peek(ps(Toks, _, _), M) :-
    head_tok(Toks, M).

head_tok([], nothing).
head_tok([tok(T, _)|_], just(T)).

peek2(ps(Toks, _, _), M) :-
    second_tok(Toks, M).

second_tok([], nothing).
second_tok([_|Ts], M) :-
    head_tok(Ts, M).

advance(ps(Toks, V, N), ps(Toks1, V, N)) :-
    drop(1, Toks, Toks1).

next_tok(S0, T, S) :-
    peek(S0, M),
    next_tok_(M, S0, T, S).

next_tok_(nothing, S0, _, _) :-
    parse_fail("unexpected end of input", S0).
next_tok_(just(T), S0, T, S) :-
    advance(S0, S).

expect(T, S0, S) :-
    next_tok(S0, T1, S),
    if_commit(T1 == T,
              true,
              ( show_tok(T, A), show_tok(T1, B),
                format(string(M), "expected ~w but found ~w", [A, B]),
                parse_fail(M, S) )).

show_tok(name(N), N).
show_tok(funct(N), S) :-
    format(string(S), "~w(", [N]).
show_tok(var(N), N).
show_tok(int(I), I).
show_tok(flt(F), F).
show_tok(str(Cs), S) :-
    format(string(S), "~q", [Cs]).
show_tok(backq(Cs), S) :-
    format(string(S), "~q", [Cs]).
show_tok(punct(P), P).
show_tok(end, "end of clause").

var_for(N, ps(T, Vs, I), V, S) :-
    if_commit(N == '_',
              ( V = var(I, '_'), I1 is I + 1, S = ps(T, Vs, I1) ),
              ( map_get(Vs, N, M), var_named(M, N, ps(T, Vs, I), V, S) )).

var_named(just(J), N, S, var(J, N), S).
var_named(nothing, N, ps(T, Vs, I), var(I, N), ps(T, Vs1, I1)) :-
    map_put(N, I, Vs, Vs1),
    I1 is I + 1.

%  pterm(+MaxPriority, -Term, -Priority, +S0, -S)
pterm(MaxP, T, P, S0, S) :-
    primary(MaxP, L, LP, S0, S1),
    infix_loop(MaxP, L, LP, T, P, S1, S).

infix_loop(MaxP, L, LP, T, P, S0, S) :-
    peek(S0, MT),
    op_name(MT, MN),
    op_info(MN, MI),
    infix_step(MI, MaxP, L, LP, T, P, S0, S).

op_name(nothing, nothing).
op_name(just(T), M) :-
    if_commit(T = name(N), M = just(N),
              if_commit(T = punct(','), M = just(','),
                        if_commit(T = punct('|'), M = just('|'), M = nothing))).

op_info(nothing, nothing).
op_info(just(N), M) :-
    infix_lookup(N, MI),
    op_info_(MI, N, M).

op_info_(nothing, _, nothing).
op_info_(just(P-A), N, just(N-P-A)).

infix_step(nothing, _, L, LP, L, LP, S, S).
infix_step(just(N-P-A), MaxP, L, LP, T, TP, S0, S) :-
    arg_priorities(A, P, LA, RA),
    if_commit(( P =< MaxP, LP =< LA ),
              ( advance(S0, S1),
                pterm(RA, R, _, S1, S2),
                if_commit(N == '|', N1 = ';', N1 = N),
                infix_loop(MaxP, comp(N1, [L, R]), P, T, TP, S2, S) ),
              ( T = L, TP = LP, S = S0 )).

arg_priorities(xfx, P, LA, RA) :-
    LA is P - 1,
    RA is P - 1.
arg_priorities(xfy, P, LA, P) :-
    LA is P - 1.
arg_priorities(yfx, P, P, RA) :-
    RA is P - 1.

can_start(nothing, false).
can_start(just(T), B) :-
    can_start_tok(T, B).

can_start_tok(name(N), B) :-
    is_infix(N, I),
    is_prefix(N, Pr),
    bool_not(Pr, NPr),
    bool_and(I, NPr, InfixOnly),
    bool_not(InfixOnly, B).
can_start_tok(funct(_), true).
can_start_tok(var(_), true).
can_start_tok(int(_), true).
can_start_tok(flt(_), true).
can_start_tok(str(_), true).
can_start_tok(backq(_), true).
can_start_tok(punct(P), B) :-
    test(memberchk(P, ['(', '[', '{']), B).
can_start_tok(end, false).

primary(MaxP, T, P, S0, S) :-
    next_tok(S0, Tok, S1),
    primary_tok(Tok, MaxP, T, P, S1, S).

primary_tok(int(I), _, int(I), 0, S, S).
primary_tok(flt(F), _, flt(F), 0, S, S).
primary_tok(var(N), _, V, 0, S0, S) :-
    var_for(N, S0, V, S).
primary_tok(str(Cs), _, T, 0, S, S) :-
    atom_codes(A, Cs),
    char_list(A, T).
primary_tok(backq(Cs), _, T, 0, S, S) :-
    ints(Cs, Is),
    mk_list(Is, atom('[]'), T).
primary_tok(punct(P), _, T, Pr, S0, S) :-
    primary_punct(P, T, Pr, S0, S).
primary_tok(funct(N), _, comp(N, Args), 0, S0, S) :-
    expect(punct('('), S0, S1),
    arg_list(Args, S1, S2),
    expect(punct(')'), S2, S).
primary_tok(name(N), MaxP, T, P, S0, S) :-
    peek(S0, MT),
    primary_name(N, MT, MaxP, T, P, S0, S).
primary_tok(end, _, _, _, S0, _) :-
    parse_fail("unexpected end of clause", S0).

ints([], []).
ints([C|Cs], [int(C)|Is]) :-
    ints(Cs, Is).

primary_punct(P, T, Pr, S0, S) :-
    if_commit(P == '(',
              ( pterm(1200, T, _, S0, S1), expect(punct(')'), S1, S), Pr = 0 ),
    if_commit(P == '[',
              ( list_term(T, S0, S), Pr = 0 ),
    if_commit(P == '{',
              ( curly_term(T, S0, S), Pr = 0 ),
              ( format(string(M), "unexpected ~q", [P]), parse_fail(M, S0) )))).

list_term(T, S0, S) :-
    peek(S0, MT),
    if_commit(MT == just(punct(']')),
              ( advance(S0, S), T = atom('[]') ),
              ( arg_list(Items, S0, S1),
                peek(S1, MT2),
                if_commit(MT2 == just(punct('|')),
                          ( advance(S1, S2), pterm(999, Tl, _, S2, S3) ),
                          ( Tl = atom('[]'), S3 = S1 )),
                expect(punct(']'), S3, S),
                mk_list(Items, Tl, T) )).

curly_term(T, S0, S) :-
    peek(S0, MT),
    if_commit(MT == just(punct('}')),
              ( advance(S0, S), T = atom('{}') ),
              ( pterm(1200, X, _, S0, S1),
                expect(punct('}'), S1, S),
                T = comp('{}', [X]) )).

primary_name(N, MT, MaxP, T, P, S0, S) :-
    if_commit(( N == '-', MT = just(int(I)) ),
              ( advance(S0, S), NI is -I, T = int(NI), P = 0 ),
    if_commit(( N == '-', MT = just(flt(F)) ),
              ( advance(S0, S), NF is -F, T = flt(NF), P = 0 ),
              ( prefix_lookup(N, MP),
                can_start(MT, CS),
                prefix_use(MP, CS, N, MT, MaxP, T, P, S0, S) ))).

prefix_use(nothing, _, N, _, _, atom(N), 0, S, S).
prefix_use(just(PP-PA), CS, N, MT, MaxP, T, P, S0, S) :-
    prefix_use_(CS, PP, PA, N, MT, MaxP, T, P, S0, S).

prefix_use_(false, _, _, N, _, _, atom(N), 0, S, S).
prefix_use_(true, PP, PA, N, MT, MaxP, T, P, S0, S) :-
    % an operator followed by an infix operator is an atom: (- = x)
    if_commit(( MT = just(name(M)), infix_only(M) ),
              ( T = atom(N), P = 0, S = S0 ),
              ( P is min(PP, MaxP),
                prefix_arg_max(PA, P, ArgMax),
                pterm(ArgMax, Arg, _, S0, S),
                T = comp(N, [Arg]) )).

infix_only(M) :-
    infix_op(M, _, _),
    if_commit(prefix_op(M, _, _), fail, true).

prefix_arg_max(fy, P, P).
prefix_arg_max(fx, P, A) :-
    A is P - 1.

arg_list(Args, S0, S) :-
    pterm(999, X, _, S0, S1),
    peek(S1, MT),
    if_commit(MT == just(punct(',')),
              ( advance(S1, S2), arg_list(Xs, S2, S), Args = [X|Xs] ),
              ( Args = [X], S = S1 )).

%  read_clause_term(-Maybe, +S0, -S): just(Term-Vars-NVars), or nothing at
%  the end of the tokens.
read_clause_term(M, S0, S) :-
    peek(S0, MT),
    read_clause_(MT, M, S0, S).

read_clause_(nothing, nothing, S, S).
read_clause_(just(_), just(T-Vs-N), ps(Toks, _, _), S) :-
    map_empty(E),
    pterm(1200, T, _, ps(Toks, E, 0), S1),
    expect(end, S1, S),
    S = ps(_, Vs, N).

read_all_terms(Ts, S0, S) :-
    read_clause_term(M, S0, S1),
    read_all_(M, Ts, S1, S).

read_all_(nothing, [], S, S).
read_all_(just(X), [X|Xs], S0, S) :-
    read_all_terms(Xs, S0, S).

%  parse_terms(+Text, -Terms): throws parse_error(Message).
parse_terms(Src, Ts) :-
    string_codes(Src, Cs),
    lex(Cs, 1, Toks),
    map_empty(E),
    read_all_terms(Ts, ps(Toks, E, 0), _).

% ---------------------------------------------------------------------------
% Programs

empty_program(prog(E, [], [])) :-
    map_empty(E).

%  program_clauses(+Program, -KeyedClauses): [Key-Clauses, ...] in order.
program_clauses(prog(Preds, Order, _), KCs) :-
    keyed_clauses(Order, Preds, KCs).

keyed_clauses([], _, []).
keyed_clauses([K|Ks], Preds, [K-Cs|KCs]) :-
    map_find(Preds, K, [], Cs),
    keyed_clauses(Ks, Preds, KCs).

program_from_clauses(Cls, P) :-
    empty_program(P0),
    foldl(add_clause, Cls, P0, P).

add_clause(C, P0, P) :-
    C = clause(H, _, _),
    goal_key(H, MK),
    add_clause_(MK, C, P0, P).

add_clause_(nothing, _, P, P).
add_clause_(just(K), C, prog(Preds, Order, Ds), P) :-
    map_get(Preds, K, M),
    add_clause_key(M, K, C, prog(Preds, Order, Ds), P).

add_clause_key(just(Cs), K, C, prog(Preds, Order, Ds), prog(Preds1, Order, Ds)) :-
    conc(Cs, [C], Cs1),
    map_put(K, Cs1, Preds, Preds1).
add_clause_key(nothing, K, C, prog(Preds, Order, Ds), prog(Preds1, Order1, Ds)) :-
    map_put(K, [C], Preds, Preds1),
    conc(Order, [K], Order1).

prog_preds(prog(P, _, _), P).
prog_order(prog(_, O, _), O).
prog_directives(prog(_, _, D), D).

%  prog_lookup(+Program, +Key, -MaybeClauses)
prog_lookup(prog(P, _, _), K, M) :-
    map_get(P, K, M).

%  parse_program(+Text, -Either): right(Program) or left(Message).
parse_program(Src, E) :-
    catch(( parse_terms(Src, Ts),
            foldl(program_step, Ts, []-[], Cls-Ds),
            check_heads(Cls),
            program_from_clauses(Cls, prog(Pr, Or, _)),
            E = right(prog(Pr, Or, Ds)) ),
          parse_error(M),
          E = left(M)).

program_step(T-_-N, Cls0-Ds0, Cls-Ds) :-
    term_clause_kind(T, K),
    program_step_(K, T, N, Cls0-Ds0, Cls-Ds).

term_clause_kind(T, K) :-
    if_commit(T = comp(':-', [_]), K = directive,
    if_commit(T = comp('?-', [_]), K = directive,
    if_commit(T = comp(':-', [_, _]), K = rule,
    if_commit(T = comp('-->', _), K = dcg,
              K = fact)))).

program_step_(directive, comp(_, [D]), _, Cls-Ds0, Cls-Ds) :-
    conc(Ds0, [D], Ds).
program_step_(rule, comp(':-', [H, B]), N, Cls0-Ds, Cls-Ds) :-
    body_vars_to_call(B, B1),
    conc(Cls0, [clause(H, B1, N)], Cls).
program_step_(dcg, T, _, Cls-Ds0, Cls-Ds) :-
    conc(Ds0, [T], Ds).
program_step_(fact, H, N, Cls0-Ds, Cls-Ds) :-
    conc(Cls0, [clause(H, atom(true), N)], Cls).

check_heads([]).
check_heads([clause(H, _, _)|Cs]) :-
    is_callable_t(H, B),
    check_head(B, H),
    check_heads(Cs).

check_head(true, _).
check_head(false, H) :-
    format(string(M), "clause head is not callable: ~q", [H]),
    throw(parse_error(M)).

%  A variable used as a goal means call/1.
body_vars_to_call(var(I, N), comp(call, [var(I, N)])).
body_vars_to_call(atom(A), atom(A)).
body_vars_to_call(int(I), int(I)).
body_vars_to_call(flt(F), flt(F)).
body_vars_to_call(comp(F, As), T) :-
    if_commit(( memberchk(F, [',', ';', '->', '*->']), As = [A, B] ),
              ( body_vars_to_call(A, A1), body_vars_to_call(B, B1), T = comp(F, [A1, B1]) ),
              if_commit(( F == '\\+', As = [A] ),
                        ( body_vars_to_call(A, A1), T = comp(F, [A1]) ),
                        T = comp(F, As))).

%  parse_term_string(+Text, -Either): right(Term-Vars-NVars) where Vars is
%  [Name-Var, ...] in order of id.
parse_term_string(Src, E) :-
    catch(( string_codes(Src, Cs0),
            rev(Cs0, R0),
            span_codes(is_space_c, R0, _, R1),
            rev(R1, Cs1),
            with_dot(Cs1, Cs2),
            string_codes(S2, Cs2),
            parse_terms(S2, Ts),
            one_term(Ts, E) ),
          parse_error(M),
          E = left(M)).

with_dot(Cs, Out) :-
    if_commit(( Cs \== [], last_code(Cs, 0'.) ),
              conc(Cs, `\n`, Out),
              conc(Cs, ` .\n`, Out)).

last_code([X|Xs], C) :-
    last_code_(Xs, X, C).

last_code_([], X, X).
last_code_([Y|Ys], _, C) :-
    last_code_(Ys, Y, C).

one_term(Ts, E) :-
    if_commit(Ts = [T-Vm-N],
              ( map_pairs(Vm, Pairs),
                by_id(Pairs, Named),
                E = right(T-Named-N) ),
              E = left("expected exactly one term")).

by_id(Pairs, Named) :-
    swap_pairs(Pairs, Swapped),
    keysort(Swapped, Sorted),
    named_vars(Sorted, Named).

swap_pairs([], []).
swap_pairs([K-I|Ps], [I-K|Qs]) :-
    swap_pairs(Ps, Qs).

named_vars([], []).
named_vars([I-K|Ps], [K-var(I, K)|Ns]) :-
    named_vars(Ps, Ns).

parse_query(Src, E) :-
    parse_term_string(Src, E0),
    query_either(E0, E).

query_either(left(M), left(M)).
query_either(right(T-Vs-N), right(T1-Vs-N)) :-
    body_vars_to_call(T, T1).
