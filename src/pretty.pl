/*  pretty.pl - printing terms and clauses as re-readable Prolog text.

    Text is built as code lists with difference lists and returned as
    strings.  A namer is a closure called as call(Namer, Id, Name, Text).
*/

default_namer(I, _, S) :-
    format(string(S), "_G~d", [I]).

%  show_term_q(+Term, -String): with quoting (writeq style).
show_term_q(T, S) :-
    show_term_with(true, default_namer, T, S).

%  show_term(+Term, -String): without quoting (write style).
show_term(T, S) :-
    show_term_with(false, default_namer, T, S).

show_term_with(Q, Nm, T, S) :-
    pr(1200, T, Q, Nm, Cs, []),
    string_codes(S, Cs).

% text pieces
txt(S, Cs0, Cs) :-
    string_codes(S, Codes),
    conc(Codes, Cs, Cs0).

pr(_, var(I, N), _, Nm, Cs0, Cs) :-
    call(Nm, I, N, S),
    txt(S, Cs0, Cs).
pr(_, int(I), _, _, Cs0, Cs) :-
    number_string(I, S),
    txt(S, Cs0, Cs).
pr(_, flt(D), _, _, Cs0, Cs) :-
    show_float(D, S),
    txt(S, Cs0, Cs).
pr(P, atom(A), Q, _, Cs0, Cs) :-
    is_infix(A, I),
    is_prefix(A, Pr),
    bool_or(I, Pr, IsOp),
    pr_atom(IsOp, P, A, Q, Cs0, Cs).
pr(P, comp(F, As), Q, Nm, Cs0, Cs) :-
    comp_shape(F, As, Shape),
    pr_comp(Shape, P, F, As, Q, Nm, Cs0, Cs).

pr_atom(true, P, A, Q, Cs0, Cs) :-
    if_commit(( P < 1200, Q == true ),
              ( txt("(", Cs0, Cs1), atom_s(A, Q, Cs1, Cs2), txt(")", Cs2, Cs) ),
              atom_s(A, Q, Cs0, Cs)).
pr_atom(false, _, A, Q, Cs0, Cs) :-
    atom_s(A, Q, Cs0, Cs).

atom_s(A, Q, Cs0, Cs) :-
    atom_q(A, Q, S),
    txt(S, Cs0, Cs).

atom_q(A, true, S) :-
    quote_atom(A, S).
atom_q(A, false, S) :-
    atom_string(A, S).

comp_shape(F, As, Shape) :-
    length(As, N),
    if_commit(( F == '.', N =:= 2 ), Shape = list,
    if_commit(( F == '{}', N =:= 1 ), Shape = curly,
    if_commit(( N =:= 2, infix_op(F, _, _) ), Shape = infix,
    if_commit(( F == '\\+', N =:= 1 ), Shape = neg,
              Shape = plain)))).

pr_comp(list, _, F, As, Q, Nm, Cs0, Cs) :-
    show_list(comp(F, As), Q, Nm, Cs0, Cs).
pr_comp(curly, _, _, [X], Q, Nm, Cs0, Cs) :-
    txt("{", Cs0, Cs1),
    pr(1200, X, Q, Nm, Cs1, Cs2),
    txt("}", Cs2, Cs).
pr_comp(infix, P, F, [L, R], Q, Nm, Cs0, Cs) :-
    infix_op(F, Op, A),
    arg_priorities(A, Op, LA, RA),
    infix_sep(F, Q, Sep),
    if_commit(Op > P,
              ( txt("(", Cs0, Cs1),
                pr_arg(LA, L, Q, Nm, Cs1, Cs2), txt(Sep, Cs2, Cs3), pr_arg(RA, R, Q, Nm, Cs3, Cs4),
                txt(")", Cs4, Cs) ),
              ( pr_arg(LA, L, Q, Nm, Cs0, Cs1), txt(Sep, Cs1, Cs2), pr_arg(RA, R, Q, Nm, Cs2, Cs) )).
pr_comp(neg, P, _, [X], Q, Nm, Cs0, Cs) :-
    if_commit(900 > P,
              ( txt("(", Cs0, Cs1), txt("\\+ ", Cs1, Cs2), pr_arg(900, X, Q, Nm, Cs2, Cs3),
                txt(")", Cs3, Cs) ),
              ( txt("\\+ ", Cs0, Cs1), pr_arg(900, X, Q, Nm, Cs1, Cs) )).
pr_comp(plain, _, F, As, Q, Nm, Cs0, Cs) :-
    atom_s(F, Q, Cs0, Cs1),
    txt("(", Cs1, Cs2),
    comma_sep(As, Q, Nm, Cs2, Cs3),
    txt(")", Cs3, Cs).

infix_sep(F, Q, Sep) :-
    if_commit(F == ',',
              Sep = ", ",
              ( atom_codes(F, FC),
                if_commit(all_alpha(FC),
                          format(string(Sep), " ~w ", [F]),
                          ( atom_q(F, Q, FQ), format(string(Sep), " ~w ", [FQ]) )) )).

all_alpha([]).
all_alpha([C|Cs]) :-
    code_type(C, alpha),
    C =\= 0'_,
    all_alpha(Cs).

%  Arguments that are negative numbers need care after operators.
pr_arg(P, X, Q, Nm, Cs0, Cs) :-
    if_commit(( P < 999, negative_number(X) ),
              ( txt("(", Cs0, Cs1), pr(P, X, Q, Nm, Cs1, Cs2), txt(")", Cs2, Cs) ),
              pr(P, X, Q, Nm, Cs0, Cs)).

negative_number(X) :-
    if_commit(X = int(I), I < 0, ( X = flt(D), D < 0 )).

comma_sep([], _, _, Cs, Cs).
comma_sep([X|Xs], Q, Nm, Cs0, Cs) :-
    pr_arg(999, X, Q, Nm, Cs0, Cs1),
    comma_rest(Xs, Q, Nm, Cs1, Cs).

comma_rest([], _, _, Cs, Cs).
comma_rest([X|Xs], Q, Nm, Cs0, Cs) :-
    txt(", ", Cs0, Cs1),
    pr_arg(999, X, Q, Nm, Cs1, Cs2),
    comma_rest(Xs, Q, Nm, Cs2, Cs).

show_list(L, Q, Nm, Cs0, Cs) :-
    collect_items(L, Items, Tl),
    txt("[", Cs0, Cs1),
    comma_sep(Items, Q, Nm, Cs1, Cs2),
    if_commit(Tl == atom('[]'),
              Cs3 = Cs2,
              ( txt("|", Cs2, Cs2a), pr_arg(999, Tl, Q, Nm, Cs2a, Cs3) )),
    txt("]", Cs3, Cs).

collect_items(T, Items, Tl) :-
    if_commit(T = comp('.', [H, R]),
              ( collect_items(R, Is, Tl), Items = [H|Is] ),
              ( Items = [], Tl = T )).

% ---------------------------------------------------------------------------
% Floats, printed as Haskell's show for Double

show_float(D, S) :-
    if_commit(D < 0,
              ( A is -D, show_float_pos(A, S0), string_concat("-", S0, S) ),
              show_float_pos(D, S)).

show_float_pos(D, S) :-
    format(string(W), "~w", [D]),
    if_commit(sub_string(W, _, _, _, "Inf"),
              S = "Infinity",
              if_commit(sub_string(W, _, _, _, "NaN"),
                        S = "NaN",
                        ( float_digits(W, Ds, E), format_digits(Ds, E, S) ))).

%  float_digits(+Text, -Digits, -Exp): Text's value is 0.Digits * 10^Exp,
%  with no leading or trailing zero digit (Digits = [0'0] for zero).
float_digits(W, Ds, E) :-
    string_codes(W, Cs),
    split_exp(Cs, Mant, Exp),
    split_point(Mant, IntP, FracP),
    length(IntP, LI),
    conc(IntP, FracP, All),
    strip_leading_zeros(All, LI, Ds0, P),
    strip_trailing_zeros(Ds0, Ds1),
    if_commit(Ds1 == [],
              ( Ds = [0'0], E = 0 ),
              ( Ds = Ds1, E is P + Exp )).

split_exp(Cs, Mant, Exp) :-
    if_commit(append(Mant0, [0'e|ExpCs], Cs),
              ( Mant = Mant0, number_codes(Exp, ExpCs) ),
              ( Mant = Cs, Exp = 0 )).

split_point(Cs, I, F) :-
    if_commit(append(I0, [0'.|F0], Cs), ( I = I0, F = F0 ), ( I = Cs, F = [] )).

strip_leading_zeros([], P, [], P).
strip_leading_zeros([C|Cs], P, Ds, Q) :-
    if_commit(C =:= 0'0,
              ( P1 is P - 1, strip_leading_zeros(Cs, P1, Ds, Q) ),
              ( Ds = [C|Cs], Q = P )).

strip_trailing_zeros(Cs, Ds) :-
    rev(Cs, R),
    strip_zeros_front(R, R1),
    rev(R1, Ds).

strip_zeros_front([], []).
strip_zeros_front([C|Cs], Out) :-
    if_commit(C =:= 0'0, strip_zeros_front(Cs, Out), Out = [C|Cs]).

format_digits(Ds, E, S) :-
    if_commit(E < 0,
              exponent_form(Ds, E, S),
              if_commit(E > 7, exponent_form(Ds, E, S), fixed_form(Ds, E, S))).

exponent_form([D|Ds], E, S) :-
    E1 is E - 1,
    if_commit(Ds == [],
              format(string(S), "~c.0e~d", [D, E1]),
              format(string(S), "~c.~se~d", [D, Ds, E1])).

fixed_form(Ds, E, S) :-
    if_commit(E =< 0,
              ( Z is -E, length(Zs, Z), maplist(=(0'0), Zs),
                conc(`0.`, Zs, P1), conc(P1, Ds, All), string_codes(S, All) ),
              ( fixed_split(E, Ds, Int, Frac),
                mk0(Int, I1), mk0(Frac, F1),
                concat_lists([I1, `.`, F1], All), string_codes(S, All) )).

fixed_split(N, Rs, Int, Frac) :-
    compare(O, N, 0),
    fixed_split_(O, N, Rs, Int, Frac).

fixed_split_(=, _, Rs, [], Rs).
fixed_split_(<, _, Rs, [], Rs).
fixed_split_(>, N, Rs, [R|Int], Frac) :-
    N1 is N - 1,
    first_or_zero(Rs, R, Rest),
    fixed_split(N1, Rest, Int, Frac).

first_or_zero([], 0'0, []).
first_or_zero([R|Rs], R, Rs).

mk0([], `0`).
mk0([C|Cs], [C|Cs]).

% ---------------------------------------------------------------------------
% Atoms

%  quote_atom(+Atom, -String): quoted when needed so it reads back.
quote_atom(A, S) :-
    if_commit(memberchk(A, ['[]', '{}', '!', ';']),
              atom_string(A, S),
    if_commit(A == ',',
              S = "','",
              ( atom_codes(A, Cs),
                if_commit(plain_atom(Cs),
                          atom_string(A, S),
                          if_commit(symbol_atom(Cs),
                                    atom_string(A, S),
                                    ( escape_codes(Cs, Es),
                                      conc(Es, `'`, E1),
                                      string_codes(S, [0'\'|E1]) ))) ))).

plain_atom([C|Cs]) :-
    code_type(C, lower(_)),
    all_csym(Cs).

all_csym([]).
all_csym([C|Cs]) :-
    code_type(C, csym),
    all_csym(Cs).

symbol_atom([C|Cs]) :-
    is_sym_c(C),
    all_sym(Cs).

all_sym([]).
all_sym([C|Cs]) :-
    is_sym_c(C),
    all_sym(Cs).

escape_codes([], []).
escape_codes([C|Cs], Out) :-
    escape_one(C, E),
    escape_codes(Cs, Rest),
    conc(E, Rest, Out).

escape_one(C, E) :-
    if_commit(C =:= 0'\', E = `\\'`,
    if_commit(C =:= 0'\\, E = `\\\\`,
    if_commit(C =:= 0'\n, E = `\\n`,
    if_commit(C =:= 0'\t, E = `\\t`,
              E = [C])))).

% ---------------------------------------------------------------------------
% Answers and clauses

%  show_answer_term(+Term, -String): variables shown as _A, _B, ... in order
%  of first occurrence, so that answers compare up to renaming.
show_answer_term(T, S) :-
    term_vars_ordered(T, Vs),
    var_ids(Vs, Ids),
    numbered(Ids, 0, Pairs),
    map_from_pairs(Pairs, Table),
    show_term_with(true, answer_namer(Table), T, S).

var_ids([], []).
var_ids([var(I, _)|Vs], [I|Is]) :-
    var_ids(Vs, Is).

answer_namer(Table, I, _, S) :-
    map_find(Table, I, 0, K),
    letter_name(K, L),
    string_concat("_", L, S).

letter_name(K, S) :-
    C is 0'A + K mod 26,
    if_commit(K < 26,
              string_codes(S, [C]),
              ( D is K // 26, format(string(S), "~c~d", [C, D]) )).

%  clause_namer(+ClauseTerm, -Namer): source names when unique, singletons
%  as _, other variables V1, V2, ...
clause_namer(T, clause_names(Names)) :-
    map_empty(E),
    count_vars(T, E, Occs),
    term_vars_ordered(T, Ordered),
    foldl(assign_name(Occs), Ordered, []-E, _-Names).

clause_names(Names, I, _, S) :-
    format(string(Def), "_G~d", [I]),
    map_find(Names, I, Def, S).

count_vars(var(I, _), M0, M) :-
    map_find(M0, I, 0, C),
    C1 is C + 1,
    map_put(I, C1, M0, M).
count_vars(atom(_), M, M).
count_vars(int(_), M, M).
count_vars(flt(_), M, M).
count_vars(comp(_, As), M0, M) :-
    foldl(count_vars, As, M0, M).

assign_name(Occs, var(I, N), Used-M0, Used1-M) :-
    map_find(Occs, I, 0, C),
    if_commit(C =:= 1,
              ( Used1 = Used, map_put(I, "_", M0, M) ),
              ( atom_string(N, NS),
                if_commit(( valid_name(N), not_member(NS, Used) ),
                          ( Used1 = [NS|Used], map_put(I, NS, M0, M) ),
                          ( if_commit(valid_name(N), Base = NS, Base = "V"),
                            fresh_name(Base, 1, Used, Cand),
                            Used1 = [Cand|Used],
                            map_put(I, Cand, M0, M) )) )).

not_member(X, L) :-
    if_commit(memberchk(X, L), fail, true).

valid_name(N) :-
    atom_codes(N, [C|Cs]),
    code_type(C, upper(_)),
    all_csym(Cs).

fresh_name(Base, K, Used, Cand) :-
    format(string(C0), "~w~d", [Base, K]),
    if_commit(memberchk(C0, Used),
              ( K1 is K + 1, fresh_name(Base, K1, Used, Cand) ),
              Cand = C0).

clause_term(clause(H, B, _), T) :-
    if_commit(B == atom(true), T = H, T = comp(':-', [H, B])).

%  show_clause(+Clause, -String): one clause with an indented body.
show_clause(C, S) :-
    clause_term(C, T),
    clause_namer(T, Nm),
    C = clause(H, B, _),
    show_term_with(true, Nm, H, HS),
    if_commit(B == atom(true),
              string_concat(HS, ".", S),
              ( body_text(Nm, 1, B, BS),
                format(string(S), "~s :-~n~s.", [HS, BS]) )).

body_text(Nm, Ind, G, S) :-
    conj_flat(G, Gs),
    maplist(goal_text(Nm, Ind), Gs, Ts),
    atomic_list_concat(Ts, ',\n', A),
    atom_string(A, S).

conj_flat(G, Gs) :-
    if_commit(G = comp(',', [A, B]),
              ( conj_flat(A, GA), conj_flat(B, GB), conc(GA, GB, Gs) ),
              Gs = [G]).

goal_text(Nm, Ind, G, S) :-
    goal_shape(G, Shape),
    goal_text_(Shape, Nm, Ind, G, S).

goal_shape(G, Shape) :-
    if_commit(G = comp(';', [comp('->', [_, _]), _]), Shape = ite,
    if_commit(G = comp(';', [_, _]), Shape = disj,
    if_commit(G = comp(if_commit, [_, _, _]), Shape = if_commit,
              Shape = plain))).

goal_text_(ite, Nm, Ind, comp(';', [comp('->', [C, T]), E]), S) :-
    pad(Ind, P),
    inner(Nm, Ind, C, CS),
    inner(Nm, Ind, T, TS),
    else_chain(Nm, Ind, E, ES),
    format(string(S), "~s(   ~s~n~s->  ~s~s~n~s)", [P, CS, P, TS, ES, P]).
goal_text_(disj, Nm, Ind, comp(';', [A, B]), S) :-
    pad(Ind, P),
    inner(Nm, Ind, A, AS),
    inner(Nm, Ind, B, BS),
    format(string(S), "~s(   ~s~n~s;   ~s~n~s)", [P, AS, P, BS, P]).
goal_text_(if_commit, Nm, Ind, comp(if_commit, [C, T, E]), S) :-
    pad(Ind, P),
    block(Nm, Ind, C, CS),
    block(Nm, Ind, T, TS),
    block(Nm, Ind, E, ES),
    format(string(S), "~sif_commit(~n~s,~n~s,~n~s~n~s)", [P, CS, TS, ES, P]).
goal_text_(plain, Nm, Ind, G, S) :-
    pad(Ind, P),
    show_term_with(true, Nm, G, GS),
    string_concat(P, GS, S).

pad(K, P) :-
    N is 4 * K,
    length(Cs, N),
    maplist(=(0' ), Cs),
    string_codes(P, Cs).

%  A conjunction argument must stay one argument when read back.
block(Nm, Ind, X, S) :-
    Ind1 is Ind + 1,
    if_commit(X = comp(',', _),
              ( pad(Ind1, P),
                Ind2 is Ind + 2,
                body_text(Nm, Ind2, X, B),
                drop_spaces(B, B1),
                format(string(S), "~s(   ~s~n~s)", [P, B1, P]) ),
              body_text(Nm, Ind1, X, S)).

inner(Nm, Ind, X, S) :-
    Ind1 is Ind + 1,
    body_text(Nm, Ind1, X, B),
    drop_spaces(B, S).

drop_spaces(S, T) :-
    string_codes(S, Cs),
    span_codes(is_blank_space, Cs, _, Rest),
    string_codes(T, Rest).

is_blank_space(0' ).

else_chain(Nm, Ind, E, S) :-
    pad(Ind, P),
    if_commit(E = comp(';', [comp('->', [C2, T2]), E2]),
              ( inner(Nm, Ind, C2, CS),
                inner(Nm, Ind, T2, TS),
                else_chain(Nm, Ind, E2, ES),
                format(string(S), "~n~s;   ~s~n~s->  ~s~s", [P, CS, P, TS, ES]) ),
              ( inner(Nm, Ind, E, ES),
                format(string(S), "~n~s;   ~s", [P, ES]) )).

show_clauses(Cs, S) :-
    maplist(show_clause_nl, Cs, Ss),
    atomic_list_concat(Ss, A),
    atom_string(A, S).

show_clause_nl(C, S) :-
    show_clause(C, S0),
    string_concat(S0, "\n", S).

show_program(P, S) :-
    program_clauses(P, KCs),
    maplist(kc_text, KCs, Ts),
    atomic_list_concat(Ts, '\n', A),
    atom_string(A, S).

kc_text(_-Cs, T) :-
    show_clauses(Cs, T).

%  show_source_term(+Term, -String): with the variables' source names.
show_source_term(T, S) :-
    show_term_with(true, source_namer, T, S).

source_namer(I, N, S) :-
    if_commit(( N \== '', N \== '_' ),
              atom_string(N, S),
              format(string(S), "_G~d", [I])).
