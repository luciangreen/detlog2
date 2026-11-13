/*  detlog_runtime.pl - the Detlog runtime in plain Prolog.

    Converted (Detlog) programs call these predicates.  The library is
    itself written in the style it supports:

      * no cut, no (;)/2, no (->)/2, no (\+)/1, no once/1;
      * every predicate is deterministic: its clauses are told apart by
        their first argument (distinct principal functors or constants),
        so SWI-Prolog's first-argument indexing selects one clause and
        leaves no choicepoint;
      * alternatives are data (packets and rows), never choicepoints.

    Two library primitives look at more than one solution of a goal:
    findall/3, which collects a packet, and limit/2 inside findall/3,
    which takes the first answer of an if_commit/3 condition.  Both
    return deterministically.

    Packets
      cp(List)          a choice packet: the alternatives of one position.
                        A nested cp/1 offers its own alternatives inline.
      [Row, ...]        an answer packet: rows, and out(Text) items for the
                        output written between answers.

    Errors are thrown as detlog_error(Message).
*/

:- module(detlog_runtime,
          [ if_commit/3,
            once_det/1,
            member_cp/2,
            between_cp/3,
            cp_rows/2,
            cp_filter/3,
            splice/2,
            splice_first/2,
            splice_extend/4,
            rows_concat/2,
            splice_safe/1,
            length_det/2,
            builtin_rows/2,
            effect_text/2,
            packet_first/3,
            packet_split/3,
            memo_lookup/3,
            memo_miss/2,
            write_packet/2
          ]).

:- use_module(library(solution_sequences), [limit/2]).

:- meta_predicate
    if_commit(0, 0, 0),
    once_det(0),
    builtin_rows(0, -),
    effect_text(0, -).

% ---------------------------------------------------------------------------
% Commitment

%!  if_commit(:Cond, :Then, :Else)
%
%   Run Then with the bindings of the first answer of Cond, or Else when
%   Cond has no answer.  The rest of Cond's answers are never computed and
%   no choicepoint is left.  This replaces (Cond -> Then ; Else), cuts,
%   once/1 and \+/1.
if_commit(Cond, Then, Else) :-
    findall(Cond, limit(1, Cond), Firsts),
    commit_first(Firsts, Cond, Then, Else).

commit_first([], _, _, Else) :-
    call(Else).
commit_first([First|_], Cond, Then, _) :-
    Cond = First,
    call(Then).

%!  once_det(:Goal)
%
%   The first answer of Goal, or failure.
once_det(Goal) :-
    if_commit(Goal, true, fail).

% ---------------------------------------------------------------------------
% Choice packets

%!  member_cp(-Packet, +List)
%
%   Packet = cp(List): the choices of member(X, List), as data.
member_cp(P, L) :-
    if_commit(is_list(L),
              P = cp(L),
              rt_error("member_cp/2: not a proper list: ~q", [L])).

%!  between_cp(+Low, +High, -Packet)
%
%   Packet = cp([Low, ..., High]): the choices of between/3, as data.  An
%   infinite range has no packet.
between_cp(Lo, Hi, P) :-
    if_commit(( int_value(Lo, L), int_value(Hi, H) ),
              ( range(L, H, Xs), P = cp(Xs) ),
              rt_error("between_cp/3: needs integer bounds (an infinite packet cannot be spliced)", [])).

int_value(E, V) :-
    catch(V is E, _, fail),
    integer(V).

range(L, H, Xs) :-
    compare(O, L, H),
    range_(O, L, H, Xs).

range_(<, L, H, [L|Xs]) :-
    L1 is L + 1,
    range(L1, H, Xs).
range_(=, L, _, [L]).
range_(>, _, _, []).

%!  cp_rows(+Packet, -Rows)
%
%   cp([E1, E2, ...]) as one-column rows [[E1], [E2], ...].  Nested packets
%   are flattened.
cp_rows(P, Rows) :-
    if_commit(cp_list(P, L),
              ( flatten_cp(L, Es), one_column(Es, Rows) ),
              rt_error("cp_rows/2: expected a choice packet cp(List), got ~q", [P])).

%!  cp_filter(+Packet, ?Pattern, -Rows)
%
%   The rows of Packet that unify with Pattern.
cp_filter(P, Pat, Out) :-
    if_commit(( nonvar(P), P = cp(Rows) ),
              splice_extend(Rows, Pat, Pat, Out),
              rt_error("cp_filter/3: expected a choice packet cp(Rows), got ~q", [P])).

cp_list(P, L) :-
    nonvar(P),
    P = cp(L),
    is_list(L).

flatten_cp([], []).
flatten_cp([X|Xs], Out) :-
    if_commit(cp_list(X, L), flatten_cp(L, F), F = [X]),
    flatten_cp(Xs, Rest),
    conc(F, Rest, Out).

one_column([], []).
one_column([X|Xs], [[X]|Rs]) :-
    one_column(Xs, Rs).

choices([], []).
choices([T|Ts], [C|Cs]) :-
    if_commit(cp_list(T, L),
              flatten_cp(L, C),
              if_commit(( nonvar(T), T = cp(Bad) ),
                        rt_error("splice/2: packet is not a proper list: ~q", [Bad]),
                        C = [T])),
    choices(Ts, Cs).

% ---------------------------------------------------------------------------
% Splicing

%!  splice(+Positions, -Rows)
%
%   The Cartesian product of the positions, in left-to-right Prolog order.
%   A position is a choice packet cp(List) or a fixed value.
splice(Ts, Rows) :-
    if_commit(is_list(Ts),
              ( choices(Ts, Cs), product(Cs, Rows) ),
              rt_error("splice/2: first argument must be a proper list", [])).

%!  splice_first(+Positions, -Row)
%
%   The first row of splice/2; fails when there is none.
splice_first(Ts, Row) :-
    splice(Ts, Rows),
    first_row(Rows, Row).

first_row([Row|_], Row).

product([], [[]]).
product([C|Cs], Rows) :-
    product(Cs, Rest),
    prefix_each(C, Rest, Rows).

prefix_each([], _, []).
prefix_each([X|Xs], Rest, Rows) :-
    cons_each(Rest, X, Front),
    prefix_each(Xs, Rest, Back),
    conc(Front, Back, Rows).

cons_each([], _, []).
cons_each([R|Rs], X, [[X|R]|Ys]) :-
    cons_each(Rs, X, Ys).

%!  splice_extend(+Rows, +Env, +Pattern, -Out)
%
%   For every row, take a fresh copy of Env-Pattern, unify the Pattern copy
%   with the row, and keep the Env copy when that succeeds.  out(Text) items
%   are kept in place.  This is how an answer packet is spliced into the
%   environment of the goal that asked for it.
splice_extend(Rows, Env, Pat, Out) :-
    if_commit(is_list(Rows),
              extend_rows(Rows, Env, Pat, Out),
              rt_error("splice_extend/4: rows are not a proper list: ~q", [Rows])).

extend_rows([], _, _, []).
extend_rows([R|Rs], Env, Pat, Out) :-
    if_commit(out_item(R),
              Out = [R|Out1],
              ( copy_term(Env-Pat, E1-P1),
                if_commit(P1 = R, Out = [E1|Out1], Out = Out1) )),
    extend_rows(Rs, Env, Pat, Out1).

out_item(R) :-
    nonvar(R),
    R = out(_).

%!  rows_concat(+ListOfRows, -Rows)
%
%   Concatenate packets: the rows of a disjunction, in order.
rows_concat(Ls, Out) :-
    if_commit(proper_lists(Ls),
              concat_all(Ls, Out),
              rt_error("rows_concat/2: expected a list of proper lists: ~q", [Ls])).

proper_lists(Ls) :-
    is_list(Ls),
    all_lists(Ls, true).

all_lists([], true).
all_lists([L|Ls], B) :-
    if_commit(is_list(L), all_lists(Ls, B), B = false).

concat_all([], []).
concat_all([L|Ls], Out) :-
    concat_all(Ls, Rest),
    conc(L, Rest, Out).

%!  splice_safe(+Groups)
%
%   True when the groups share no unbound variable, so their packets can be
%   computed independently and spliced.
splice_safe(Gs) :-
    if_commit(is_list(Gs),
              ( var_sets(Gs, Ss), disjoint_sets(Ss, B) ),
              B = false),
    B == true.

var_sets([], []).
var_sets([G|Gs], [S|Ss]) :-
    term_variables(G, S),
    var_sets(Gs, Ss).

disjoint_sets([], true).
disjoint_sets([S|Ss], B) :-
    none_shared(Ss, S, B1),
    disjoint_sets(Ss, B2),
    and(B1, B2, B).

none_shared([], _, true).
none_shared([T|Ts], S, B) :-
    no_common(S, T, B1),
    none_shared(Ts, S, B2),
    and(B1, B2, B).

no_common([], _, true).
no_common([V|Vs], T, B) :-
    var_in(T, V, In),
    not_(In, B1),
    no_common(Vs, T, B2),
    and(B1, B2, B).

var_in([], _, false).
var_in([W|Ws], V, B) :-
    if_commit(V == W, B = true, var_in(Ws, V, B)).

and(true, B, B).
and(false, _, false).

not_(true, false).
not_(false, true).

% ---------------------------------------------------------------------------
% Deterministic built-in modes, effects and packets

%!  length_det(?List, ?Length)
%
%   length/2 in its deterministic modes only.
length_det(L, N) :-
    '$skip_list'(_, L, End),
    if_commit(( var(End), var(N) ),
              rt_error("length_det/2: list and length both unbound (that mode needs a choicepoint)", []),
              length(L, N)).

%!  builtin_rows(:Goal, -Rows)
%
%   All answers of a built-in goal as one packet [[Goal1], [Goal2], ...].
builtin_rows(MG, Rows) :-
    strip_module(MG, M, G),
    findall([G], M:G, Rows).

%!  effect_text(:Goal, -Text)
%
%   The text an output built-in would write, as an atom.  In converted
%   code output is data: an out(Text) item of the answer packet.
effect_text(MG, Text) :-
    with_output_to(atom(Text), MG).

%!  packet_first(+Packet, -OutsBefore, -Result)
%
%   The out/1 items before the first row, and first(Row), or none.
packet_first(P, Pre, Res) :-
    if_commit(is_list(P),
              ( outs_prefix(P, Pre, Rest), first_or_none(Rest, Res) ),
              rt_error("packet_first/3: not a packet: ~q", [P])).

outs_prefix([], [], []).
outs_prefix([X|Xs], Pre, Rest) :-
    if_commit(out_item(X),
              ( Pre = [X|Pre1], outs_prefix(Xs, Pre1, Rest) ),
              ( Pre = [], Rest = [X|Xs] )).

first_or_none([], none).
first_or_none([R|_], first(R)).

%!  packet_split(+Packet, -Outs, -Rows)
%
%   The out/1 items and the answer rows of a packet.
packet_split(P, Outs, Rows) :-
    if_commit(is_list(P),
              split_items(P, Outs, Rows),
              rt_error("packet_split/3: not a packet: ~q", [P])).

split_items([], [], []).
split_items([X|Xs], Outs, Rows) :-
    if_commit(out_item(X),
              ( Outs = [X|Os], Rows = Rs ),
              ( Outs = Os, Rows = [X|Rs] )),
    split_items(Xs, Os, Rs).

%!  write_packet(+Packet, -Rows)
%
%   Write the out/1 items of a packet in order and return its rows: the
%   top level of a converted program.
write_packet(P, Rows) :-
    if_commit(is_list(P),
              write_items(P, Rows),
              rt_error("write_packet/2: not a packet: ~q", [P])).

write_items([], []).
write_items([X|Xs], Rows) :-
    if_commit(out_item(X),
              ( X = out(T), write(T), Rows = Rs ),
              Rows = [X|Rs]),
    write_items(Xs, Rs).

% ---------------------------------------------------------------------------
% Memo tables

%!  memo_lookup(+Args, +Table, -Rows)
%
%   Table is [[Pattern, Rows], ...]; the first entry whose pattern is a
%   variant of Args gives a copy of its rows.  Fails when there is none.
memo_lookup(Args, Table, Rows) :-
    if_commit(is_list(Table),
              memo_find(Table, Args, Rows),
              rt_error("memo_lookup/3: not a memo table: ~q", [Table])).

memo_find([E|Es], Args, Rows) :-
    if_commit(( E = [Pat, Rs], Pat =@= Args ),
              copy_term(Rs, Rows),
              memo_find(Es, Args, Rows)).

%!  memo_miss(+Key, +Args)
%
%   A complete memo table has no entry for Args: an error.
memo_miss(K, A) :-
    rt_error("memo_miss: ~q was memoised as complete, but has no entry for ~q", [K, A]).

% ---------------------------------------------------------------------------
% Helpers

conc([], L, L).
conc([X|Xs], L, [X|Ys]) :-
    conc(Xs, L, Ys).

rt_error(Format, Args) :-
    format(string(Msg), Format, Args),
    throw(detlog_error(Msg)).
