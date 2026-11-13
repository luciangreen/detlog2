/*  stream.pl - answer streams.

    An answer stream (a packet) is a lazy list of events:

      []            the end
      [Ev|Stream]   an event, then the rest
      lz(Closure)   not computed yet: call(Closure, Stream) computes it

    Events are out(Text) (text written by output built-ins), ans(State)
    (an answer) and err(Message) (an error; the stream stops there).

    Streams are data, never choicepoints.  Because tails can be lz/1
    closures, only the answers that are needed are ever computed: a query
    can take the first answer of an infinite generator.
*/

%  force(+Stream, -Forced): the first constructor of a stream.
force([], []).
force([E|S], [E|S]).
force(lz(G), S) :-
    call(G, S1),
    force(S1, S).

%  append_s(+Xs, +Ys, -Zs): concatenate two streams; an error ends both.
append_s(Xs, Ys, lz(append_step(Xs, Ys))).

append_step(Xs, Ys, R) :-
    force(Xs, F),
    append_f(F, Ys, R).

append_f([], Ys, Ys).
append_f([E|T], Ys, R) :-
    append_ev(E, T, Ys, R).

append_ev(err(M), _, _, [err(M)]).
append_ev(out(O), T, Ys, [out(O)|lz(append_step(T, Ys))]).
append_ev(ans(S), T, Ys, [ans(S)|lz(append_step(T, Ys))]).

%  bind_s(+Stream, +K, -Out): splice call(K, State, Stream) into every
%  answer of Stream.
bind_s(S, K, lz(bind_step(S, K))).

bind_step(S, K, R) :-
    force(S, F),
    bind_f(F, K, R).

bind_f([], _, []).
bind_f([E|T], K, R) :-
    bind_ev(E, T, K, R).

bind_ev(out(O), T, K, [out(O)|lz(bind_step(T, K))]).
bind_ev(err(E), _, _, [err(E)]).
bind_ev(ans(St), T, K, R) :-
    call(K, St, S1),
    append_s(S1, lz(bind_step(T, K)), R).

%  stream_list(+Stream, -List): force a whole (finite) stream.
stream_list(S, L) :-
    force(S, F),
    stream_list_f(F, L).

stream_list_f([], []).
stream_list_f([E|T], [E|L]) :-
    stream_list(T, L).

%  stream_take_answers(+N, +Stream, -Events): events up to and including
%  the N-th answer (or the end, or an error).
stream_take_answers(N, S, Evs) :-
    compare(O, N, 0),
    take_answers_(O, N, S, Evs).

take_answers_(<, _, _, []).
take_answers_(=, _, _, []).
take_answers_(>, N, S, Evs) :-
    force(S, F),
    take_answers_f(F, N, Evs).

take_answers_f([], _, []).
take_answers_f([E|T], N, [E|Evs]) :-
    take_answers_ev(E, T, N, Evs).

take_answers_ev(out(_), T, N, Evs) :-
    stream_take_answers(N, T, Evs).
take_answers_ev(err(_), _, _, []).
take_answers_ev(ans(_), T, N, Evs) :-
    N1 is N - 1,
    stream_take_answers(N1, T, Evs).

%  head_answer(+Stream, -Before, -Result): the out/err events before the
%  first answer, and first(State), stop(Message) or none.  Only the head
%  of the stream is demanded.
head_answer(S, Before, R) :-
    force(S, F),
    head_answer_f(F, Before, R).

head_answer_f([], [], none).
head_answer_f([E|T], Before, R) :-
    head_answer_ev(E, T, Before, R).

head_answer_ev(out(O), T, [out(O)|B], R) :-
    head_answer(T, B, R).
head_answer_ev(err(M), _, [], stop(M)).
head_answer_ev(ans(St), _, [], first(St)).

%  maybe_stream(+MaybeState, -Stream)
maybe_stream(nothing, []).
maybe_stream(just(St), [ans(St)]).

ok_stream(St, [ans(St)]).

%  answers_of(+Events, -States)
answers_of([], []).
answers_of([E|Es], Sts) :-
    answers_of(Es, Rest),
    answer_ev(E, Rest, Sts).

answer_ev(ans(St), Rest, [St|Rest]).
answer_ev(out(_), Rest, Rest).
answer_ev(err(_), Rest, Rest).
