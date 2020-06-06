:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
:- use_module(library(clpfd)).
:- use_module('../reif.pl').
:- set_prolog_flag(toplevel_print_anon, false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A simple explanation mechanism:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic debugging_info/4.

prolog_trace_interception(Port, Frame, _PC, continue) :-
    prolog_frame_attribute(Frame, level, Level),
    prolog_frame_attribute(Frame, goal, Goal),
    prolog_frame_attribute(Frame, has_alternatives, HasAlternatives),
    assertz(debugging_info(Level, Port, HasAlternatives, Goal)).

reifyTrace(G, TraceReification) :-
    debug, trace, \+ (call(G), false), notrace, nodebug,

    findall(N-P-A-C, debugging_info(N, P, A, C), TraceReification1),
    normalizeLevel(TraceReification1, TraceReification2),
    noSystemFalse(TraceReification2, TraceReification),

    retractall(debugging_info(_,_,_,_)).

tuple4(A, B, C, D, A-B-C-D).

% This puts the level of the goal at 0 and throws out the -1 instance.
normalizeLevel(Trace, NormalizedTrace) :-
    maplist(tuple4, Levels, Ports, Alternatives, Goals, Trace),
    min_list(Levels, MinLevel),
    maplist({MinLevel}/[X, Y]>>(Y #= X - MinLevel - 1), Levels, NormalizedLevels),
    maplist(tuple4, NormalizedLevels, Ports, Alternatives, Goals, Trace1),
    exclude([-1-_-_-_]>>true, Trace1, NormalizedTrace).

% This is supposed to be called on a trace with normalized level since we want
% to throw out only the top occurences of system-false.
noSystemFalse(Trace, CleanTrace) :-
    exclude([0-_-_-(system:false)]>>true, Trace, CleanTrace).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A simple explanation mechanism:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

isExitTrace(exit).
isExitTrace(fail).

trace_toplevel(Trace, TopLevelTrace) :-
    include([N-Port-_-_] >> (isExitTrace(Port), (N #= 0; N #= 1)),
            Trace,
            TopLevelTrace).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Experiment
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

printlist(List) :- maplist([X]>>(print(X),nl), List).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Chunking
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list([])     --> [].
list([L|Ls]) --> [L], list(Ls).

partial(Fold, Parsed) -->
    list(FirstPart),
    {foldl(Fold, FirstPart, [], Parsed)},
    list(_).

toplevelTrace_solutions(TopLevelTrace, Solutions) :-
  phrase(solutions(Solutions), TopLevelTrace).

toplevelGoal(Goal) --> [0-_-_-Goal].

solutions([]) --> [].
solutions([Goal :- Attempts|Rest]) -->
    list(Chunk),
    {maplist([N-_-_-_]>>dif(N,0), Chunk),
     chunk_attempts(Chunk, Attempts)},
    toplevelGoal(Goal),
    solutions(Rest).

chunk_attempts(Trace, Attempts) :-
    reverse(Trace, ReverseTrace),
    foldl(chunkStep, ReverseTrace, [], Attempts).

chunkStep(_-fail-false-G, Attempts, [[no-G] | Attempts]).
chunkStep(_-exit-true-G, [], [[G]]).
chunkStep(_-exit-true-G, [Attempt|Attempts], [[G|Attempt] | Attempts]).
chunkStep(_-exit-false-G, [], [[G]]).
chunkStep(_-exit-false-G, [Attempt|Attempts], Histories1) :-
    maplist({G}/[A, [G|A]]>>true, [Attempt|Attempts], Histories1).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Three example to guide us
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gestalt(G) :-
    reifyTrace(G, Trace),
    trace_toplevel(Trace, TopLevelTrace),
    toplevelTrace_solutions(TopLevelTrace, Solutions), !,
    printlist(Solutions).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Three example to guide us
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

a(a,b).
a(c,d).
b(c,d).

% c has multiple solutions
c(X,Y) :- a(X,Y).
c(X,Y) :- b(X,Y).

% d has no solution
d(X,Y) :-
    a(X,Y),
    c(Y,X).

e1(a).
e2(a).
e2(b).
e2(_) :- fail.
e3(X) :- d(X, a).
e4(X) :-
    e1(X),
    e2(Y),
    e3(Y).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Tests
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%?- gestalt(c(X,Y)).
%@ c(a,b):-[[a(a,b)]]
%@ c(c,d):-[[a(c,d)]]
%@ c(c,d):-[[b(c,d)]]
%@ true.

%?- gestalt(d(X,Y)).
%@ d(_16080,_16082):-[[a(a,b),no-c(b,a)],[a(c,d),no-c(d,c)]]
%@ true.

%?- gestalt(e4(X)).
%@ e4(_16582):-[[e1(a),e2(a),no-e3(a)],[e1(a),e2(b),no-e3(b)],[e1(a),no-e2(_16610)]]
%@ true.
