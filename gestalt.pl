:- module(gestalt, [gestalt/1]).

:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
:- use_module(library(clpfd)).
:- use_module('../reif.pl').
:- set_prolog_flag(toplevel_print_anon, false).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% A simple explanation mechanism:
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- dynamic debugging_info/4.

user:prolog_trace_interception(Port, Frame, _PC, continue) :-
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

toplevelGoal(Port-Goal) --> [0-Port-_-Goal].

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
%% Gestalt
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

gestalt(G) :-
    reifyTrace(G, Trace),
    trace_toplevel(Trace, TopLevelTrace),
    toplevelTrace_solutions(TopLevelTrace, Solutions),
    asClauses(Solutions, Clauses),
    maplist(portray_clause, Clauses), !.

simplifyTrue((A, true), A).
simplifyTrue((A, B), (A, B)) :- dif(B, true).

list_conjunction([], true).
list_conjunction([A|As], Result) :-
    list_conjunction(As, Cs),
    simplifyTrue((A,Cs), Result).

asClauses([fail-G:-Failures], Clauses) :-
    distributeFailures(G :- Failures, Clauses).
asClauses([(exit-G:-Success)|Succs], Clauses) :-
    unwrapSuccesses([(exit-G:-Success)|Succs], Clauses).

distributeFailures(G :- Solutions, DistributedSolutions) :-
    maplist({G}/[Sol, G:-Sol_]>>list_conjunction(Sol, Sol_), Solutions, DistributedSolutions).

unwrapSuccesses(Successes, UnwrappedSuccesses) :-
    maplist([exit-G:-[Succs], G:-Succs_]>>list_conjunction(Succs, Succs_), Successes, UnwrappedSuccesses).

