:- use_module(library(clpfd)).
:- use_module(library(dcg/basics)).
:- use_module(library(clpfd)).
:- use_module('reif.pl').
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

%reifyTrace
study(G, TraceReification) :-
    debug, trace,
    \+ (call(G), false),
    notrace, nodebug,
    findall(N-P-A-C, debugging_info(N, P, A, C), TraceReification),
    retractall(debugging_info(_,_,_,_)).

cleanstudy(G, TraceReification) :-
    study(G, TraceReification1),
    normalizeLevel(TraceReification1, TraceReification2),
    noSystemFalse(TraceReification2, TraceReification).

% end of reifyTrace

tuple4(A, B, C, D, A-B-C-D).


cleantoplevel(G, TraceTopLevel) :-
    cleanstudy(G, Trace),
    onlyTopLevel(Trace, TraceTopLevel).

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

onlyTopLevel(Trace, TopLevelTrace) :-
    exclude([N-_-_-_] >> (N #>= 2), Trace, TopLevelTrace).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Two example to guide us
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

%?- e4(X).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Experiment
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

printlist(List) :- maplist([X]>>(print(X),nl), List).

%?-write_canonical(system:false).

%?- cleanstudy(c(X,Y), _Trace), printlist(_Trace).

%?- cleantoplevel(d(X,Y), _Trace), printlist(_Trace).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Chunking
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

list([])     --> [].
list([L|Ls]) --> [L], list(Ls).

partial(Fold, Parsed) -->
    list(FirstPart),
    {foldl(Fold, FirstPart, [], Parsed)},
    list(_).

toplevelTraceStatement(Goal) --> [0-_-_-Goal].

chunkedTrace(Chunks) --> toplevelTraceStatement(_), chunk(Chunks).

isExitTrace(exit).
isExitTrace(fail).

trace_traceExitOnly(Trace, TraceExitOnly) :-
    include([_-Port-_-_]>>isExitTrace(Port), Trace, TraceExitOnly).

chunk([]) --> [].
chunk([Goal :- Histories|Rest]) -->
    list(In),
    {maplist([N-_-_-_]>>dif(N,0), In),
     createHistories(In, Histories)
    },
    toplevelTraceStatement(Goal),
    chunk(Rest).


%?- cleantoplevel(c(X,Y), _ReifiedTrace), trace_traceExitOnly(_ReifiedTrace, _RTExits), printlist(_RTExits), nl, phrase(chunk(_Chunks), _RTExits), printlist(_Chunks).
%@ 1-exit-true-a(a,b)
%@ 0-exit-true-c(a,b)
%@ 1-exit-false-a(c,d)
%@ 0-exit-true-c(c,d)
%@ 1-exit-false-b(c,d)
%@ 0-exit-false-c(c,d)
%@
%@ c(a,b):-[[a(a,b)]]
%@ c(c,d):-[[a(c,d)]]
%@ c(c,d):-[[b(c,d)]]
%@ true ;

%?- cleantoplevel(d(X,Y), _ReifiedTrace), printlist(_ReifiedTrace), nl, phrase(chunk(_Chunks), _ReifiedTrace), printlist(_Chunks).

%?- cleantoplevel(e4(X), _ReifiedTrace), trace_traceExitOnly(_ReifiedTrace, _RTExits), printlist(_RTExits), nl, phrase(chunk(_Chunks), _RTExits), printlist(_Chunks).
%@ 1-exit-false-e1(a)
%@ 1-exit-true-e2(a)
%@ 1-fail-false-e3(a)
%@ 1-exit-true-e2(b)
%@ 1-fail-false-e3(b)
%@ 1-fail-false-e2(_1608)
%@ 0-fail-false-e4(_1580)
%@
%@ e4(_1580):-[[e1(a),e2(a),no-e3(a)],[e1(a),e2(b),no-e3(b)],[e1(a),no-e2(_1608)]]
%@ true ;
%@ false.

contrafoo(_-fail-false-G, Histories, [[no-G] | Histories]).
contrafoo(_-exit-true-G, [], [[G]]).
contrafoo(_-exit-true-G, [H|Histories], [[G|H] | Histories]).
contrafoo(_-exit-false-G, [], [[G]]).
contrafoo(_-exit-false-G, [Hist|Histories], Histories1) :-
    maplist({G}/[H, [G|H]]>>true, [Hist|Histories], Histories1).

createHistories(Trace, Histories) :-
    reverse(Trace, ReverseTrace),
    foldl(contrafoo, ReverseTrace, [], Histories).
