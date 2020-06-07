:- use_module('gestalt.pl').

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

%?- gestalt(d(X,Y)).

%?- gestalt(e4(X)).

:- dynamic debugging_info/4.

prolog_trace_interception(Port, Frame, _PC, continue) :-
    prolog_frame_attribute(Frame, level, Level),
    prolog_frame_attribute(Frame, goal, Goal),
    prolog_frame_attribute(Frame, has_alternatives, HasAlternatives),
    print(debugging_info(Level, Port, HasAlternatives, Goal)),
    assertz(debugging_info(Level, Port, HasAlternatives, Goal)).
