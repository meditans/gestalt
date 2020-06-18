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
%@ user:c(a, b) :-
%@     user:a(a, b).
%@ user:c(c, d) :-
%@     user:a(c, d).
%@ user:c(c, d) :-
%@     user:b(c, d).
%@ true.

%?- gestalt(d(X,Y)).
%@ user:d(_, _) :-
%@     user:a(a, b),
%@     no-(user:c(b, a)).
%@ user:d(_, _) :-
%@     user:a(c, d),
%@     no-(user:c(d, c)).
%@ true.

%?- gestalt(e4(X)).
%@ user:e4(_) :-
%@     user:e1(a),
%@     user:e2(a),
%@     no-(user:e3(a)).
%@ user:e4(_) :-
%@     user:e1(a),
%@     user:e2(b),
%@     no-(user:e3(b)).
%@ user:e4(_) :-
%@     user:e1(a),
%@     no-(user:e2(_)).
%@ true.
