:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).
:- use_module(library(lists)).

lit(true) :-
    true.
lit(false) :-
    false.

not(lit(true)) :-
    lit(false).
not(lit(false)) :-
    lit(true).

and(lit(true), lit(true)) :-
    lit(true).
and(lit(true), lit(false)) :-
    lit(false).
and(lit(false), lit(true)) :-
    lit(false).
and(lit(false), lit(false)) :-
    lit(false).

or(lit(true), lit(true)) :-
    lit(true).
or(lit(true), lit(false)) :-
    lit(true).
or(lit(false), lit(true)) :-
    lit(true).
or(lit(false), lit(false)) :-
    lit(false).

equivalence(lit(true), lit(true)) :-
    lit(true).
equivalence(lit(true), lit(false)) :-
    lit(false).
equivalence(lit(false), lit(true)) :-
    lit(false).
equivalence(lit(false), lit(false)) :-
    lit(true).

implies(lit(true), lit(true)) :-
    lit(true).
implies(lit(true), lit(false)) :-
    lit(false).
implies(lit(false), lit(true)) :-
    lit(true).
implies(lit(false), lit(false)) :-
    lit(true).


exactly_one_pos(ListOfVars) :-
    count(lit(true), ListOfVars, 1).

count(_, [], 0).
count(X, [X|T], N) :- 
    count(X, T, M), 
    N is M+1.
count(X, [_|T], N) :- 
    count(X, T, N).

min_one_pos(ListOfVars) :-
    member(lit(true), ListOfVars).
    

%% normalise(+Formula, -NFormula).
normalise(_Formula, _NFormula) :-
    true.

%% to_cnf(+Formula, -CNF).
to_cnf(_Formula, _CNF) :-
    true.

%% solve(+CNF).
solve(_CNF) :-
    true.
