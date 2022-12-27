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


exactly_one_pos(ListOfVars).

min_one_pos(ListOfVars).

    
normalise(lit(X), lit(X)).
normalise(equivalence(A, B), Res) :-
    normalise(A, NA),
    normalise(B, NB),
    Res = and(or(not(NA), NB), or(NA, not(NB))).
normalise(implies(A, B), Res) :-
    normalise(A, NA),
    normalise(B, NB),
    Res = or(not(NA), NB).
normalise(and(A, B), and(NA, NB)) :-
    normalise(A, NA),
    normalise(B, NB).
normalise(or(A, B), or(NA, NB)) :-
    normalise(A, NA),
    normalise(B, NB).
normalise(not(A), not(NA)) :-
    normalise(A, NA).
%% normalise(+Formula, -NFormula).
% normalise(_Formula, _NFormula) :-
%     true.
to_cnf(Formula, CNF) :-
    normalise(Formula, Normalised),
    to_cnf_helper(Normalised, CNF).

to_cnf_helper(lit(X), [[X]]).
to_cnf_helper(not(lit(X)), [[not(X)]]).
to_cnf_helper(not(or(A, B)), CNF) :-
    to_cnf_helper(not(A), CNF1),
    to_cnf_helper(not(B), CNF2),
    append(CNF1, CNF2, CNF).
to_cnf_helper(and(A, B), CNF) :-
    to_cnf_helper(A, CNF1),
    to_cnf_helper(B, CNF2),
    append(CNF1, CNF2, CNF).
to_cnf_helper(or(A, B), [[A|Rest]|Tail]) :-
    to_cnf_helper(A, [[A|Rest]|_]),
    to_cnf_helper(B, Tail).
to_cnf_helper(or(A, B), [[B|Rest]|Tail]) :-
    to_cnf_helper(B, [[B|Rest]|_]),
    to_cnf_helper(A, Tail).
to_cnf_helper(or(A, B), [[A, B|Rest]|Tail]) :-
    to_cnf_helper(A, [[A|_]|_]),
    to_cnf_helper(B, [[B|Rest]|_]),
    to_cnf_helper(A, Tail).

%% to_cnf(+Formula, -CNF).
% to_cnf(_Formula, _CNF) :-
%     true.

%% solve(+CNF).
solve(_CNF) :-
    true.
