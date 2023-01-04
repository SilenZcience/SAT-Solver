:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).
:- use_module(library(lists)).

normalise(lit(L), lit(L)) :- !.
normalise(equivalence(P, Q), and(or(not(P1), Q1), or(not(Q1), P1))) :- !,
    normalise(P, P1),
    normalise(Q, Q1).
normalise(implies(P, Q), or(not(P1), Q1)) :- !,
    normalise(P, P1),
    normalise(Q, Q1).
normalise(and(P, Q), and(P1, Q1)) :- !,
    normalise(P, P1),
    normalise(Q, Q1).
normalise(or(P, Q), or(P1, Q1)) :- !,
    normalise(P, P1),
    normalise(Q, Q1).
normalise(not(P), not(P1)) :- !,
    normalise(P, P1).

normalise(min_one_pos(List), NFormula) :-
	normalise_list(List, NList),
	normalise_min_one_pos(NList, NFormula).

normalise(exactly_one_pos(List), NFormula) :-
	normalise_list(List, NList),
	normalise_exactly_one_pos(NList, NFormula).

normalise_min_one_pos([], lit(false)).
normalise_min_one_pos([H|T], or(H, Rest)) :-
	normalise_min_one_pos(T, Rest).

normalise_exactly_one_pos([], lit(false)).
normalise_exactly_one_pos([H|T], or(H, and(not(H), Rest))) :-
	normalise_exactly_one_pos(T, Rest).

normalise_list([], []).
normalise_list([H|T], [NH|NT]) :-
	normalise(H, NH),
	normalise_list(T, NT).

%% to_cnf(+Formula, -CNF).
to_cnf(_Formula, _CNF) :-
    true.

%% solve(+CNF).
solve(_CNF) :-
    true.
