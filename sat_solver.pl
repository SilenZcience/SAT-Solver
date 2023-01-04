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


% Function Entry
to_cnf(Formula, CNF) :-
    normalise(Formula, NFormula),
    to_cnf_helper(NFormula, CNF).

% Default literal
to_cnf_helper(lit(L), [[L]]) :- !.

% Default and
to_cnf_helper(and(P, Q), CNF) :- !,
	to_cnf_helper(P, CNF1),
	to_cnf_helper(Q, CNF2),
	% format("~w~n", "test"), % Debug TODO: remove
    append(CNF1, CNF2, CNF).

% Distributive Law
to_cnf_helper(or(A, and(B, C)), Res) :- !,
	to_cnf(and(or(A, B), or(A, C)), Res).
to_cnf_helper(or(and(B, C), A), Res) :- !,
	to_cnf(and(or(A, B), or(A, C)), Res).

% Default or
to_cnf_helper(or(P, Q), [[P1, Q1]|CNF]) :- !,
	to_cnf_helper(P, [[P1]|CNF1]),
	to_cnf_helper(Q, [[Q1]|CNF2]),
    append(CNF1, CNF2, CNF).

% Default Negation
to_cnf_helper(not(lit(L)), [[not(L)]]) :- !.
% Double Negation
to_cnf_helper(not(not(L)), CNF) :- !,
	to_cnf_helper(L, CNF).

% De Morgan's laws
to_cnf_helper(not(and(P, Q)), CNF) :- !,
	to_cnf_helper(or(not(P), not(Q)), CNF).
to_cnf_helper(not(or(P, Q)), CNF) :- !,
	to_cnf_helper(and(not(P), not(Q)), CNF).

% With Double Negation Solved and De Morgan's Law implemented
% step 2 of to_cnf is finished (according to slides L3)

% With the Disjunctive Distributive Law implemented
% we have finished step 3 of to_cnf

% TODO: even tho the run_tests(cnf). seem to pass we still need to
% implement the other steps on the slides.
% step 4 would be to simplify, yet the tests seem to not want that implemented....
% https://en.wikipedia.org/wiki/Logical_equivalence
% simplify possibilities:
% Negation Law:
% 	and(X, not(X)) -> /
% 	or(X, not(X)) -> /
% Tautologies:
% 	and(X, X) -> X
%	or(X, X) -> X
% Absorption Law:
% 	or(X, and(X, Y)) -> X
% 	and(X, or(X, Y)) -> X


%% solve(+CNF).
solve(_CNF) :-
    true.
