:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).
:- use_module(library(lists)).

normalise(lit(L), lit(L)) :- !.
normalise(equivalence(A, B), NFormula) :-
    normalise(and(implies(A, B), implies(B, A)), NFormula).
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

normalise(min_one_pos(ListOfVars), NFormula) :- !,
	normalise_list(ListOfVars, NList),
	min_one_pos(NList, NFormula).

normalise(exactly_one_pos(ListOfVars), NFormula) :- !,
	normalise_list(ListOfVars, NList),
	exactly_one_pos(NList, NFormula).

% Concatenate all elements by or
min_one_pos([], lit(false)) :- !.
min_one_pos([H|T], or(H, Rest)) :- !,
	min_one_pos(T, Rest).

% Do the recursive call n times, with n = Length of List
exactly_one_pos(ListOfVars, NFormula) :-
	length(ListOfVars, Length),
	exactly_one_pos(ListOfVars, Length, NFormula), !.

% Create DNF; Each conjuction has all but one element negated.
% Creates a lot of unnecessary elements, but returns a correct result.
exactly_one_pos(_, 0, lit(false)) :- !.
exactly_one_pos([H|T], Length, or(and(H, NegatedList), NFormula)) :-
	% format("~w~n", Length), % TODO: remove debug format
	% format("~w~n", H), % TODO: remove debug format
	NewLength is Length -1,
	append(T, [H], RotatetList),
	negate_list(T, NegatedList), 
	exactly_one_pos(RotatetList, NewLength, NFormula), !.

negate_list([], lit(true)) :- !.
negate_list([H|T], and(not(H), NT)) :- !,
	negate_list(T, NT).

normalise_list([], []) :- !.
normalise_list([H|T], [NH|NT]) :- !,
	normalise(H, NH),
	normalise_list(T, NT).



to_cnf(Formula, CNF) :-
	normalise(Formula, CNF1), !,
	to_cnf2_loop(CNF1, CNF2), !,
	to_cnf3_loop(CNF2, CNF3), !,
	format("~w~n", CNF1), % TODO: remove debug format
	to_list(CNF3, CNF), !.
	
% Push negations inward, until exclusively lit(X) elements
% are negated.
to_cnf2_loop(Formula, Result) :-
	to_cnf2(Formula, TempResult),
	(Formula = TempResult -> Result = Formula ;
		to_cnf2_loop(TempResult, Result)).

% De Morgan's Law
to_cnf2(not(and(P, Q)), or(not(P), not(Q))).
to_cnf2(not(or(P, Q)), and(not(P), not(Q))).

% Double negation
to_cnf2(not(not(P)), P).

% Default
to_cnf2(not(Formula), not(Result)) :-
	to_cnf2(Formula, Result).
to_cnf2(and(P, Q), and(P1, Q1)) :-
	to_cnf2(P, P1),
	to_cnf2(Q, Q1).
to_cnf2(or(P, Q), or(P1, Q1)) :-
	to_cnf2(P, P1),
	to_cnf2(Q, Q1).
to_cnf2(Formula, Formula).


% Shift disjunctions until CNF is reached
to_cnf3_loop(Formula, Result) :-
	to_cnf3(Formula, TempResult),
	(Formula = TempResult -> Result = Formula ;
		to_cnf3_loop(TempResult, Result)).

% Distributive Law
to_cnf3(or(P, and(Q, R)), and(or(P, Q), or(P, R))).
to_cnf3(or(and(Q, R), P), and(or(P, Q), or(P, R))).

% Default
to_cnf3(not(Formula), not(Result)) :-
	to_cnf3(Formula, Result).
to_cnf3(and(P, Q), and(P1, Q1)) :-
	to_cnf3(P, P1),
	to_cnf3(Q, Q1).
to_cnf3(or(P, Q), or(P1, Q1)) :-
	to_cnf3(P, P1),
	to_cnf3(Q, Q1).
to_cnf3(Formula, Formula).


% Translate recursive syntax tree to list of lists.
to_list(lit(P), [[P]]) :- !.
to_list(not(lit(P)), [[not(P)]]) :- !.
to_list(or(P, Q), [CNF]) :- 
    to_list(P, [CNF1]),
    to_list(Q, [CNF2]),
    append(CNF1, CNF2, CNF), !.
to_list(and(P, Q), CNF) :-
    to_list(P, CNF1),
    to_list(Q, CNF2),
    append(CNF1, CNF2, CNF).

% https://en.wikipedia.org/wiki/Logical_equivalence
% TODO: 
% run_tests(verify_sat).
% Tests 12 fails! :
% to_cnf(and(lit(X),and(lit(Y),and(not(lit(Z)),min_one_pos([lit(X),lit(Y),lit(Z)])))), CNF).
% gives:
% CNF = [[X], [Y], [not(Z)], [X, Y, Z, false]]
% which is correct!
% solve() has a problem with the 'false' within the or-statement... it shouldn't!

% i suggest we implement a simplify method to work around the problem.
% simplify possibilities:
% Negation Law:
% 	[[X, not(X), ...]] -> []
% Tautologies:
% 	[[X, X, ...]] -> [[X, ...]]
% definite true
% 	when an or statement contains a true, we can ignore the entire or statement
% when an or statement contains more than one element we can delete every 'false' element,
% as long as the statement is left with at least 1 element.


%% solve(+CNF).
solve(CNF) :-
    subs(CNF, Res),
    solve_all(Res,true).


subs([], []) :-
    !.
subs([H|T], [A|Res]) :-
    is_list(H),
    !,
    subs(H, A),
    subs(T, Res).
subs([A|T], [A|Res]) :-
    var(A),
    !, 
    (A=true; A=false),
    subs(T, Res).
subs([not(A)|T], [not(A)|Res]) :-
    var(A),
    !,
    (A=true; A=false),
    subs(T, Res).
subs([H|T], [H|Res]) :-
    subs(T,Res).


solve_all([], false) :- !.
solve_all([true], true) :- !.
solve_all([false], false) :- !.
solve_all([not(false)], true) :- !.
solve_all([not(true)], false) :- !.

%% and
solve_all([H|T], true) :-
    is_list(H),
    !,
    solve_all(H, true),
    solve_and(T, true),
    !.

%% or
solve_all([H|T], true) :- 
    solve_all([H], Hres),
    !,
    solve_all(T, Tres),
    or(Hres, Tres).


solve_and([], true) :- !.
solve_and(Lst, Res) :-
    solve_all(Lst, Res).


or(true,false).
or(true,true).
or(false,true).