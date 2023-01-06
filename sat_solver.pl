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




to_cnf(Formula, CNF) :-
	normalise(Formula, Normalized),
	to_cnf_helper_all(Normalized, Pushed), !,
	format("~w~n", Pushed), % TODO: remove debug format
	clausal_form(Pushed, CNF).
	
to_cnf_helper_all(Formula, Result) :-
	to_cnf_helper(Formula, TempResult),
	(Formula = TempResult -> Result = Formula ; to_cnf_helper_all(TempResult, Result)).

to_cnf_helper(not(and(P, Q)), or(not(P), not(Q))) :- !.
to_cnf_helper(not(or(P, Q)), and(not(P), not(Q))) :- !.

to_cnf_helper(not(not(P)), P) :- !.
to_cnf_helper(not(Formula), not(Result)) :-
	to_cnf_helper(Formula, Result).

to_cnf_helper(and(P, or(Q, R)), or(and(P, Q), and(P, R))) :- !.
to_cnf_helper(and(P, Q), and(P1, Q1)) :-
	!,
	to_cnf_helper(P, P1),
	to_cnf_helper(Q, Q1).
to_cnf_helper(or(P, and(Q, R)), and(or(P, Q), or(P, R))) :- !.
to_cnf_helper(or(P, Q), or(P1, Q1)) :-
	!,
	to_cnf_helper(P, P1),
	to_cnf_helper(Q, Q1).
to_cnf_helper(Formula, Formula).



clausal_form(and(P, Q), Clauses) :-
    !,
    clausal_form(P, PClauses),
    clausal_form(Q, QClauses),
    append(PClauses, QClauses, Clauses).
clausal_form(or(P, Q), [Clauses]) :- !,
	clausal_form(P, [CNF1]),
	clausal_form(Q, [CNF2]),
	append(CNF1, CNF2, Clauses), !.
clausal_form(lit(L), [[L]]) :- !.
clausal_form(not(lit(L)), [[not(L)]]) :- !.



% % Default literal
% to_cnf_helper(lit(L), [[L]]) :- !.

% % Default and
% to_cnf_helper(and(P, Q), CNF) :- !,
% 	to_cnf_helper(P, CNF1),
% 	to_cnf_helper(Q, CNF2),
% 	% format("~w~n", "test"), % Debug TODO: remove
%     append(CNF1, CNF2, CNF).

% % Distributive Law
% to_cnf_helper(or(A, and(B, C)), CNF) :-
% 	to_cnf_helper(and(or(A, B), or(A, C)), CNF),
% 	!.
% to_cnf_helper(or(and(B, C), A), CNF) :-
% 	to_cnf_helper(and(or(A, B), or(A, C)), CNF),
% 	!.

% % Default or
% to_cnf_helper(or(P, Q), [CNF]) :- 
% 	to_cnf_helper(P, [CNF1]),
% 	to_cnf_helper(Q, [CNF2]),
%     append(CNF1, CNF2, CNF), !.

% % Default Negation
% to_cnf_helper(not(lit(L)), [[not(L)]]) :- !.
% % Double Negation
% to_cnf_helper(not(not(L)), CNF) :- !,
% 	to_cnf_helper(L, CNF).

% % De Morgan's laws
% to_cnf_helper(not(and(P, Q)), CNF) :- !,
% 	to_cnf_helper(or(not(P), not(Q)), CNF).
% to_cnf_helper(not(or(P, Q)), CNF) :- !,
% 	to_cnf_helper(and(not(P), not(Q)), CNF).

% flattening_list([], []).
% flattening_list([H|T], R) :- 
%     is_list(H),
%     flattening_list(T, T1), 
%     !, 
%     append(H, T1, R).
% flattening_list([H|T], [H|T1]) :- 
%     flattening_list(T, T1).

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