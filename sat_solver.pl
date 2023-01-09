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
% Creates a lot of unnecessary elements, but returns a correct result!
exactly_one_pos(_, 0, lit(false)) :- !.
exactly_one_pos([H|T], 1, NFormula) :- 
	negate_list(T, NegatedList),
	NFormula = and(H, NegatedList).
exactly_one_pos([H|T], Length, NFormula) :-
	NewLength is Length -1,
	append(T, [H], RotatetList),
	negate_list(T, NegatedList),
	exactly_one_pos(RotatetList, NewLength, NFormulaR), !,
	NFormula = or(and(H, NegatedList), NFormulaR).

negate_list([], lit(true)) :- !.
negate_list([H|T], Result) :-
    negate_list(T, NT),
    (
		% simplify (last element doesn't need to call 'and')
		NT = lit(true) ->  Result = not(H);
		Result = and(not(H), NT)
    ).

% normalise all elements from min_one_pos and exactly_one_pos
% unnecessary if only lit() values are used within these terms.
normalise_list([], []) :- !.
normalise_list([H|T], [NH|NT]) :- !,
	normalise(H, NH),
	normalise_list(T, NT).



to_cnf(Formula, CNF) :-
	normalise(Formula, CNF1), !,
	to_cnf2_loop(CNF1, CNF2), !,
	to_cnf3_loop(CNF2, CNF3), !,
	% format("~w~n", CNF1), % Debug
	% format("~w~n", CNF2), % Debug
	% format("~w~n", CNF3), % Debug
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

% TODO: fix tests unsat5, unsat6, unsat12
%% solve(+CNF).
solve(CNF) :- 
    remove_elements_already_set(CNF, NEWCNF), 
    (CNF == NEWCNF -> 
        dpll(NEWCNF) ; 
        check_brackets(NEWCNF, Res), 
        dpll(Res)).

check_brackets(CNF, NEWCNF) :-
    maplist(term_to_atom, CNF, CNF1),
    atomics_to_string(CNF1, CNF2),
    split_string(CNF2, '[', '', Res),
    get_element(0, Res, Temp1),
    get_element(1, Res, Temp2),
    ((Temp1 == "", Temp2 == "") -> 
        append(CNF, NEWCNF) ; 
        NEWCNF = CNF).

%%[[false, [not(X)], [Y]]] -> [[[not(X)],[Y]]]
remove_elements_already_set(CNF, NEWCNF) :-
    maplist(remover(true), CNF, Res),
    maplist(remover(false), Res, Res1),
    maplist(remover([true]), Res1, Res2),
    maplist(remover([false]), Res2, Res3),
    exclude(empty, Res3, NEWCNF).

has_empty_clause(CNF) :-
    member([], CNF), !.

unit_clause([H|_],H) :-
    length(H, 1),
    H \== true, 
    H \== false, 
    !.
unit_clause([_|T],R) :-
    unit_clause(T,R).

negate(not(X),X) :- !.
negate(X,not(X)) :- !.

member_checkUnit(false, X) :- 
    var(X), 
    !, 
    X == false.
member_checkUnit(true, X) :- 
    var(X), 
    !, 
    X == true.
member_checkUnit(X, [H|T]) :- 
    X == H, !; 
    member_checkUnit(X, T), !.


member_checkBranch(false, X) :- 
    var(X), 
    !, 
    X == false.
member_checkBranch(true, X) :- 
    var(X), 
    !, 
    X == true.
member_checkBranch(X, [H|T]) :- 
    X == H, !; 
    member_checkBranch(X, T), !.
member_checkBranch(X, [H|T]) :- 
    is_list(H), member(X, H) ; 
    member_checkBranch(X, T), !.


remover(_, [], []) :- !.
remover(R, [H|T], T2) :- 
    \+ H \== R, 
    remover(R, T, T2), 
    !.
remover(R, [H|T], [H|T2]) :- 
    H \== R, 
    remover(R, T, T2), 
    !.

simplify_dpllUnit(_Lit, [], []).
simplify_dpllUnit(Lit, [H|T], [V|Simplified]) :- 
    (member_checkUnit(Lit, H) -> 
        V = [] ; 
        member_checkUnit([Lit], H) -> 
            K = H, remover([Lit], K, V); 
            V = H, V \== Lit), simplify_dpllUnit(Lit, T, Simplified).

simplify_dpllBranch(_Lit, [], []).
simplify_dpllBranch(Lit, [H|T], [V|Simplified]) :- 
    (member_checkBranch(Lit, H) -> V = [] ; 
    member_checkBranch([Lit], H) -> K = H, 
    remover([Lit], K, V); V = H, V \== Lit), 
    simplify_dpllBranch(Lit, T, Simplified).

empty([]).

check_CNF(CNF, Var) :-
    length(CNF, N),
    maplist(length, CNF, NEWCNF),
    (var(Var) ->
        negate(NegLit, Var)
        ;
        negate(Var, NegLit)),
    ((N == 2, length(NEWCNF, 2), (member_checkUnit(NegLit, CNF);member_checkUnit([NegLit], CNF);member_checkUnit(2, NEWCNF), get_element(1, CNF, Temp), member_checkUnit([Var], Temp), member_checkUnit([NegLit], Temp))) -> true ;
    list_to_set(CNF, Temp),
    ((N == 3, length(Temp, 1)) -> true;fail)).

check_CNFBranch(CNF) :-
    get_element(0, CNF, CNF1),
    get_element(0, CNF1, CNF2),
    get_element(1, CNF1, CNF3),
    get_element(0, CNF2, Lit1),
    get_element(0, CNF3, Lit2),
    negate(NegLit, Lit2),
    Lit1 == NegLit.

simplify(Lit, CNF, NEWCNF, N) :-
    \+check_CNFBranch(CNF),
    (var(Lit) ->
        negate(NegLit, Lit)
        ;
        negate(Lit, NegLit)),
    maplist(remover(NegLit), CNF, CNF1),
    maplist(remover([NegLit]), CNF1, CNF2),
    (N == 0 -> 
        simplify_dpllUnit(Lit, CNF2, CNF3);
        simplify_dpllBranch(Lit, CNF2, CNF3)),
    exclude(empty, CNF3, NEWCNF).


dpll([]).
dpll(CNF) :-
    \+has_empty_clause(CNF),
    unit_clause(CNF, [Var]),
    \+check_CNF(CNF, Var),
    (var(Var) -> Var = true; (is_list(Var), get_element(0,Var, New), var(New)) -> New = true ; term_variables(Var, Res), member(This, Res), This = false),
    simplify(Var, CNF, NEWCNF, 0), 
    dpll(NEWCNF), !.
dpll(CNF) :-
    \+has_empty_clause(CNF),
    \+unit_clause(CNF, _), 
    term_variables(CNF, Vars),
    member(Var, Vars),
    !,
    (Var = true, simplify(Var, CNF, NEWCNF, 1); Var = false, negate(NegLit, Var), simplify(NegLit, CNF, NEWCNF, 1)), 
    dpll(NEWCNF).
        

get_element(0, [H|_], H) :- !.
get_element(N, [_|T], H) :- 
    N > 0, 
    N1 is N - 1, 
    get_element(N1, T, H), !.
