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

% TODO: fix tests unsat6
%% solve(+CNF).
solve(CNF) :- 
	simplify_cnf(CNF, NEWCNF),
	dpll(NEWCNF).

dpll([]).
dpll(CNF) :-
    % \+has_empty_clause(CNF),
    unit_clause(CNF, [Var]),
    \+check_CNF(CNF, Var),
    (var(Var) -> Var = true; (is_list(Var), get_element(0,Var, New), var(New)) -> New = true ; term_variables(Var, Res), member(This, Res), This = false),
    simplify(Var, CNF, NEWCNF, 0), 
    dpll(NEWCNF), !.
dpll(CNF) :-
    % \+has_empty_clause(CNF),
    \+unit_clause(CNF, _), 
    term_variables(CNF, Vars),
    member(Var, Vars),
    !,
    (Var = true, simplify(Var, CNF, NEWCNF, 1); Var = false, negate(NegLit, Var), simplify(NegLit, CNF, NEWCNF, 1)), 
    dpll(NEWCNF).

% überprüft, ob es eine Unit-Klausel gibt
unit_clause([H|_],H) :-
    length(H, 1),
    !.
unit_clause([_|T],R) :-
    unit_clause(T,R).

% überprüft, ob die gegebene Formel in CNF bereits eine Lösung enthält
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

% wird verwendet, um die CNF zu vereinfachen
simplify(Lit, CNF, NEWCNF, N) :-
    \+check_CNFBranch(CNF),
    (var(Lit) ->
        negate(NegLit, Lit)
        ;
        negate(Lit, NegLit)),
    maplist(remover(NegLit), CNF, CNF1),
    (N == 0 -> 
        simplify_dpllUnit(Lit, CNF1, CNF2);
        simplify_dpllBranch(Lit, CNF1, CNF2)),
    exclude(empty, CNF2, NEWCNF).

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
    % \+ H \== R, 
	H == R,
    remover(R, T, T2), 
    !.
remover(R, [H|T], [H|T2]) :- 
    % H \== R, 
    remover(R, T, T2), 
    !.

empty([]).

check_CNFBranch(CNF) :-
    get_element(0, CNF, CNF1),
    get_element(0, CNF1, CNF2),
    get_element(1, CNF1, CNF3),
    get_element(0, CNF2, Lit1),
    get_element(0, CNF3, Lit2),
    negate(NegLit, Lit2),
    Lit1 == NegLit.
     

get_element(0, [H|_], H) :- !.
get_element(N, [_|T], H) :- 
    N > 0, 
    N1 is N - 1, 
    get_element(N1, T, H), !.


simplify_cnf(CNF, NEWCNF) :- 
	% not(true) -> false, not(false) -> true
	dissolve_negations(CNF, CNF1), !,
	% delete disjunction if it contains true
	remove_true_clauses_direct(CNF1, CNF2), !,
	% delete disjunction if it contains 'X' and 'not(X)'
	remove_true_clauses_indirect(CNF2, CNF3), !,
	% remove duplicated elements within each disjunction
	remove_duplicate_elements(CNF3, CNF4), !,
	% remove every 'false' element. if a disjunctive clause only contains 'false': fail!
	remove_false_elements(CNF4, CNF5), !,
	% remove duplicated disjunctions
	remove_duplicate_disjunctions(CNF5, NEWCNF), !.


% [[X, not(true)], [not(false)]] -> [[X, false], [true]]
dissolve_negations([], []).
dissolve_negations([Clause|Clauses], [DissolvedClause|DissolvedClauses]) :-
	dissolve_negations_clause(Clause, DissolvedClause), !,
	dissolve_negations(Clauses, DissolvedClauses).

dissolve_negations_clause([], []).
dissolve_negations_clause([not(X)|Literals], [false|DissolvedLiterals]) :-
	X==true,
	dissolve_negations_clause(Literals, DissolvedLiterals), !.
dissolve_negations_clause([not(X)|Literals], [true|DissolvedLiterals]) :-
	X==false,
	dissolve_negations_clause(Literals, DissolvedLiterals), !.
dissolve_negations_clause([Literal|Literals], [Literal|DissolvedLiterals]) :-
	dissolve_negations_clause(Literals, DissolvedLiterals), !.


% [[X, Y, true], [Z]] -> [[Z]]
remove_true_clauses_direct([],[]).
remove_true_clauses_direct([Clause|Clauses], Result) :-
	(   lit_member(Clause, true)
	->  remove_true_clauses_direct(Clauses, Result)
	;   Result = [Clause|NewClause],
		remove_true_clauses_direct(Clauses, NewClause)
	).

lit_member([], _) :- fail.
lit_member([Head|_], X) :-
	Head == X, !.
lit_member([_|Tail], X) :-
	lit_member(Tail, X).


% [[X, Y, not(X)], [Z]] -> [[Z]]
remove_true_clauses_indirect([], []).
remove_true_clauses_indirect([Clause|Clauses], Result) :-
	(   var_member_x_notx(Clause)
	->  remove_true_clauses_indirect(Clauses, Result)
	;   Result = [Clause|NewClause],
		remove_true_clauses_indirect(Clauses, NewClause)
	).


var_member_x_notx(Clause) :-
	length(Clause, Length),
	var_member_x_notx(Clause, Length), !.
var_member_x_notx(_, 0) :- fail, !.
var_member_x_notx([Head|Tail], Length) :-
	lit_member(Tail, not(Head));
	(Length > 0,
	NewLength is Length -1,
	append(Tail, [Head], RotatetList),
	var_member_x_notx(RotatetList, NewLength), !).


% [[X, X, Y]] -> [[X, Y]]
remove_duplicate_elements([], []).
remove_duplicate_elements([Clause|Clauses], [ClauseNoDups|Result]) :-
	sort(Clause, ClauseNoDups),
	remove_duplicate_elements(Clauses, Result).


% [[X, Y, false]] -> [[X, Y]]
% [[false]] -> fail!
remove_false_elements([], []).
remove_false_elements([Clause|Clauses], [CleanClause|CleanClauses]) :-
	lit_remover(Clause, false, CleanClause),
	CleanClause \= [],
	remove_false_elements(Clauses, CleanClauses).

lit_remover([], _, []) :- !.
lit_remover([Head|Tail], R, Result) :- 
	Head == R, 
	lit_remover(Tail, R, Result), 
	!.
lit_remover([Head|Tail], R, [Head|Result]) :- 
	lit_remover(Tail, R, Result), 
	!.

% [[X, Y], [X, Y]] -> [[X, Y]]
remove_duplicate_disjunctions(CNF, CleanedCNF) :-
	sort(CNF, CleanedCNF).