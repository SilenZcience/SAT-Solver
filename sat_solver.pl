:- module(sat_solver,[normalise/2, to_cnf/2, solve/1]).

:- load_test_files([]).
:- use_module(library(lists)).

% --------------- Version 1 normalise ---------------
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
min_one_pos([H], H) :- !.
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
% --------------- End Version 1 normalise ---------------

% % --------------- Version 2 normalise ---------------
% normalise(Formula, NFormula) :-
%     (Formula = lit(A) -> NFormula = lit(A)) ;
%     (Formula = equivalence(A, B) -> normalise(and(or(not(A), B), or(not(B), A)), NFormula)) ;
%     (Formula = implies(A, B) -> normalise(A, AA), normalise(B, BB), NFormula = or(not(AA), BB)) ;
%     (Formula = and(A, B) -> normalise(A, AA), normalise(B, BB), NFormula = and(AA, BB)) ;
%     (Formula = or(A, B) -> normalise(A, AA), normalise(B, BB), NFormula = or(AA, BB)) ;
%     (Formula = not(A) -> normalise(A, AA), NFormula = not(AA)) ;
% 	(Formula = min_one_pos(ListOfVars) -> min_one_pos(ListOfVars, NFormula)) ;
% 	(Formula = exactly_one_pos(ListOfVars) -> exactly_one_pos(ListOfVars, NFormula)).

% min_one_pos([H], H) :- !.
% min_one_pos([H|T], R) :- 
% 	min_one_pos(T, R1),
% 	R = or(H, R1).

% exactly_one_pos([H|T], H) :-
% 	length([H|T], 1), !.
% exactly_one_pos(L, and(A, not(B))) :- exactly_one_pos_xor(L, A), exactly_one_pos_and(L, B).
% exactly_one_pos_xor([H], H).
% exactly_one_pos_xor([H|T], or(and(not(H),B),and(H, not(B)))) :- exactly_one_pos_xor(T, B).
% exactly_one_pos_and([H], H).
% exactly_one_pos_and([H|T], and(H, B)) :- exactly_one_pos_and(T, B).
% % --------------- End Version 2 normalise ---------------

% --------------- Version 1 to_cnf ---------------
to_cnf(Formula, CNF) :-
	% to_cnf (step1 on the slides = normalise)
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
% --------------- End Version 1 to_cnf ---------------

% % --------------- Version 2 to_cnf ---------------
% to_cnf(Formula, CNF) :-
% 	normalise(Formula, Normalised), !,
% 	to_cnf_push_negations_inward_loop(Normalised, CNF2),
% 	push_disjunctions_inward_loop(CNF2, CNF3),
% 	listify(CNF3, CNF).
	
% to_cnf_push_negations_inward_loop(Formula, Result) :-
% 	to_cnf_push_negations_inward(Formula, Temp),
% 	(Formula = Temp -> Result = Formula ;
% 		to_cnf_push_negations_inward_loop(Temp, Result)).

% to_cnf_push_negations_inward(Formula, Result) :-
% 	Formula = not(not(A)) -> to_cnf_push_negations_inward(A, Result) ;
% 	Formula = not(or(A, B)) -> (to_cnf_push_negations_inward(A, AA), to_cnf_push_negations_inward(B, BB),
% 								Result = and(not(AA), not(BB))) ;
%     Formula = not(and(A, B)) -> (to_cnf_push_negations_inward(A, AA), to_cnf_push_negations_inward(B, BB),
% 								Result = or(not(AA), not(BB))) ;
%     Formula = not(A) -> (to_cnf_push_negations_inward(A, B),
% 						Result = not(B)) ;
%     Formula = and(A, B) -> (to_cnf_push_negations_inward(A, AA), to_cnf_push_negations_inward(B, BB),
% 							Result = and(AA, BB)) ;
%     Formula = or(A, B) -> (to_cnf_push_negations_inward(A, AA), to_cnf_push_negations_inward(B, BB),
% 							Result = or(AA, BB)) ;
%     Formula = lit(_) -> Result = Formula.

% push_disjunctions_inward_loop(Formula, Result) :-
% 	push_disjunctions_inward(Formula, Temp),
% 	(Formula = Temp -> Result = Formula ;
% 		push_disjunctions_inward_loop(Temp, Result)).

% push_disjunctions_inward(Formula, Result) :-
% 	(Formula = or(A, and(B, C)) ;
% 	Formula = or(and(B, C), A)) ->
% 							(push_disjunctions_inward(A, AA), push_disjunctions_inward(B, BB), push_disjunctions_inward(C, CC),
% 							Result = and(or(AA, BB), or(AA, CC))) ;
% 	Formula = not(A) -> (push_disjunctions_inward(A, AA), Result = not(AA)) ;
% 	Formula = and(A, B) -> (push_disjunctions_inward(A, AA), push_disjunctions_inward(B, BB),
% 							Result = and(AA, BB)) ;
% 	Formula = or(A, B) -> (push_disjunctions_inward(A, AA), push_disjunctions_inward(B, BB),
% 							Result = or(AA, BB)) ;
% 	Formula = lit(_) -> Result = Formula.

% listify(Literal, List) :- Literal = lit(A), List = [[A]].
% listify(NotLiteral, List) :- NotLiteral = not(lit(A)), List = [[not(A)]].
% listify(OrExpression, List) :-
% 	OrExpression = or(A, B),
%     listify(A, [AA]), listify(B, [BB]),
%     append(AA, BB, C),
% 	List = [C].
% listify(AndExpression, List) :-
% 	AndExpression = and(A, B),
%     listify(A, AA), listify(B, BB),
%     append(AA, BB, C),
% 	List = C.
% % --------------- End Version 2 to_cnf ---------------

% % --------------- Version TEST solve ---------------
% solve(CNF) :-
% 	simplify_cnf(CNF,  SimplifiedCNF), !,
% 	dpll(SimplifiedCNF).
% % solve(CNF) :-
% % 	dpll(CNF).

% dpll([]).
% dpll(CNF) :-
% 	unit_propagate(CNF, R),
%     term_variables(CNF, Vars),
%     member(Var, Vars), !,
%     (Var = true, remove_disjunctions_with_literal(true, R, RN);
% 	Var = false, remove_disjunctions_with_literal(not(false), R, RN)),
%     dpll(RN).


% unit_propagate([], []).
% unit_propagate([H|T], R) :-
% 	length(H, 1),
% 	contradicting_unit_clauses(H, [H|T], [NH|NT]),
% 	unit_propagate([[], NH|NT], R), !.
% unit_propagate([H|T], [H|NT]) :-
% 	unit_propagate(T, NT), !.


% contradicting_unit_clauses([Element], List, NList) :-
% 	check_contradiction(Element, List),
% 	remove_contradicting([Element], List, NList).

% check_contradiction(Element, [H|_]) :-
% 	(Element == not(X), H == [X]; H == [not(Element)]).
% check_contradiction(Element, [_|T]) :-
% 	check_contradiction(Element, T).


% remove_contradicting([A], [H|T], R) :-
% 	([A] == H; [not(A)] == H),
% 	remove_contradicting([A], T, R), !. 
% remove_contradicting(A, [H|T], [H|NT]) :-
% 	remove_contradicting(A, T, NT), !.
% remove_contradicting(_, [], []).


% remove_disjunctions_with_literal(_, [], []).
% remove_disjunctions_with_literal(Literal, [H|T], R) :- 
%     (lit_member(H, Literal) -> remove_disjunctions_with_literal(Literal, T, R);
% 	remove_disjunctions_with_literal(Literal, T, Result), R = [H|Result]).
% % --------------- End Version TEST solve ---------------

% --------------- Version 1 solve ---------------
% solve(CNF) :-
% 	simplify_cnf(CNF, Simplified), !,
% 	dpll_algorithm(Simplified).
solve(CNF) :-
	dpll_algorithm(CNF).

% dpll oriented on pseudocode from the slides
% If F = {} then 
% 	return (SAT, p);
dpll_algorithm([]).
dpll_algorithm(CNF) :-
	% If F contains clause {} then 
	%	 return (UNSAT, null);
	\+ member([], CNF),
	% (F,p) = Unit-Propagate(F, p);
	unit_propagation(CNF, P),

	dpll_algorithm(P), !.
dpll_algorithm(CNF) :-
	% If F contains clause {} then 
	%	 return (UNSAT, null);
	\+ member([], CNF),
	% x = literal such that x and ¬x are not in p;
    term_variables(CNF, Vars),
	member(Var, Vars), !,
    (Var = true,
    simplify(Var, CNF, Simplified) ; 
    Var = false, 
    negate(Var, NegatedVar), 
    simplify(NegatedVar, CNF, Simplified)),

    dpll_algorithm(Simplified).

% unit propagation oriented on pseudocode from the slides
unit_propagation(CNF, P) :-
	get_unit_clause(CNF, [Var]),
	% Var is either 'not(_)' or '_'
	% var(Var) -> Var = '_'
	% otherwise get term_variable from 'not(_)'
	% p = p U {x};
	(var(Var), Var = true;
	term_variables(Var, Res), member(false, Res)),
	% F = F|{x};
	remove_disjunctions_with_literal(Var, CNF, P),!.

get_unit_clause([H|_], H) :-
	length(H, 1).
get_unit_clause([_|T], R) :-	
	get_unit_clause(T, R).

simplify(Lit, CNF, Simplified) :-
    negate(Lit, NegatedLit),
	% Delete all negated occurences our current Var
    maplist(remove_literal(NegatedLit), CNF, CNF1),
	% Delete all Disjunctions containing our current Var
    remove_disjunctions_with_literal(Lit, CNF1, Simplified).


negate(not(X),X) :- !.
negate(X,not(X)) :- !.


remove_disjunctions_with_literal(_, [], []).
remove_disjunctions_with_literal(Literal, [H|T], R) :-
	(lit_member(H, Literal) -> R = RT ; R = [H|RT]),
	remove_disjunctions_with_literal(Literal, T, RT).


%% this predicate may be interposed between solve() and dpll().
%% in case of very large formulas, it may increase the performance.
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

% lit_member([], _) :- fail.
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
	remove_literal(false, Clause, CleanClause),
	CleanClause \= [],
	remove_false_elements(Clauses, CleanClauses).

remove_literal(_, [], []).
remove_literal(Literal, [H|T], Cleansed) :-
    (H == Literal -> remove_literal(Literal, T, Cleansed);
	remove_literal(Literal, T, Tail), Cleansed = [H|Tail]).

% [[X, Y], [X, Y]] -> [[X, Y]]
remove_duplicate_disjunctions(CNF, CleanedCNF) :-
	sort(CNF, CleanedCNF).
% --------------- End Version 1 solve ---------------

% % --------------- Version 2 solve ---------------
% solve(CNF) :-
% 	dpll(CNF).

% dpll([]).
% dpll(CNF) :-
% 	% unit propagation
%     is_unit_clause(CNF, [Var]),
%     (var(Var) -> Var = true;
% 	term_variables(Var, Res),
% 	member(false, Res)),
%     disjunction_remover(Var, CNF, NEWCNF),
%     dpll(NEWCNF), !.

% dpll(CNF) :-
%     \+is_unit_clause(CNF, _), 
%     term_variables(CNF, Vars),
%     member(Var, Vars), !,
%     (Var = true,
%     simplify(Var, CNF, NEWCNF) ; 
%     Var = false, 
%     negate(Var, NegatedVar), 
%     simplify(NegatedVar, CNF, NEWCNF)),
%     dpll(NEWCNF).


% is_unit_clause([H|T], R) :-
% 	(length(H, 1) -> R = H; is_unit_clause(T, R)).
	

% simplify(Lit, CNF, Simplified) :-
%     negate(Lit, NegatedLit),
%     maplist(remover(NegatedLit), CNF, CNF1),
%     simplify_dpllUnit(Lit, CNF1, CNF2),
%     exclude(empty_clause, CNF2, Simplified).


% simplify_dpllUnit(_Lit, [], []).
% simplify_dpllUnit(Lit, [H|T], [V|Simplified]) :- 
%     (termContainsLiteral(Lit, H) -> 
%         V = [] ; 
%         termContainsLiteral([Lit], H) -> 
%             K = H, remover([Lit], K, V) ; 
%             V = H, V \== Lit), 
%     simplify_dpllUnit(Lit, T, Simplified).

% negate(not(X),X) :- !.
% negate(X,not(X)) :- !.


% termContainsLiteral(false, X) :- 
%     var(X), !, 
%     X == false.
% termContainsLiteral(true, X) :- 
%     var(X), !, 
%     X == true.
% termContainsLiteral(X, [H|T]) :- 
%     X == H, !; 
%     termContainsLiteral(X, T), !.


% remover(_, [], []) :- !.
% remover(R, [H|T], T2) :- 
% 	H == R,
%     remover(R, T, T2), !.
% remover(R, [H|T], [H|T2]) :- 
%     remover(R, T, T2), !.

% empty_clause([]) :- !.


% disjunction_remover(_, [], []).
% disjunction_remover(Literal, [H|T], R) :- 
%     (lit_member(H, Literal) -> disjunction_remover(Literal, T, R);
% 	disjunction_remover(Literal, T, Result), R = [H|Result]).

% % --------------- End Version 2 solve ---------------