
:- use_module(sat_solver).
:- use_module(library(lists)).
:- use_module(library(plunit)).

:- begin_tests(cnf).

test(to_cnf1,[true(Res == [[X],[true]])]) :-
    to_cnf(and(lit(X),lit(true)), Res).

test(to_cnf2,[true(Res == [[X],[true,false]])]) :-
    to_cnf(and(lit(X), or(lit(true),lit(false))), Res).

test(to_cnf3,[true(Res == [[not(A),B]])]) :-
    to_cnf(implies(not(not(lit(A))),lit(B)), Res).

test(to_cnf4,[true(Res == [[A]])]) :-
    to_cnf(lit(A), Res).

test(to_cnf5,[true(Res == [[A,B]])]) :-
    to_cnf(or(lit(A),lit(B)), Res).

test(to_cnf6,[true(Res == [[A],[B]])]) :-
    to_cnf(and(lit(A),lit(B)), Res).

test(to_cnf_bt1,[all(Res = [[[not(A),B]]])]) :-
    to_cnf(implies(not(not(lit(A))),lit(B)), Res),
    is_list(Res).

test(to_cnf_bt2,[all(Res = [[[X],[true,false]]])]) :-
    to_cnf(and(lit(X), or(lit(true),lit(false))), Res),
    is_list(Res).

test(to_cnf_bt3,[all(Res = [[[A,B]]])]) :-
    to_cnf(or(lit(A),lit(B)), Res),
    is_list(Res).

test(to_cnf_bt2,[all(Res = [[[A],[B]]])]) :-
    to_cnf(and(lit(A),lit(B)), Res),
    is_list(Res).

:- end_tests(cnf).

:- begin_tests(verify_sat).

test(sat0, [nondet,all(X == [true])]) :-
    to_cnf(lit(X), CNF),
    solve(CNF).

test(sat1, [nondet,all(X == [true])]) :-
    to_cnf(and(lit(X),lit(true)), CNF),
    solve(CNF).

test(sat2, [nondet,all(X == [true])]) :-
    to_cnf(or(lit(X),and(lit(true),lit(false))), CNF),
    solve(CNF).

test(sat3, [nondet,all([X,Y] == [[false,true]])]) :-
    to_cnf(or(lit(false),and(not(lit(X)),lit(Y))), CNF),
    solve(CNF).

test(sat4, [nondet,true(X == false; Y == true)]) :-
    to_cnf(or(not(lit(X)),lit(Y)), CNF),
    solve(CNF).

test(sat5, [nondet,all([X,Y] == [[true,true]])]) :-
    to_cnf(and(lit(X),lit(Y)), CNF),
    solve(CNF).

test(sat6, [nondet,all(X == [false])]) :-
    to_cnf(not(lit(X)), CNF),
    solve(CNF).

test(sat7, [nondet,all(X == [true])]) :-
    to_cnf(lit(X), CNF),
    solve(CNF).

test(sat8, [nondet]) :-
    to_cnf(not(and(implies(lit(X),not(or(lit(Y),lit(Z)))), or(and(lit(X),lit(Y)), not(lit(Z))))), CNF),
    is_list(CNF),
    solve(CNF).

test(sat9, [nondet,true((X == true, Y == false, Z == false); (X == false, Y == true, Z == false); (X == false, Y == false, Z == true))]) :-
    to_cnf(exactly_one_pos([lit(X),lit(Y),lit(Z)]), CNF),
    solve(CNF).

test(sat10, [nondet,true((X == false, Y == true, Z == false); (X == false, Y == false, Z == true))]) :-
    to_cnf(and(not(lit(X)),exactly_one_pos([lit(X),lit(Y),lit(Z)])), CNF),
    solve(CNF).

test(sat11, [nondet,true((X == false, Y == false, Z == true))]) :-
    to_cnf(and(not(lit(X)),and(not(lit(Y)),exactly_one_pos([lit(X),lit(Y),lit(Z)]))), CNF),
    solve(CNF).

test(sat12, [nondet,true((X == true, Y == true, Z == false))]) :-
    to_cnf(and(lit(X),and(lit(Y),and(not(lit(Z)),min_one_pos([lit(X),lit(Y),lit(Z)])))), CNF),
    solve(CNF).

test(sat13, [nondet,all(X == [true])]) :-
    to_cnf(exactly_one_pos([lit(X)]), CNF),
    solve(CNF).

test(sat14, [nondet,all(X == [true])]) :-
    to_cnf(min_one_pos([lit(X)]), CNF),
    solve(CNF).

test(sat15, [nondet]) :-
    to_cnf(equivalence(lit(X),lit(Y)), CNF),
    solve(CNF),
    X == true,
    Y == true.

test(sat16, [nondet]) :-
    to_cnf(equivalence(lit(X),lit(Y)), CNF),
    solve(CNF),
    X == false,
    Y == false.

test(sat17, [nondet,all([X,Y] == [[false,true]])]) :-
    to_cnf(and(not(lit(X)),and(lit(Y),implies(lit(X),lit(Y)))), CNF),
    solve(CNF).

test(sat18, [nondet,all([X,Y] == [[true,true]])]) :-
    to_cnf(and(lit(X),equivalence(lit(X),lit(Y))), CNF),
    solve(CNF).

test(sat19, [nondet,all([X,Y] == [[true,true]])]) :-
    to_cnf(and(min_one_pos([lit(X),lit(Y)]),equivalence(lit(X),lit(Y))), CNF),
    solve(CNF).

:- end_tests(verify_sat).

:- begin_tests(verify_unsat).

test(unsat0, [fail]) :-
    to_cnf(and(not(implies(lit(X),lit(Y))),and(not(lit(X)),lit(Y))), CNF),
    solve(CNF).

test(unsat1, [fail]) :-
    to_cnf(and(not(implies(lit(X),lit(Y))),and(not(lit(X)),lit(Y))), CNF),
    solve(CNF).

test(unsat2, [fail]) :-
    to_cnf(and(not(lit(X)),lit(X)), CNF),
    solve(CNF).

test(unsat3, [fail]) :-
    to_cnf(or(and(not(lit(X)),lit(X)), and(not(lit(Y)),not(not(lit(Y))))), CNF),
    solve(CNF).

test(unsat4, [fail]) :-
    to_cnf(and(and(not(implies(lit(X),lit(Y))),and(not(lit(X)),lit(Y))),and(lit(Z),not(lit(Z)))), CNF),
    solve(CNF).

test(unsat5, [fail]) :-
    to_cnf(and(not(lit(X)),and(not(lit(Y)),and(not(lit(Z)),exactly_one_pos([lit(X),lit(Y),lit(Z)])))), CNF),
    solve(CNF).

test(unsat6, [fail]) :-
    to_cnf(and(lit(X),and(lit(Y),and(not(lit(Z)),exactly_one_pos([lit(X),lit(Y),lit(Z)])))), CNF),
    solve(CNF).

test(unsat7, [fail]) :-
    to_cnf(and(not(lit(X)),and(not(lit(Y)),and(not(lit(Z)),min_one_pos([lit(X),lit(Y),lit(Z)])))), CNF),
    solve(CNF).

test(unsat8, [fail]) :-
    to_cnf(equivalence(lit(X),lit(Y)), CNF),
    solve(CNF),
    X == false,
    Y == true.

test(unsat9, [fail]) :-
    to_cnf(equivalence(lit(false),lit(true)), CNF),
    solve(CNF).

test(unsat10, [fail]) :-
    to_cnf(and(lit(X),and(not(lit(Y)),equivalence(lit(X),lit(Y)))), CNF),
    solve(CNF).

test(unsat11, [fail]) :-
    to_cnf(and(lit(X),and(not(lit(Y)),implies(lit(X),lit(Y)))), CNF),
    solve(CNF).

test(unsat12, [fail]) :-
    to_cnf(and(exactly_one_pos([lit(X),lit(Y)]),equivalence(lit(X),lit(Y))), CNF),
    solve(CNF).

:- end_tests(verify_unsat).
