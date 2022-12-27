Export the necessary predicates in the solver module.
The tests from the .plt file are loaded in your module automatically by using load_test_files/1.

Run SAT tests:
swipl sat_solver.pl
?- run_tests.

Run single test block:
?- run_tests(cnf).

Run single test:
?- run_tests(cnf:to_cnf1).

Run SAT benchmarks:
swipl sat_benchmarks.pl
?- run_benchmarks.
