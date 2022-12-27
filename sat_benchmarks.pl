
:- use_module(sat_solver).
:- use_module('resources/dimacs_parser').

run_benchmarks :-
    format("Running benchmarks..~n", []),
    MaxIndex = 7,
    solve_benchmarks(1, MaxIndex, 0, Inferences),
    format("SAT benchmarks (~w files): ~w inferences.~n", [MaxIndex,Inferences]), !.

% Solve the benchmarks located in 'resources/sat_benchmarks/*.cnf' enumerated from 1 to MaxIndex.
% Measure the time without the overhead of parsing the test resources by using statistics/2.
solve_benchmarks(Index, MaxIndex, Acc, Res) :-
    Index > MaxIndex,
    !,
    Res = Acc.
solve_benchmarks(Index, MaxIndex, Acc, Inferences) :-
    atom_concat('resources/sat_benchmarks/',Index,TempPath),
    atom_concat(TempPath,'.cnf',Path),
    dimacs_to_prolog(Path, ListOfClauses), !,
    statistics(inferences, PreInferences),
    solve(ListOfClauses),
    statistics(inferences, PostInferences),
    !,
    NewAcc is Acc + (PostInferences - PreInferences),
    NewIndex is Index + 1,
    solve_benchmarks(NewIndex, MaxIndex, NewAcc, Inferences).
