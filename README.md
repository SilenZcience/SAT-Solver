# SAT-Solver

A simple SAT-Solver written in Prolog as part of an university project at Heinrich-Heine-University (Introduction to Logic Programming). 

## Description

The program transforms any propositional logic formula into conjunctive normalform and solves them afterwards using the DPLL algorithm.

The input is a syntax tree that is built recursively from the following Prolog terms:
* literals *lit(...)*
    - the constants **lit(true)** and **lit(false)**
    - Prolog variables such as **lit(X)**
* the equivalence *ρ ⇔ ϕ*, in Prolog **equivalence(ρ,ϕ)**
* the implication *ρ ⇒ ϕ*, in Prolog **implies(ρ,ϕ)**
* the conjunction *ρ ∧ ϕ*, in Prolog **and(ρ,ϕ)**
* the disjunction *ρ ∨ ϕ*, in Prolog **or(ρ,ϕ)**
* the negation *¬ρ*, in Prolog **not(ρ)**
* **exactly_one_pos(ListOfVars)**: exactly one variable in **ListOfVars** is true
* **min_one_pos(ListOfVars)**: at least one variable in **ListOfVars** has to be true

You can solve any formula using the following two predicates:
- to_cnf(+Formula, -CNF).
- solve(+CNF).

## Getting Started

### Dependencies

* Made- and Executable with [SWI-Prolog](https://www.swi-prolog.org/Download.html).

### Installing

Download the stand-alone file [sat_solver.pl](https://raw.githubusercontent.com/SilenZcience/SAT-Solver/main/sat_solver.pl).
<!-- ```console
git clone git@github.com:SilenZcience/SAT-Solver.git
``` -->

### Executing program

Open the `sat_solver.pl` in Prolog:
```console
?- ['<PATH_TO_FILE>'].
```
Execute your queries:

`True ∧ X` :
```console
?- Formula = and(lit(true), lit(X)), to_cnf(Formula, CNF), solve(CNF).
Formula = and(lit(true), lit(true)),
X = true,
CNF = [[true], [true]].
```
`min_one_pos(X, Y) ∧ (X ⇔ Y)` :
```console
?- to_cnf(and(min_one_pos([lit(X),lit(Y)]),equivalence(lit(X),lit(Y))), CNF), solve(CNF).
X = Y, Y = true,
CNF = [[true, true], [not(true), true], [not(true), true]] 
```
`¬X ∧ Y ∧ (X ⇒ Y)` :
```console
?- to_cnf(and(not(lit(X)),and(lit(Y),implies(lit(X),lit(Y)))), CNF), solve(CNF).
X = false,
Y = true,
CNF = [[not(false)], [true], [not(false), true]].
```

## Authors

[SilenZcience](https://github.com/SilenZcience) <br>
[gulmariyam](https://github.com/gulmariyam)
