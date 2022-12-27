:- module(dimacs_parser,[dimacs_to_prolog/2]).

dimacs_to_prolog(FilePath,ListOfClauses) :-
    parse(FilePath,ListOfDimacsClauses) ,
    to_vars(ListOfDimacsClauses,ListOfClauses).

% Convert a list of clauses parsed from the DIMACS format to a list of clauses with variables.
to_vars(ListOfLists,CNF) :-
    empty_assoc(Vars), 
    to_vars(ListOfLists,Vars,_,CNF).

to_vars([[]|T],VarsIn,VarsOut,[[]|TVars]) :- !,
    to_vars(T,VarsIn,VarsOut,TVars).
to_vars([[Num|Nums]|T],VarsIn,VarsOut,[[RAnonymousVar|NumsVars]|TVars]) :- !,
    to_pos(Num,PNum) , 
    (get_assoc(PNum, VarsIn, AnonymousVar)
     -> VarsT = VarsIn
     ;  AnonymousVar = _ , put_assoc(PNum, VarsIn, AnonymousVar, VarsT)),
    to_vars(Nums,VarsT,VarsT2,NumsVars),
    to_vars(T,VarsT2,VarsOut,TVars) , 
    anonymous_var(Num,AnonymousVar,RAnonymousVar).
to_vars([],Vars,Vars,[]).
to_vars([Num|T],VarsIn,VarsOut,[RAnonymousVar|TVars]) :-
    to_pos(Num,PNum) , 
    (get_assoc(PNum, VarsIn, AnonymousVar)
     -> VarsT = VarsIn
     ;  AnonymousVar = _ , put_assoc(PNum, VarsIn, AnonymousVar, VarsT)),
    to_vars(T,VarsT,VarsOut,TVars) , 
    anonymous_var(Num,AnonymousVar,RAnonymousVar).

anonymous_var(Number,Var,Var) :- Number > 0.
anonymous_var(Number,Var,not(Var)) :- Number < 0.

to_pos(Number,NNumber) :- NNumber is abs(Number).

% Parse a file in the DIMACS format to a Prolog list of lists.
parse(FilePath,ListOfClauses) :-
    phrase_from_file(dimacs_to_prolog(ListOfClauses),FilePath).

dimacs_to_prolog([]) --> ``.
dimacs_to_prolog(ListOfClauses) -->
    ws , `\n` , dimacs_to_prolog(ListOfClauses).
dimacs_to_prolog([Clause|ListOfClauses]) -->
    clause(Clause) , `\n` ,
    dimacs_to_prolog(ListOfClauses).
dimacs_to_prolog(ListOfClauses) -->
    skip , ws , `\n` , dimacs_to_prolog(ListOfClauses).

clause([]) --> ``.
clause([]) -->
    ` ` , ws , number(D) , ws , {D == 0}.
clause([D|ListOfLiterals]) -->
    number(D) , ` ` , ws , {D \= 0} ,
    clause(ListOfLiterals).
clause([D|ListOfLiterals]) -->
    ws , number(D) , ws , {D \= 0} ,
    clause(ListOfLiterals).

skip --> skip_symbol , skip.
skip --> number(_) , skip.
skip --> ``.
skip --> ws , skip.

ws --> ` ` , ws.
ws --> ``.

number(N) --> `-` , ! , number(PosN) , {N is PosN * -1}.
number(N) --> digit(D1) , digit(D2) , digit(D3) , {N is D1*100+D2*10+D3}.
number(N) --> digit(D1) , digit(D2) , {N is D1*10+D2}.
number(N) --> digit(N).

digit(0) --> `0`.
digit(1) --> `1`.
digit(2) --> `2`.
digit(3) --> `3`.
digit(4) --> `4`.
digit(5) --> `5`.
digit(6) --> `6`.
digit(7) --> `7`.
digit(8) --> `8`.
digit(9) --> `9`.

skip_symbol --> `a` ; `A`.
skip_symbol --> `b` ; `B`.
skip_symbol --> `c` ; `C`.
skip_symbol --> `d` ; `D`.
skip_symbol --> `e` ; `E`.
skip_symbol --> `f` ; `F`.
skip_symbol --> `g` ; `G`.
skip_symbol --> `h` ; `H`.
skip_symbol --> `i` ; `I`.
skip_symbol --> `j` ; `J`.
skip_symbol --> `k` ; `K`.
skip_symbol --> `l` ; `L`.
skip_symbol --> `m` ; `M`.
skip_symbol --> `n` ; `N`.
skip_symbol --> `o` ; `O`.
skip_symbol --> `p` ; `P`.
skip_symbol --> `q` ; `Q`.
skip_symbol --> `r` ; `R`.
skip_symbol --> `s` ; `S`.
skip_symbol --> `t` ; `T`.
skip_symbol --> `u` ; `U`.
skip_symbol --> `v` ; `V`.
skip_symbol --> `w` ; `W`.
skip_symbol --> `x` ; `X`.
skip_symbol --> `y` ; `Y`.
skip_symbol --> `z` ; `Z`.
skip_symbol --> `?`.
skip_symbol --> `.`.
skip_symbol --> `,`.
skip_symbol --> `:`.
skip_symbol --> `-`.
skip_symbol --> `+`.
skip_symbol --> `'`.
skip_symbol --> `@`.
skip_symbol --> `[`.
skip_symbol --> `]`.
skip_symbol --> `{`.
skip_symbol --> `}`.
skip_symbol --> `(`.
skip_symbol --> `)`.
skip_symbol --> `=`.
skip_symbol --> `%`.
