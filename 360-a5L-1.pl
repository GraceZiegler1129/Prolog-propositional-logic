% CISC 360 a5L, Fall 2020

% Q1:
% Add your student ID:
student_id( 20010846 ).

% BE SURE TO ADD YOUR STUDENT ID BETWEEN THE (  ) ABOVE.

/*
Q2: Truth Tables

In order to build a truth table for a formula, there are 4 steps:

1) Traverse the formula to find all atomic propositions (propositional variables).

2) Assign all possible combinations of True and False
   to the set of atomic propositions in the formula.

3) Evaluate the formula for each truth value assignment obtained in (2).

4) Use the results of (1-3) to build the table.

In this question, you will implement steps (1-3).
*/

% In this simplified version of classical propositional logic,
% we have the following possible Formulas:
%
% top                        % truth
% bot                        % falsehood
% v(PropVar)                 % propositional variable
% and(Formula, Formula)      % conjunction
% or(Formula, Formula)       % disjunction
% implies(Formula, Formula)  % implication

% Some example constants:
% v(a)
% v(b)
% v(c)
% v(d)
% v(e)
% v(f)
% v(g)

/* Some example formulas you can use to test your functions

 These are given in a slightly weird way: formula1(Phi) is true iff
 Phi is equal to formula number 1.
 
 We can use it in a query like this:

   ?- formula1(Phi), prove([], Phi).

 Because the predicate formula1 is defined solely by the fact below,
 Prolog will find the solution Phi = implies( and( v(a), v(b)), v(d)),
 and the effect will be the same as if we had typed the formula directly
 as the second argument to 'prove'.

   ?- prove([], implies( and( v(a), v(b)), v(d))).
*/
formula1( implies( and( v(a), v(b)), v(d))).
formula2( implies( bot, (and( v(a), v(b)))) ).
formula3( implies( and( v(a), v(b)), top) ).
formula4( and( implies(v(a), and(v(b), v(h))), and(v(e), v(f))) ).
formula5( and( v(a), v(b)) ).
formula6( implies( v(a), v(b) )).

/*
  A valuation is a list of assign/2s,
    corresponding to a truth value (i.e. true or false)
    for each variable in a formula.
  Example:
 
    [assign(a, true), assign(b, false)]   assigns true to v(a) and false to v(b)

  A TruthTable is an enumeration of all combinations of truth value assignments
    for a given formula, paired with the corresponding evaluation of that formula.
  Example:
 
     truth_table( [truth([assign(a, true)], true)],
                  [truth([assign(a, false)], false)])
  
  is a truth table for the formula v(a).
*/

nub([],       []).
nub([X | Xs], Ys) :- member(X, Xs), nub(Xs, Ys).
nub([X | Xs], [X | Ys]) :- \+ member(X, Xs), nub(Xs, Ys).

/* Q2a: getVars:
  Traverse a formula and build a list of all propositional variables
  in the formula, without duplicates.

  Example:  getVars(and(v(a), v(b)), [a, b]) should be true.

  Hint: Consider using 'append' and 'nub' in the clauses
  for 'and' and 'implies'.
*/
getVars( top, []).
getVars( bot, []).
getVars( v(V), [V]).
getVars( and(Q1, Q2), Vs) :-
    getVars(Q1, V1),
    getVars(Q2, V2),
    append(V1, V2, V3),
    nub(V3, Vs).

getVars( or(Q1, Q2), Vs) :-
    getVars(Q1, Vs),
    getVars(Q2, Vs).

getVars( implies(Q1, Q2), Vs) :-
    getVars(Q1, V1),
    getVars(Q2, V2),
    append(V1, V2, V3),
    nub(V3, Vs).

/*
  Q2b: oneValuation
*/
is_bool(true).     % a possibly useful predicate: is_bool is true iff
is_bool(false).    %  its argument is a Boolean ('true' or 'false').

oneValuation([], []).
oneValuation([V | Vs], [assign(V, B) | Vs_Valuation]) :-
    is_bool(B),
    oneValuation(Vs, Vs_Valuation).

/*
  getValuations:
   Build a list of all possible truth valuations for a set of constants
*/
getValuations([], [[]]).
getValuations([V | Vs], Result) :-
  getValuations(Vs, Valuations),
  addToFront( assign(V, true),  Valuations, True_Valuations),
  addToFront( assign(V, false), Valuations, False_Valuations),
  append( True_Valuations, False_Valuations, Result).

/*
  addToFront x xss
  Add the element x to the start of each list in xss.
  Example:
    addToFront( 1, [[2,3], [], [4,5,6]],  [[1,2,3], [1], [1,4,5,6]]).
*/
addToFront( _, [], []).
addToFront( X, [Xs | Xss], [[X | Xs] | RecursiveResult]) :-
    addToFront( X, Xss, RecursiveResult).


/*
  Q2c: evalF (Formula, Valuation, Result)
  Evaluate Formula under Valuation, returning the boolean Result
*/
evalF( top,         _,    true).
evalF( bot,         _,    false).
evalF( v(V),        Valu, Result) :- member(assign(V, Result), Valu).

evalF( and(Q1, Q2), Valu, true)  :- evalF( Q1, Valu, true),
                                    evalF( Q2, Valu, true).
evalF( and(Q1, _),  Valu, false) :- evalF( Q1, Valu, false).
evalF( and(_, Q2),  Valu, false) :- evalF( Q2, Valu, false).


evalF( implies(Q1, Q2), Valu, true) :- evalF(Q1, Valu, false), evalF(Q2, Valu, true).
evalF( or(Q1, Q2), Valu, true) :- evalF(Q1, Valu, _), evalF(Q2, Valu, _).



/*
  buildTable:
   Build a truth table for a given formula.
   You can use this function to help check your definitions
   of getVars, getValuations and evalF.
*/
buildTable( Q, truth_table( TruthTable)) :-
  getVars(Q, Consts),
  getValuations( Consts, Valuations),
  format('formula: ~p ~n', Q), 
  zip_eval( Q, Valuations, TruthTable).

format_valuation( [], '').
format_valuation( [assign(V, Bool) | Valu], ConcatenatedString) :-
  concat( V,  ' = ', S1),
  concat( S1, Bool,  S2),
  concat( S2, ', ',  S3),
  format_valuation( Valu, String),
  concat(S3, String, ConcatenatedString).

zip_eval( _, [], [] ).
zip_eval( Q, [Valuation | Rest],
              [truth(Valuation, Bool) | Result] ) :-
    evalF(Q, Valuation, Bool),
    format_valuation( Valuation, String),
    format('~p:   ~p ~n', [String, Bool]),
    zip_eval( Q, Rest, Result).


/*
Q3: Tiny Theorem Prover
*/

/*
  append3( Ctx1, Formula, Ctx2, Ctx)
 
  append3 takes:
   a list of formulas Ctx1
   an element Formula
   a list of formulas Ctx2
  and "returns" the result of appending all of them,
  similar to Haskell   Ctx = Ctx1 ++ (formula : Ctx2)
                  or   Ctx = Ctx1 ++ [formula] ++ Ctx2
*/
append3( [], Formula, Ctx2, [Formula | Ctx2]).

append3( [X | Xs], Formula, Ctx2, [X | Result]) :-
  append3( Xs, Formula, Ctx2, Result).

/*
  We will use append3 "backwards":
  instead of taking concrete Ctx1, Formula, Ctx2
  provided by the user, we take a concrete *result* Ctx
  and use append3 to "split up" the Ctx.
*/

% prove(Ctx, P):
%   true if, assuming everything in Ctx is true,
%    the formula p is true according to the rules given in a3.pdf.

/*
  This is the cool part:
  *each rule in the figure from a3L becomes a Prolog clause*.
  There is no "problem solving" where someone (like the instructor)
  figures out an algorithm that first "decomposes" the context,
  then tries the -Right rules.
  
  (That also requires figuring out how to decompose the context, using an accumulator.)

  In Prolog, we can write a clause for each logical rule, and it "just works".
*/

% rule 'UseAssumption'
prove( Ctx, P) :- member( P, Ctx).

% rule 'TOP-Right'
prove( _,   top).

/*
Q3a:
  Write Prolog clauses that correspond to the rules
  BOT-Left,
  AND-Right, and
  IMPLIES-Right.
*/

% rule 'BOT-Left'
% CONCLUSION:  Ctx1 ++ [bot] ++ Ctx2 |- Q
prove(Ctx, _) :- 
    append3(Ctx1, bot, Ctx2, Ctx),
    append(Ctx1, [bot | Ctx2], CtxB),
    prove(CtxB, bot).


% rule 'AND-Right'
% CONCLUSION:  Ctx |- and(Q1, Q2)
prove(Ctx, and(Q1, Q2)) :- 
    prove(Ctx, Q1),
    prove(Ctx, Q2).

% rule 'IMPLIES-Right'
% CONCLUSION:  Ctx |- implies(P, Q)
prove(Ctx, implies(P,Q)) :- 
    prove([P | Ctx], Q).

% rule 'AND-Left'
% CONCLUSION:  Ctx1 ++ [and(P1, P2)] ++ Ctx2 |- Q
prove(Ctx, Q) :-
  append3( Ctx1, and(P1, P2), Ctx2, Ctx),
  append( Ctx1, [P1 | [P2 | Ctx2]], CtxP12),  % CtxP12 = Ctx1 ++ [P1, P2] ++ Ctx2
  prove( CtxP12, Q).                          % CtxP12 |- Q

/*
  Q3b: IMPLIES-Left
*/
% rule 'IMPLIES-Left'
% CONCLUSION:  Ctx1 ++ [implies(P1, P2)] ++ Ctx2 |- Q
prove(Ctx, Q) :-
    append3( Ctx1, implies(P1, P2), Ctx2, Ctx),
    append(Ctx1, Ctx2, CtxP),
    prove(CtxP, P1),
    append(Ctx1, [P2 | Ctx2], CtxP2),
    prove(CtxP2, Q).

/*
  ?- prove([v(a), bot, v(b)], v(c)).
  true
  
  ?- prove([implies(v(b), v(h))], implies(v(b), v(h))).
  true
  ?- prove([implies(v(b), v(d))], implies(and(v(b), v(b)), v(d))).
  true
  ?- prove([implies(and(v(b), v(e)), v(d))], implies(v(b), v(h))).
  false
  ?- prove([and(and(v(a), v(b)), and(v(d), (v(e))))], v(d)).
  true

  ?- prove([v(a)], or(v(a), v(b))).
  true
  ?- prove([v(b)], or(v(a), v(b))).
  true
  ?- prove([or(v(a), v(b))], or(v(b), v(a))).
  true
  ?- prove([v(e), or(v(a), v(b)), v(e)], or(v(b), v(a))).
  true
*/

/*
  Q4:
  Add clauses for 'or'.
*/

% rules 'OR-Right1', 'OR-Right2'
% You can write this as two rules, or write ; if you like.
% CONCLUSION:  Ctx |- or(P1, P2)
prove(Ctx, or(P1, _)) :- 
    prove(Ctx, P1).

prove(Ctx, or(_, P2)) :- 
    prove(Ctx, P2).

% rule 'OR-Left'
% CONCLUSION: Ctx1 ++ [or(P1, P2)] ++ Ctx2 |- Q
prove(Ctx, Q) :- 
  append3(Ctx1, or(P1, P2), Ctx2, Ctx),
  append(Ctx1, [P1 | Ctx2], CtxP1),
  prove(CtxP1, Q),
  append(Ctx1, [P2 | Ctx2], CtxP2),
  prove(CtxP2, Q).  



/*
   Bonus:
   
   Develop rules for 'not', then implement them.  See the PDF file.
   (Copy this file to a5Lbonus.pl first!)
*/
