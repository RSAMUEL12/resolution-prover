/* Dual Clause Form Program */

?-op(140, fy, neg).
?-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, 
               notimp, notrevimp, equiv, notequiv]).

/*member(Item, List :- Item ocurs in List */

member(X, [X | _]).
member(X, [_ | Tail]) :- member(X, Tail).

/* remove(Item, List, Newlist) :-
 * Newlist is the result of removing all occurrences of
 * Item from List
 */

remove(X, [ ], [ ]).
remove(X, [X | Tail], Newtail) :- remove(X, Tail , Newtail).
remove(X, [Head | Tail], [Head | Newtail]) :- remove(X, Tail, Newtail).

/* conjunction(X) :- X is an alpha formula.
 */

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

/* disjunctive(X) :- X is a beta formula. */

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).
disjunctive(_ notequiv _).
disjunctive(neg(_ equiv _)).
disjunctive(_ equiv _).
disjunctive(neg(_ notequiv _)).

/* unary(X) :- X is a double negation or a negated constant. */

unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z) :- Y and Z are the components of the formula X, as defined in the alpha
 * and beta table */

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).
/* New equiv and notequiv components */
components(X equiv Y, neg X and neg Y, X and Y).
components(neg(X equiv Y), neg X and Y, X and neg Y).
components(X notequiv Y, neg X and Y, X and neg Y).
components(neg(X notequiv Y), neg X and neg Y, X and Y).
/*
components(X equiv Y, neg X and neg Y , X or Y).
components(neg(X equiv Y), neg X and Y, X and neg Y).
components(X notequiv Y, neg X and Y, X and neg Y). */

/* component(X, Y) :- Y is the component of the unary formula X */

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* singlestep(Old, New) :- New is the result of applying a single step of the expansion
 * process to Old, which is a generalized disjunction of generalised conjunctions. */

singlestep([Conjunction | Rest], New) :- member(Formula, Conjunction), unary(Formula),
    component(Formula, Newformula), 
    remove(Formula, Conjunction, Temporary),
    Newconjunction = [Newformula | Temporary], 
    New = [Newconjunction | Rest].

singlestep([Conjunction | Rest], New) :- 
    member(Beta, Conjunction), 
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo), 
    remove(Beta, Conjunction, Temporary),
    Newcon = [Betaone, Betatwo | Temporary], 
    New = [Newcon | Rest].

singlestep([Conjunction | Rest], New) :- 
    member(Alpha, Conjunction), 
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo), 
    remove(Alpha, Conjunction, Temporary), 
    Newconone = [Alphaone | Temporary],
    Newcontwo = [Alphatwo | Temporary], 
    New = [Newconone, Newcontwo | Rest].

singlestep([Conjunction|Rest], [Conjunction|Newrest]) :- 
    singlestep(Rest, Newrest).

expand_and_close(Tableau) :-
    singlestep(Tableau, Newtableau),
    !,
    expand_and_close(Newtableau).

expand_and_close(Tableau) :- 
    writeln(Tableau), 
    deleteTrue(Tableau, Newtableau), 
    writeln(Newtableau),
    resolution(Newtableau, Final),
    isEmpty(Final).
    
/*closed(Resolution) :- every branch of Tableau contains a contradiction */

isEmpty(List) :- member([], List).

checkEmptyList(List, []) :- member([], List).
checkEmptyList(List, List).

deleteTrue(List, Final) :-
    member(Sublist, List),
    member(Var, Sublist),
    (unary(neg Var) -> component(neg Var, Compliment); Compliment = neg Var),
    member(Compliment, Sublist),
    remove(Compliment, Sublist, Newsub1),
    remove(Var, Newsub1, Newsub2),
    remove(Sublist, List, Newlist),
    append([Newsub2], Newlist, Result),
    removeEmpty(Result, Newresult),
    deleteTrue(Newresult, Final).
deleteTrue(List, List).

removeEmpty(List, Newlist) :- member([], List), remove([], List, Newlist).
removeEmpty(List, List).

/* 
Iterates through each value to try all combinations to make an empty list

member(X, [[a, neg b],[neg b],[a,neg a,b]]),
member(Y, X),
member(Z, [[a,b],[neg b],[a,neg a,b]]),
not(Z = X),
member(neg Y, Z). 
*/


/* test(X) :- create a complete tableau expansion for neg X and see if it is closed. */

/* 
expand_and_close(Tableau) :- some expansion of Tableaus closes

expand_and_close(Tableau) :- closed(Tableau).
expand_and_close(Tableau) :-
    singlestep(Tableau, Newtableau),
    !,
    expand_and_close(Newtableau).
*/

/* Create tableau expansion for neg X, if closed, we have a proof, otherwise no. */
/*
test(X) :- 
    if_then_else(expand_and_close([[neg X]]), yes, no) */

resolution(Conjunction, Resolvent) :- resolutionstep(Conjunction, Newcon), resolution(Newcon, Resolvent).
resolution(Conjunction, Conjunction).
resolution([], []).

resolutionstep([Head1 | Tail], Newresult) :-
    member(X, Head1),
    member(Y, Tail),
    (unary(neg X) -> component(neg X, A); A = neg X),
    member(A, Y),
    remove(X, Head1, List1),
    remove(A, Y, List2), /* removes the complement of X from the element in Tail*/
    remove(Y, Tail, Newtail), /* Remove the subset Y where neg X is */
    append(List1, List2, Newlist),
    Result = [Newlist | Newtail],
    checkEmptyList(Result, Newresult). /* If an empty clause is present, then it is closed.*/ 

/*
Need to remove all occurrences of X in one list, and neg(X) in the other list,
If X is present in one and neg(X) in the other.
Call member?

After singlestep, check if in one list there is a formula X and in another list neg(X) is present
If so, call remove to remove neg(X) and X, and return a new list with all the values of the 
two lists without X and neg(X)

remove(X, [ ], [ ]).
remove(X, [neg(X) | Tail], Newtail) :- remove(neg(X), Tail , Newtail).
remove(X, [Head | Tail], [Head | Newtail]) :- remove(X, Tail, Newtail).

resolution(A, B) :- resolutionstep(A, X), resolution(X, B).
resolution(A, A).*/

test(X) :- 
    if_then_else(expand_and_close([[neg X]]), yes, no).

if_then_else(P, Q, R) :- P, !, Q.
if_then_else(P, Q, R) :- R.

yes :- write("YES, Resolution theorem").
no :- write("NO, not a resolution theorem").

