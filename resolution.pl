/* Dual Clause Form Program  | CS262 Logic and Verification */

/*
Outputs from Test Data
    1. YES
    2. YES
    3. YES
    4. NO
    5. YES
    6. YES (around 20 mins to complete execution)
    7. YES
    8. NO
    9. NO
    10. YES
*/

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

/* returns CNF of Formula */
clauseform(Formula, Conjunction) :- expand_and_close([[Formula]], Conjunction).

expand_and_close(Formula, NormalForm) :-
    singlestep(Formula, Conjunction),
    !,
    expand_and_close(Conjunction, NormalForm),
    !.
expand_and_close(List, List).

resolve(Formula) :- 
    clauseform(Formula, Conjunction), !,
    writeln(Conjunction),
    sort(Conjunction, Sorted), !,
    deleteTrue(Sorted, Newcon),
    deleteDupVars(Newcon, Unique),
    /* If the empty list is present before resolution, then there is no contradiction hence not a res. theorem */
    /* Newcon can be empty if deleteTrue causes Unique = [[]] meaning that the CNF is always true */
    (not(isEmpty(Unique)) ; fail),
    checkFalse(Unique, List), /*checks if a clause contains only false, then it can never be true*/
    removeFalse(List, Newlist),
    !,
    resolution(Newlist, Final),
    isEmpty(Final).
    
/*closed(Resolution) :- every branch of Tableau contains a contradiction */

isEmpty([]).

/* Checks to see if the empty list is present */
/* If so, then the CNF of formula X is closed */
checkEmptyList(List, []) :- member([], List).
checkEmptyList(List, List).

/* Checks to see if there is a clause with solely false as a variable */
/* It will return the empty list because then the formula X given by the user cannot be true */
checkFalse(List, []) :- member([false], List).
checkFalse(List, List).

/* Deletes clauses that evaluate to true e.g. [a, neg a] is removed from the CNF*/
deleteTrue(List, Final) :-
    member(Sublist, List),
    member(Var, Sublist),
    (unary(neg Var) -> component(neg Var, Compliment); Compliment = neg Var),
    (member(Compliment, Sublist); member(true, Sublist)),
    remove(Sublist, List, Newlist),
    removeEmpty(Newlist, Result),
    deleteTrue(Result, Final),
    !.
deleteTrue(List, List).

/* removes any false variables each clause in List */
removeFalse(List, Newfinal) :-
    member(Sub, List),
    member(false, Sub),
    remove(false, Sub, Newsub),
    remove(Sub, List, Newlist),
    removeFalse(Newlist, Result),
    append([Newsub], Result, Final),
    removeEmpty(Final, Newfinal),
    !.
removeFalse(List, List).

/* Function to delete duplicate variables in each clause */
deleteDupVars([Head | Tail], Newresult) :-
    sort(Head, Sublist),
    deleteDupVars(Tail, Result),
    append([Sublist], Result, Newresult),
    !.
deleteDupVars(List, List).

/* removes any empty list in List */
removeEmpty(List, Newlist) :- member([], List), remove([], List, Newlist).
removeEmpty(List, List).

resolution(Conjunction, Resolvent) :- resolutionstep(Conjunction, Resolvent), !.
resolution(Conjunction, Conjunction). /* if it can't find the empty list, then it is not a resolution theorem */
resolution([], []).

resolutionstep([], []).
resolutionstep(List, Final) :-
    member(X, List), /* gets 2 sublists to find X and ¬X */
    member(Y, List),
    not(same(X, Y)), /* makes sure they are not the same */
    member(E1, X), /* finds a member in sublist 1 */
    (unary(neg E1) -> component(neg E1, A); A = neg E1), /* gets compliment of element */
    member(A, Y), /* checks if complement is in the sublist 2 */
    removeClause(E1, X, A, Y, List, Result),
    checkEmptyList(Result, Newresult),
    resolutionstep(Newresult, Final). /* If an empty clause is present, then it is closed.*/ 

/* Removes the variables X and ¬X from D1 and D2 to create the resolvent */
removeClause(X1, D1, X2, D2, Conjunction, Final) :-
    remove(X1, D1, NewD1),
    remove(X2, D2, NewD2),
    append(NewD1, NewD2, Resolvent),
    /* Now removes the disjunctions in place of Resolvent */
    removeOne(D1, Conjunction, Newcon),
    removeOne(D2, Newcon, Newnewcon),
    append([Resolvent], Newnewcon, Final),
    !.

/* removes single occurrence of an element from a list */
removeOne(_, [], []).
removeOne(Term, [Term|Tail], Tail).
removeOne(Term, [Head|Tail], [Head|Result]) :-
  removeOne(Term, Tail, Result).

/* checks if two given lists are the same */
same([], []).
same([H1|R1], [H2|R2]):-
    H1 = H2,
    same(R1, R2).

test(X) :-
    statistics(walltime, [TimeSinceStart | [TimeSinceLastCall]]),
    if_then_else(resolve(neg X), yes, no),
    statistics(walltime, [NewTimeSinceStart | [ExecutionTime]]),
    write('Execution took '), write(ExecutionTime), write(' ms.'), nl. 

if_then_else(P, Q, R) :- P, !, Q.
if_then_else(P, Q, R) :- R.

yes :- writeln("YES, Resolution theorem").
no :- writeln("NO, not a resolution theorem").

