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
conjunctive(_ equiv _).
conjunctive(neg(_ notequiv _)).

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
components(X equiv Y, X imp Y, Y imp X).
components(neg(X equiv Y), neg(X imp Y), neg(Y imp X)).
components(X notequiv Y, neg(X imp Y), neg(Y imp X)).
components(neg(X notequiv Y), X imp Y, Y imp X).
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

expand(Dis, Newdis) :- singlestep(Dis, Temp), resolution(Temp, Newtemp), expand(Newtemp, Newdis).
expand(Dis, Dis).

resolution(List, Newnewlist) :- resolutionstep(List, Newlist), resolution(Newlist, Newnewlist).
resolution(List, Newnewlist) :- resolutionstep_neg(List, Newlist), resolution(Newlist, Newnewlist).

resolution(List, List).

resolutionstep([[Head|Temp]|Tail], Newlist) :- 
    member([neg(Head)], Tail), /* Finds if there is a neg version of the first value in the list of disj */
    remove([neg(Head)], Tail, List1),
    remove(Head, [Head|Temp], List2),
    append(List1, List2, Newlist).

resolutionstep_neg([[Head|Temp]|Tail], Newlist) :- 
    unary(neg(Head)), /* deal with any double complements */
    component(neg(Head), New),
    member([New], Tail), /* Finds if there is a neg version of the first value in the list of disj */
    remove([New], Tail, List1),
    remove(Head, [Head|Temp], List2),
    append(List1, List2, Newlist).

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

clauseform(X, Y) :- expand([[X]], Y).


