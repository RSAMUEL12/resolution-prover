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

removeAll(X, [ ], [ ]) :- !.
removeAll(X, [X | Tail], Newtail) :- !, remove(X, Tail , Newtail).
removeAll(X, [Head | Tail], [Head | Newtail]) :- !, remove(X, Tail, Newtail).

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

expand_and_close(Tableau, Final) :-
    singlestep(Tableau, Newtableau),
    expand_and_close(Newtableau, Final).

expand_and_close(List, List).

resolution(Proof) :- expand_and_close([[neg Proof]], Conj), !, closed(Conj).

/*closed(Resolution) :- every branch of Tableau contains a contradiction */

resolutionstep(Proof) :-
    /* Finding 2 disjunctions and an element X in one, neg X in the other */
    member(Disj1, Proof),
    member(X, Disj1),
    member(Disj2, Proof),
    not(Disj1 = Disj2),
    member(neg X, Disj2),
    !,
    /* Remove the X and neg X */
    /* Remove the two disjunctions from the Conj */
    /* Add the new resolvent to the Conj */
    remove(X, Disj1, Newdisj1),
    remove(neg X, Disj2, Newdisj2),
    append(Newdisj1, Newdisj2, Resolvent),
    remove(Disj1, Proof, Newproof),
    remove(Disj2, Newproof, Newproof),
    !,
    Final = [Resolvent | Proof],
    checkEmptyList(Final, Empty),
    closed(Empty).

/* Deal with double complement */
resolutionstep(Proof) :-
    /* Finding 2 disjunctions and an element X in one, neg X in the other */
    member(Disj1, Proof),
    member(X, Disj1),
    member(Disj2, Proof),
    not(Disj1 = Disj2),
    component(neg X, A),
    member(A, Disj2),
    !,
    /* Remove the X and neg X */
    /* Remove the two disjunctions from the Conj */
    /* Add the new resolvent to the Conj */
    remove(X, Disj1, Newdisj1),
    remove(A, Disj2, Newdisj2),
    append(Newdisj1, Newdisj2, Resolvent),
    remove(Disj1, Proof, Newproof),
    remove(Disj2, Newproof, Newproof),
    !,
    Final = [Resolvent | Proof],
    checkEmptyList(Final, Empty),
    closed(Empty).

resolutionstep([]).
    

closed([Head1 | Rest]) :-
    member(X, Head1),
    member(Y, Rest),
    member(neg X, Y),
    !,
    remove(X, Head1, List1),
    remove(neg X, Y, List2), 
    remove(Y, Rest, Newrest), /* Remove the subset Y where neg X is */
    !,
    append(List1, List2, Newlist),
    Result = [Newlist | Newrest],
    checkEmptyList(Result, Newresult),
    (closed(Newresult); closed(Rest)),
    !.

/* Deal with double complement */
closed([Head1 | Rest]) :-
    member(X, Head1),
    member(Y, Rest),
    unary(neg X),
    component(neg X, NewX),
    member(NewX, Y),
    !,
    remove(X, Head1, List1),
    remove(NewX, Y, List2), 
    remove(Y, Rest, Newrest), /* Remove the subset Y where neg X is */
    !,
    append(List1, List2, Newlist),
    Result = [Newlist | Newrest],
    checkEmptyList(Result, Newresult),
    (closed(Newresult); closed(Rest)),
    !.

closed([]).

checkEmptyList(List, []) :- member([], List).
checkEmptyList(List, List).

/* 
Iterates through each value to try all combinations to make an empty list

member(X, [[a, neg b],[neg b],[a,neg a,b]]),
member(Y, X),
member(Z, [[a,b],[neg b],[a,neg a,b]]),
not(Z = X),
member(neg Y, Z). 
*/

test(X) :- 
    if_then_else(expand_and_close([[neg X]], Result), yes, no).

if_then_else(P, Q, R) :- P, !, Q.
if_then_else(P, Q, R) :- R.

yes :- write("Resolution theorem").
no :- write("not a resolution theorem").

