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

expand_and_close(Tableau) :- closed(Tableau).
expand_and_close(Tableau) :-
    singlestep(Tableau, Newtableau),
    !,
    expand_and_close(Newtableau).

/*closed(Resolution) :- every branch of Tableau contains a contradiction */

closed([Head1 | Rest]) :-
    member(X, Head1),
    member(Y, Rest),
    member(neg X, Y),
    remove(X, Head1, List1),
    remove(neg X, Y, List2), 
    remove(Y, Rest, Newrest), /* Remove the subset Y where neg X is */
    append(List1, List2, Newlist),
    append(Newlist, Newrest, Result),
    closed(Result).

/* Deal with double complement */
closed([Head1 | Rest]) :-
    member(X, Head1),
    member(Y, Rest),
    unary(neg X),
    component(neg X, NewX),
    member(NewX, Y),
    remove(X, Head1, List1),
    remove(NewX, Y, List2), 
    remove(Y, Rest, Newrest), /* Remove the subset Y where neg X is */
    append(List1, List2, Newlist),
    append(Newlist, Newrest, Result),
    closed(Result).

closed([]).

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

resolution(List, Final) :- resolutionstep(List, [[H | T] | Tail]), resolution([T | Tail], Result), attachHead(H, Result, Final).
resolution(List, List).

resolutionstep([[H | T], Head2 | Tail], Result) :-
    member(neg(H), Head2),
    remove(neg(H), Head2, List1),
    remove(H, [H | T], List2),
    append(List1, List2, Newlist),
    Result = [Newlist | Tail].

/*resolutionstep([[H | T], Head2 | Tail], []).*/

/* Dealing with double complements */
resolutionstep([[H | T], Head2 | Tail], Result) :-
    unary(neg(H)),
    component(neg(H), NewH),
    member(NewH, Head2),
    remove(NewH, Head2, List1),
    remove(H, [H | T], List2),
    append(List1, List2, Newlist),
    Result = [Newlist | Tail].

resolutionstep([Head1, Head2, Head3 | Tail], Newlist) :-
    resolutionstep([Head1, Head3 | Tail], List2), !,
    append(List2, [Head2], Newlist).

resolutionstep([Head1, Head2 | [ ]], [Head1, Head2 | [ ]]).

/* Adding back the first element of the list to the head */
attachHead(H, [Head | Tail], Newlist) :-
    Newhead = [H | Head],
    append([Newhead], Tail, Newlist).

attachHead(H, [Head], [Newhead]) :-
    Newhead = [[H] | Head].

attachHead(H, [[ ]], [[H]]).

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

yes :- write("Resolution theorem").
no :- write("not a resolution theorem").

