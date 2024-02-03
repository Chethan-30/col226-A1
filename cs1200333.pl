/* Part A: Specification */




/* membership of X in S */


/* no element is a member of the empty set */

mem(X,[]) :- fail.


/* X is a member of a set containing X, of course! */

mem(X,[X|_]) :- !.


/* if X is not the first chosen element of S, then it may be a later element */

mem(X,[_|R]) :- mem(X,R). 








/*





1. Specify the reflexive-transitive closure of a relation R over S  (R is a subset of S X S) in terms of membership */


/* The below is the membership checking for the reflexivity   */
mem((FIRSTELE,FIRSTELE),reftransclos(RELATION,GIVENSET)) :- mem(FIRSTELE,GIVENSET),!.


/* The below is the membership checking for the Normal element for the    */
mem((FIRSTELE,SECONDELE), reftransclos(RELATION,GIVENSET)) :- mem((FIRSTELE,SECONDELE), RELATION), !.


/* The below is the membership checking for the recursively formed element */

mem((FIRSTELE,THIRDELE), reftransclos(RELATION,GIVENSET)) :- mem((FIRSTELE,SECONDELE), RELATION),  mem((SECONDELE,THIRDELE), reftransclos(RELATION,GIVENSET)), !. 



/*

?- mem((1,4), reftransclos([(1,2),(2,4),(4,3),(4,5)],[1,2,3,4,5])).  --true


*/

/*
2. Specify the reflexive-symmetric-transitive closure of a relation R over S  (R is a subset of S X S) in terms of membership  */




/* The below is the membership checking for the reflexivity   */


mem((FIRSTELE,FIRSTELE),refsymtransclos(RELATION,GIVENSET)) :- mem(FIRSTELE,GIVENSET),!.

/* The below is the membership checking for the Normal element for the and the symmetry property   */

mem((FIRSTELE,SECONDELE), refsymtransclos(RELATION,GIVENSET)) :- (mem((FIRSTELE,SECONDELE), RELATION) ; mem((SECONDELE,FIRSTELE), RELATION)), !.

/* The below is the membership checking for the recursively formed element */


mem((FIRSTELE,THIRDELE), refsymtransclos(RELATION,GIVENSET)) :- mem((FIRSTELE,SECONDELE), RELATION),  mem((SECONDELE,THIRDELE), refsymtransclos(RELATION,GIVENSET)), !. 


/* reverse symmetry checking */


mem((FIRSTELE,THIRDELE), refsymtransclos(RELATION,GIVENSET)) :- mem((THIRDELE,SECONDELE), RELATION),  mem((SECONDELE,FIRSTELE), refsymtransclos(RELATION,GIVENSET)), !. 






/*

?- mem((1,4), refsymtransclos([(1,2),(2,4),(4,3),(4,5)],[1,2,3,4,5])).  --true


*/








/* Part B: Implementation of Sets as Lists with no duplicates.  */





/*  del(X,L1,L2) -- delete element X from a list L1 to obtain L2 */ 

del(X, [ ] , [ ]) :- !.

del(X, [X|R], Z) :- del(X, R, Z), !.

del(X, [Y|R], [Y|Z]) :- del(X, R, Z), !.



/*  remdups(L, L1) remove duplicates from a list L to get L1 */

remdups([ ], [ ]) :- !.

remdups([X|R], [X|Z]) :- del(X, R, L), remdups(L, Z).



/* Assuming no duplicates in S1, S2

 here is an implementation of union of S1, S2 */

unionI([ ], S2, S2) :- !.

unionI(S1, [ ], S1) :- !.

unionI([X|R], S2, [X|Z]) :- del(X, S2, S3),  unionI(R, S3, Z).

  

/* append(L1, L2, L3) -- append lis  L1 to list L2 to get list  L3 */

append( [ ], L, L).

append( [X|R], L, [X|Z]) :- append(R, L, Z).



/* mapcons(X,L1, L2) --  cons the element X to each list in L1 to get L2 */

mapcons(X, [ ], [ ]) :- !.

mapcons(X, [Y|R], [ [X|Y] | Z ]) :- mapcons(X, R, Z).



/* powerI( S, P1): Here is an implementation of powerset of S */

powerI([ ], [ [ ] ]) :- !.

powerI([X|R], P) :- powerI(R, P1),  mapcons(X, P1, P2), append(P2, P1, P).


/*
1. Check with sufficient examples  that unionI and powerI indeed implement union and power.  */

/* 

    unionI([1,2,3],[4,5,6],[1,2,3,4,5,6]) -- True.
    unionI([1,2,3],[4,5,6],[1,2,3,4,6,5]) -- False.

    powerI([1,2],[[1, 2], [1], [2], []]). -- True  .

    powerI([1,2],[[],[1,2],[1],[2]]).   -- False


*/



/*
2 .Check that union does not have duplicates.  */

checkdup([]):-fail,!.
checkdup([X|T]):-mem(X,T),!.
checkdup([X|T]):-checkdup(T).

/*
checkdup([1,2,3]). --false
checkdup([1,2,2]). --true

*/


/*
3. Assuming no duplicates in lists representing S1 and S2, write a PROLOG program  interI(S1, S2, S3) that implements intersection of two finite sets.  */



checking(X,[X|_]).
checking(X,[_|T]):- checking(X,T).

doing(X,S,Z1,Z):- checking(X,S) -> Z=[X|Z1];Z=Z1.

interl([],_,[]).
interl(_,[],[]).
interl([X|T],S,Z):- interl(T,S,Z1),doing(X,S,Z1,Z).



/*
4. Assuming no duplicates in lists representing S1 and S2, write a PROLOG program  diffI(S1, S2, S3) that implements set-difference of two finite sets.  */


diffl([],_,[]).
diffl(L,[],L).
diffl(L,[X|T],Z):- del(X,L,L1),diffl(L1,T,Z).


/*
5. Assuming no duplicates in lists representing S1 and S2, write a PROLOG program  cartesianI(S1, S2, S3) that implements cartesian of two finite sets.  */


simple([],[]).
simple(X,[X|T]):- simple([],T).
create(X,Y,[X|T]):- simple(Y,T).
createfull(X,[],[]).
createfull(X,[Y|T],[(X,Y)|Z]):-createfull(X,T,Z).
cartesianl([],_,[]).
cartesianl(_,[],[]).
cartesianl([X|T],S,Z):- cartesianl(T,S,Z1),createfull(X,S,Z2),append(Z1,Z2,Z).


/*
6. Provide sufficient test cases examples to demonstrate your implementations are correct.   */


/* Intersection  */

/*
interl([1,2,3],[3,4],[3]). --true

interl([1,2,3,4,5],[3,4],[3,4]). --true

interl([1,2,3,4,5],[3,4],[4,3]). --false




*/

/* difference */

/*
diffl([1,2,3],[2,3],[1]). --true
diffl([1,2,3],[],[1,2,3]). --true
diffl([1,2,3],[1,5],[1,2,3]). --false



*/

/* Cartesian product */



/*
cartesianl([1,2],[3],[(1,3),(2,3)]). --true

cartesianl([1,2],[3],[(1,3)]). --false

cartesianl([1,2],[],[]).  --true


*/


/*
7. Suggest a way to check that the powersets obtained from the implementation of two different valid representations of a set (elements given in different order) are equal.  */


/* subset */
subset([],L) :- !.
subset([X|R],L) :- mem(X,L), subset(R,L). 

/* equal sets */
eqset(L1, L2) :- subset(L1,L2), subset(L2,L1). 

/*
By using the above  we see the results of the powersets of the two sets A,B WHERE B is the smae as A but with order different.
Let powerI(A,P1),powerI(B,P2) now eqset(P1,P2) is true.


*/