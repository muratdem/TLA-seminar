------------ MODULE beans ------------------
EXTENDS Integers
CONSTANTS W, B
ASSUME /\ W \in 0..100
       /\ B \in 0..100
       /\ W+B > 0

VARIABLES w,b

Init == /\ w = W
        /\ b = B

WW ==   /\ w > 1  \* same color and white
        /\ w' = w-1 /\ UNCHANGED b

BB ==   /\ b > 1  \* same color and black
        /\ b' = b - 2 
        /\ w' = w + 1  

WB ==   /\ w > 0 /\ b > 0  \* different color
        /\ w' = w - 1 /\ UNCHANGED b

Next == \/ WW
        \/ BB
        \/ WB
        \/ UNCHANGED w /\ UNCHANGED b \* termination

vars == <<w,b>>   
Spec == Init /\ [] [Next]_vars
             /\ WF_vars(Next) \* Weak Fairness

TypeOK ==   w+b > 0

Termination == <> (w+b < 2)

DecreasingN == [] [w'+b'< w+b]_vars

EvenB == [] [b%2=0 => b'%2=0]_vars

OddB == [] [b%2=1 => b'%2=1]_vars
\* EvenW == [] [w%2=0 => w'%2=0]_vars  \* not an invariant

============================================
Problem description:

Consider a can of coffee beans.

Each bean is either white or black.  The can is initially
nonempty (w+b>0).  Now consider the following program: 

Choose two beans from the can;

- if they are the same color, toss them out and put in a white bean

- if they are different colors, toss them out and put in a black bean

This rule is repeated.
