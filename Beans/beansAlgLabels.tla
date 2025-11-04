------------ MODULE beansAlgLabels ------------------
EXTENDS Integers
CONSTANTS W, B
ASSUME /\ W \in 0..100 /\ B \in 0..100
       /\ W+B > 0

(* --fair algorithm beansAlg {
   variable w=W, b=B;
  {S:while (TRUE)
     { either 
       {await (w>1); \* \* same color and white
WW:     w:=w-1;};
       or
       {await (b>1); \* \* same color and black
BB:     b:= b-2; w:= w+1;};            
       or
        {await (w>0 /\ b>0); \* \* different color
WB:     w:= w-1;};            
      }
    }
  }
*)

\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "d5971503")
VARIABLES w, b, pc

vars == << w, b, pc >>

Init == (* Global variables *)
        /\ w = W
        /\ b = B
        /\ pc = "S"

S == /\ pc = "S"
     /\ \/ /\ (w>1)
           /\ pc' = "WW"
        \/ /\ (b>1)
           /\ pc' = "BB"
        \/ /\ (w>0 /\ b>0)
           /\ pc' = "WB"
     /\ UNCHANGED << w, b >>

WW == /\ pc = "WW"
      /\ w' = w-1
      /\ pc' = "S"
      /\ b' = b

BB == /\ pc = "BB"
      /\ b' = b-2
      /\ w' = w+1
      /\ pc' = "S"

WB == /\ pc = "WB"
      /\ w' = w-1
      /\ pc' = "S"
      /\ b' = b

Next == S \/ WW \/ BB \/ WB

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 


TypeOK ==   w+b > 0

Termination == <> (w+b < 1)

DecreasingN == [] [w'+b'< w+b]_<<w,b>>

EvenB == [] [b%2=0 => b'%2=0]_vars

Display == [ white |-> w,
             black |-> b,
           action |-> pc]

========================================
Consider a can of coffee beans.

Each bean is either white or black.  The can is initially
nonempty (w+b>0).  Now consider the following program: 

Choose two beans from the can;

- if they are the same color, toss them out and put in a white bean

- if they are different colors, toss them out and put in a black bean


This action is repeated.
