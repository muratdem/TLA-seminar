------------ MODULE beansAlg ------------------
EXTENDS Integers
CONSTANTS W, B
ASSUME /\ W \in 0..100
       /\ B \in 0..100
       /\ W+B > 0

(* --fair algorithm beansAlg {
   variable w=W, b=B;
  {S:while (TRUE)
     { either 
      {await (w>1); \* same color and white
      	  w:=w-1;
          };
       or
     {await (b>1); \* same color and black
          b:= b-2; w:= w+1;
         };            
       or
    {await (w>0 /\ b>0); \* different color
          w:= w-1;
         };            
      }
    }
   }
*)

\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "23b9abeb")
VARIABLES w, b

vars == << w, b >>

Init == (* Global variables *)
        /\ w = W
        /\ b = B

Next == \/ /\ (w>1)
           /\ w' = w-1
           /\ b' = b
        \/ /\ (b>1)
           /\ b' = b-2
           /\ w' = w+1
        \/ /\ (w>0 /\ b>0)
           /\ w' = w-1
           /\ b' = b

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 



TypeOK ==   w+b > 0

Termination == <> (w+b < 2)

DecreasingN == [] [w'+b'< w+b]_vars

EvenB == [] [b%2=0 => b'%2=0]_vars

OddB == [] [b%2=1 => b'%2=1]_vars

\* EvenW == [] [w%2=0 => w'%2=0]_vars


========================================
Problem description:

Consider a can of coffee beans.

Each bean is either white or black.  The can is initially
nonempty (w+b>0).  Now consider the following program: 

Choose two beans from the can;

- if they are the same color, toss them out and put in a white bean

- if they are different colors, toss them out and put in a black bean


This action is repeated.
