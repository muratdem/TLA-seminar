------------ MODULE beansAlg3 ------------------
EXTENDS Integers


(* --fair algorithm beansAlg3 {
   variable r \in 1..5, g \in 1..5, b \in 1..5;

define {
TypeOK == /\ r \in 0..200
          /\ g \in 0..200
          /\ b \in 0..200

FinalCan == r+g+b >= 0          

Termination == <> (r+g+b =< 1)

DecreasingN == [] [r'+g'+b'< r+g+b]_<<r,g,b>>

DifferentOneSurvives == r%2=g%2 /\ b%2#r%2 ~> r=0 /\ g=0 /\ b=1 

ModalityPersists == [] [/\ r%2=g%2 /\ b%2#r%2  =>  r'%2=g'%2 /\ b'%2#r'%2
                        /\ r%2=b%2 /\ g%2#r%2  =>  r'%2=b'%2 /\ g'%2#r'%2
                        /\ b%2=g%2 /\ r%2#b%2  =>  b'%2=g'%2 /\ r'%2#b'%2
                        ]_<<r,g,b>>
}

   { S: while (TRUE)
     { either 
        {await (r>1); \* same color and red
RR:        r:=r-2; 
          };
       or
         {await (b>1);  \* same color and blue
BB:        b:=b-2; 
          };
       or   
         {await (g>1);  \* same color and green
GG:        g:=g-2; 
          };
       or
         {await (r>0 /\ b>0);  \* red and blue
RB:         r:= r-1; b:=b-1; g:=g+1;
         };            
       or
        {await (r>0 /\ g>0); \* red and green
RG:         r:= r-1; g:=g-1; b:=b+1;
         };            
       or
         {await (b>0 /\ g>0); \* blue and green
BG:         b:= b-1; g:=g-1; r:=r+1;
         };            
      }\* end while
    }
   }\* end alg
*)

\* BEGIN TRANSLATION (chksum(pcal) = "7c28162a" /\ chksum(tla) = "25608c07")
VARIABLES r, g, b, pc

(* define statement *)
TypeOK == /\ r \in 0..200
          /\ g \in 0..200
          /\ b \in 0..200

FinalCan == r+g+b >= 0

Termination == <> (r+g+b =< 1)

DecreasingN == [] [r'+g'+b'< r+g+b]_<<r,g,b>>

DifferentOneSurvives == r%2=g%2 /\ b%2#r%2 ~> r=0 /\ g=0 /\ b=1

ModalityPersists == [] [/\ r%2=g%2 /\ b%2#r%2  =>  r'%2=g'%2 /\ b'%2#r'%2
                        /\ r%2=b%2 /\ g%2#r%2  =>  r'%2=b'%2 /\ g'%2#r'%2
                        /\ b%2=g%2 /\ r%2#b%2  =>  b'%2=g'%2 /\ r'%2#b'%2
                        ]_<<r,g,b>>


vars == << r, g, b, pc >>

Init == (* Global variables *)
        /\ r \in 1..5
        /\ g \in 1..5
        /\ b \in 1..5
        /\ pc = "S"

S == /\ pc = "S"
     /\ \/ /\ (r>1)
           /\ pc' = "RR"
        \/ /\ (b>1)
           /\ pc' = "BB"
        \/ /\ (g>1)
           /\ pc' = "GG"
        \/ /\ (r>0 /\ b>0)
           /\ pc' = "RB"
        \/ /\ (r>0 /\ g>0)
           /\ pc' = "RG"
        \/ /\ (b>0 /\ g>0)
           /\ pc' = "BG"
     /\ UNCHANGED << r, g, b >>

RR == /\ pc = "RR"
      /\ r' = r-2
      /\ pc' = "S"
      /\ UNCHANGED << g, b >>

BB == /\ pc = "BB"
      /\ b' = b-2
      /\ pc' = "S"
      /\ UNCHANGED << r, g >>

GG == /\ pc = "GG"
      /\ g' = g-2
      /\ pc' = "S"
      /\ UNCHANGED << r, b >>

RB == /\ pc = "RB"
      /\ r' = r-1
      /\ b' = b-1
      /\ g' = g+1
      /\ pc' = "S"

RG == /\ pc = "RG"
      /\ r' = r-1
      /\ g' = g-1
      /\ b' = b+1
      /\ pc' = "S"

BG == /\ pc = "BG"
      /\ b' = b-1
      /\ g' = g-1
      /\ r' = r+1
      /\ pc' = "S"

Next == S \/ RR \/ BB \/ GG \/ RB \/ RG \/ BG

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION 

===========================================================

Consider a coffee can containing an arbitrary (but finite) number of beans. The beans come in 3 different colors: red, green, and blue. Now consider the following program:

Choose two beans from the can;

if they are the same color, toss them out

if they are different colors, toss them out and add a bean of the third color

Repeat.
