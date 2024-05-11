----------------------------- MODULE 2PC2withBTM ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT 
    RMMAYFAIL, TMMAYFAIL    \* Whether RM & TM may fail

(* --fair algorithm 2PC {
  variable 
    rmState = [rm \in RM |-> "working"],
    tmState = "init"; \* if unknown, BTM is triggered
  
define {
    RM == 1..3  \* set of resource managers 

    canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared","committed"} 
    canAbort ==     \E rm \in RM  : rmState[rm] \in {"aborted","unknown"} 
                /\ ~\E rmc \in RM : rmState[rmc]= "committed"  \* for BTM

    \* Type invariant
    TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "unknown"}]
              /\ tmState \in {"init","commit","abort","unknown"}

    \* Invariant: no two RMs arrive at conflicting decisions           
    Consistent ==         
        ~ \E rm1, rm2 \in RM : /\ rmState[rm1] = "aborted"
                               /\ rmState[rm2] = "committed"

    \* Bait invariant to test TLC output
    NotCommitted == \A rm \in RM : rmState[rm] # "committed" 

    \* To replace termination
    Completion == <> (\A rm \in RM : rmState[rm] \in {"committed","aborted"}) 

    \* Bait invariant to check if BTM takes over
    TerminalUnknown == [] [tmState = "unknown"  => tmState' = "unknown"]_<<pc>>
    \* TerminalUnknown == [] [tmState = "unknown" =>  tmState'="abort"]_<<tmState>>
  }


  fair process (RManager \in RM) 
  variables pre=""; {
RS:  while (/\ rmState[self] \notin {"committed", "aborted"}
            /\ pre \notin {"committed", "aborted"}) { 
        either { 
           await rmState[self] = "working";
           rmState[self] := "prepared"; } 
        or { 
           await rmState[self]="prepared" /\ tmState="commit";
RC:        rmState[self] := "committed";}
        or {
           await rmState[self]="working" 
            \/  (rmState[self]="prepared" /\ tmState="abort");
RA:        rmState[self] := "aborted";}  
        or { 
           await RMMAYFAIL  /\  pre # rmState[self];
RF:        pre := rmState[self];    \* Log state pre-failure
           rmState[self] := "unknown";  \* Fail
RR:        rmState[self]:= pre;     \* Recover state pre-failure
           }   
     }                 
  }

   
  fair process (TManager=0) {
TS:  either { 
        await canCommit;
TC:     tmState := "commit";}
     or { 
        await canAbort;
TA:     tmState := "abort";};

TF:     if (TMMAYFAIL) tmState := "unknown"; 
  }


  fair process (BTManager=10) {
BTS: either {
        await canCommit /\ tmState = "unknown"; 
BTC:    tmState := "commit";}     
     or {
        await canAbort /\ tmState = "unknown";
BTA:    tmState := "abort";}
  }
}

***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES rmState, tmState, pc

(* define statement *)
RM == 1..3

canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared","committed"}
canAbort ==     \E rm \in RM  : rmState[rm] \in {"aborted","unknown"}
            /\ ~\E rmc \in RM : rmState[rmc]= "committed"


TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted", "unknown"}]
          /\ tmState \in {"init","commit","abort","unknown"}


Consistent ==
    ~ \E rm1, rm2 \in RM : /\ rmState[rm1] = "aborted"
                           /\ rmState[rm2] = "committed"


NotCommitted == \A rm \in RM : rmState[rm] # "committed"


Completion == <> (\A rm \in RM : rmState[rm] \in {"committed","aborted"})


TerminalUnknown == [] [tmState = "unknown"  => tmState' = "unknown"]_<<pc>>

VARIABLE pre

vars == << rmState, tmState, pc, pre >>

ProcSet == (RM) \cup {0} \cup {10}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        (* Process RManager *)
        /\ pre = [self \in RM |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"
                                        [] self = 10 -> "BTS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF /\ rmState[self] \notin {"committed", "aborted"}
                  /\ pre[self] \notin {"committed", "aborted"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             /\ pc' = [pc EXCEPT ![self] = "RS"]
                          \/ /\ rmState[self]="prepared" /\ tmState="commit"
                             /\ pc' = [pc EXCEPT ![self] = "RC"]
                             /\ UNCHANGED rmState
                          \/ /\      rmState[self]="working"
                                \/  (rmState[self]="prepared" /\ tmState="abort")
                             /\ pc' = [pc EXCEPT ![self] = "RA"]
                             /\ UNCHANGED rmState
                          \/ /\ RMMAYFAIL  /\  pre[self] # rmState[self]
                             /\ pc' = [pc EXCEPT ![self] = "RF"]
                             /\ UNCHANGED rmState
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED << tmState, pre >>

RC(self) == /\ pc[self] = "RC"
            /\ rmState' = [rmState EXCEPT ![self] = "committed"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RA(self) == /\ pc[self] = "RA"
            /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RF(self) == /\ pc[self] = "RF"
            /\ pre' = [pre EXCEPT ![self] = rmState[self]]
            /\ rmState' = [rmState EXCEPT ![self] = "unknown"]
            /\ pc' = [pc EXCEPT ![self] = "RR"]
            /\ UNCHANGED tmState

RR(self) == /\ pc[self] = "RR"
            /\ rmState' = [rmState EXCEPT ![self] = pre[self]]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RManager(self) == RS(self) \/ RC(self) \/ RA(self) \/ RF(self) \/ RR(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState, pre >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "TF"]
      /\ UNCHANGED << rmState, pre >>

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "TF"]
      /\ UNCHANGED << rmState, pre >>

TF == /\ pc[0] = "TF"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unknown"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, pre >>

TManager == TS \/ TC \/ TA \/ TF

BTS == /\ pc[10] = "BTS"
       /\ \/ /\ canCommit /\ tmState = "unknown"
             /\ pc' = [pc EXCEPT ![10] = "BTC"]
          \/ /\ canAbort /\ tmState = "unknown"
             /\ pc' = [pc EXCEPT ![10] = "BTA"]
       /\ UNCHANGED << rmState, tmState, pre >>

BTC == /\ pc[10] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, pre >>

BTA == /\ pc[10] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, pre >>

BTManager == BTS \/ BTC \/ BTA

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

=============================================================================

