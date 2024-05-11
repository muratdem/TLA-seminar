----------------------------- MODULE 2PC ------------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANT
    TMMAYFAIL   \* whether TM may fail

(* --algorithm 2PC {
  variable 
    rmState = [rm \in RM |-> "working"],
    tmState = "unknown";

  define {
    RM == 1..3  \* set of resource managers 
      
    canCommit == \A rm \in RM : rmState[rm] \in {"prepared"}
    canAbort  == \E rm \in RM : rmState[rm] = "aborted"

    \* Type invariant           
    TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
              /\ tmState \in {"commit","abort","unknown"}

    \* Invariant: no two RMs arrive at conflicting decisions            
    Consistent ==         
        ~ \E rm1, rm2 \in RM : /\ rmState[rm1] = "aborted"
                               /\ rmState[rm2] = "committed"

    \* Bait invariants to test TLC output      
    NotCommitted == \A rm \in RM : rmState[rm] # "committed"   
  }

  macro Prepare(p) {
    await rmState[p] = "working";
    rmState[p] := "prepared" ;    
  }
   
  macro Decide(p) {
    either { 
        await tmState="commit";
        rmState[p] := "committed";}
    or { 
        await rmState[p]="working" \/ tmState="abort";
        rmState[p] := "aborted";}  
  }


  fair process (RManager \in RM) {
RS:   while (rmState[self] \in {"working", "prepared"}) { 
        either 
            Prepare(self) 
        or 
            Decide(self) 
        }
  }


  fair process (TManager=0) {
TS: either { 
        await canCommit;
TC:     tmState := "commit";}    
    or { 
        await canAbort;
TA:     tmState := "abort";};

TF: if (TMMAYFAIL) tmState := "unknown"; \* tm state becomes inaccessible
    }

} \* end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "2684d127" /\ chksum(tla) = "c9cd9736")
VARIABLES rmState, tmState, pc

(* define statement *)
RM == 1..3

canCommit == \A rm \in RM : rmState[rm] \in {"prepared"}
canAbort  == \E rm \in RM : rmState[rm] = "aborted"


TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
          /\ tmState \in {"commit","abort","unknown"}


Consistent ==
    ~ \E rm1, rm2 \in RM : /\ rmState[rm1] = "aborted"
                           /\ rmState[rm2] = "committed"


NotCommitted == \A rm \in RM : rmState[rm] # "committed"


vars == << rmState, tmState, pc >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "unknown"
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                          \/ /\ \/ /\ tmState="commit"
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                \/ /\ rmState[self]="working" \/ tmState="abort"
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED rmState
            /\ UNCHANGED tmState

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << rmState, tmState >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "TF"]
      /\ UNCHANGED rmState

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "TF"]
      /\ UNCHANGED rmState

TF == /\ pc[0] = "TF"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unknown"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED rmState

TManager == TS \/ TC \/ TA \/ TF

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=========================
