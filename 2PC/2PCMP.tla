----------------------------- MODULE 2PCMP ------------------------------
EXTENDS Integers, FiniteSets, TLC
CONSTANT
    TMMAYFAIL   \* whether TM may fail

\* This is just an educational exercise to showcase 
\* how 2PC.tla that was modeled as a shared memory system
\* can be re-modeled as a message-passing system.
\* State-space increased by 5 folds, model got uglier, 
\* with not much benefit for additional behaviors to check. 
\* We used "network" set as a shared whiteboard to add msgs and read from.
\* Set filtering did the heavy-lifting for receiving a message of interest.
\* We also converted global rmState/tmState into process-local vars.
\* This resulted in having to move the Invariants at the end of TLA translation.


(* --algorithm 2PCMP {
  variable
    network = {}; \* all communication happens here via shared whiteboard model: add/read    

  define {
    RM == 1..3  \* set of resource managers 
      
    \* useful definitions to filter/query network 
    PreparedMsgs(i) == {m \in network: m.t="prepared"   /\ m.s=i}
    AbortedMsgs(i)  == {m \in network: m.t="aborted"    /\ m.s=i}
    TCommitMsg(i)   == {m \in network: m.t="t-commit"   /\ m.d=i}
    TAbortMsg(i)    == {m \in network: m.t="t-abort"    /\ m.d=i}

    canCommit == \A rm \in RM : PreparedMsgs(rm) # {}
    canAbort  == \E rm \in RM : AbortedMsgs(rm) # {}
      
    \* example of message constructors 
    msg_prepared(i) == [ t |-> "prepared", s |-> i ]
    msg_aborted(i)  == [ t |-> "aborted",  s |-> i ]

    \* All possible protocol messages
    Messages == [t:{"prepared"}, s:RM]
        \union  [t:{"aborted"},  s:RM]
        \union  [t:{"t-commit"}, d:RM]
        \union  [t:{"t-abort"},  d:RM]      
                
  }


  \* macro for sending a message to the network
  macro Send(m)  { network := network \union {m}; }

          
  macro Prepare(p) {
    await rmState = "working";
    rmState := "prepared" ;
    Send(msg_prepared(p));      
  }
   
  macro Decide(p) {
    either { 
        \* await tmState="commit";
        await TCommitMsg(p) # {};        
        rmState := "committed";}
    or { 
        \* await rmState[p]="working" \/ tmState="abort";
        await rmState="working" \/ TAbortMsg(p) #{}; 
        rmState := "aborted";
        Send(msg_aborted(p));}  
  }


  fair process (RManager \in RM)
  variables 
      rmState = "working"; 
  {
RS:   while (rmState \in {"working", "prepared"}) { 
        either 
            Prepare(self) 
        or 
            Decide(self) 
        }
  }


  fair process (TManager=0) 
    variables
        tmState = "unknown", 
        informset = RM;
    {      
TS: either { 
        await canCommit;
TC:     tmState := "commit";
TCI:    while (informset#{}) {
            with (r \in informset) {
                network := network \union {[t|->"t-commit", d|->r]};
                informset := informset \ {r};
            };
            if (TMMAYFAIL) goto TF;
        }   
        }    
    or { 
        await canAbort;
TA:     tmState := "abort";
TaI:    while (informset#{}) {
            with (r \in informset) {
                network := network \union {[t|->"t-abort", d|->r]};
                informset := informset \ {r};
            };
            if (TMMAYFAIL) goto TF;
        }   
        };

TF: tmState := "unknown"; \* tm state becomes inaccessible
    }

} \* end algorithm
*)

\* BEGIN TRANSLATION (chksum(pcal) = "91cdbd09" /\ chksum(tla) = "b6852bf3")
VARIABLES network, pc

(* define statement *)
RM == 1..3


PreparedMsgs(i) == {m \in network: m.t="prepared"   /\ m.s=i}
AbortedMsgs(i)  == {m \in network: m.t="aborted"    /\ m.s=i}
TCommitMsg(i)   == {m \in network: m.t="t-commit"   /\ m.d=i}
TAbortMsg(i)    == {m \in network: m.t="t-abort"    /\ m.d=i}

canCommit == \A rm \in RM : PreparedMsgs(rm) # {}
canAbort  == \E rm \in RM : AbortedMsgs(rm) # {}


msg_prepared(i) == [ t |-> "prepared", s |-> i ]
msg_aborted(i)  == [ t |-> "aborted",  s |-> i ]


Messages == [t:{"prepared"}, s:RM]
    \union  [t:{"aborted"},  s:RM]
    \union  [t:{"t-commit"}, d:RM]
    \union  [t:{"t-abort"},  d:RM]

VARIABLES rmState, tmState, informset

vars == << network, pc, rmState, tmState, informset >>

ProcSet == (RM) \cup {0}

Init == (* Global variables *)
        /\ network = {}
        (* Process RManager *)
        /\ rmState = [self \in RM |-> "working"]
        (* Process TManager *)
        /\ tmState = "unknown"
        /\ informset = RM
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TS"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             /\ network' = (network \union {(msg_prepared(self))})
                          \/ /\ \/ /\ TCommitMsg(self) # {}
                                   /\ rmState' = [rmState EXCEPT ![self] = "committed"]
                                   /\ UNCHANGED network
                                \/ /\ rmState[self]="working" \/ TAbortMsg(self) #{}
                                   /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
                                   /\ network' = (network \union {(msg_aborted(self))})
                       /\ pc' = [pc EXCEPT ![self] = "RS"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << network, rmState >>
            /\ UNCHANGED << tmState, informset >>

RManager(self) == RS(self)

TS == /\ pc[0] = "TS"
      /\ \/ /\ canCommit
            /\ pc' = [pc EXCEPT ![0] = "TC"]
         \/ /\ canAbort
            /\ pc' = [pc EXCEPT ![0] = "TA"]
      /\ UNCHANGED << network, rmState, tmState, informset >>

TC == /\ pc[0] = "TC"
      /\ tmState' = "commit"
      /\ pc' = [pc EXCEPT ![0] = "TCI"]
      /\ UNCHANGED << network, rmState, informset >>

TCI == /\ pc[0] = "TCI"
       /\ IF informset#{}
             THEN /\ \E r \in informset:
                       /\ network' = (network \union {[t|->"t-commit", d|->r]})
                       /\ informset' = informset \ {r}
                  /\ IF TMMAYFAIL
                        THEN /\ pc' = [pc EXCEPT ![0] = "TF"]
                        ELSE /\ pc' = [pc EXCEPT ![0] = "TCI"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "TF"]
                  /\ UNCHANGED << network, informset >>
       /\ UNCHANGED << rmState, tmState >>

TA == /\ pc[0] = "TA"
      /\ tmState' = "abort"
      /\ pc' = [pc EXCEPT ![0] = "TaI"]
      /\ UNCHANGED << network, rmState, informset >>

TaI == /\ pc[0] = "TaI"
       /\ IF informset#{}
             THEN /\ \E r \in informset:
                       /\ network' = (network \union {[t|->"t-abort", d|->r]})
                       /\ informset' = informset \ {r}
                  /\ IF TMMAYFAIL
                        THEN /\ pc' = [pc EXCEPT ![0] = "TF"]
                        ELSE /\ pc' = [pc EXCEPT ![0] = "TaI"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "TF"]
                  /\ UNCHANGED << network, informset >>
       /\ UNCHANGED << rmState, tmState >>

TF == /\ pc[0] = "TF"
      /\ tmState' = "unknown"
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << network, rmState, informset >>

TManager == TS \/ TC \/ TCI \/ TA \/ TaI \/ TF

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


\* INVARIANTS moved here after making variables local

    \* Type invariant           
    TypeOK == /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
              /\ tmState \in {"commit","abort","unknown"}
              /\ network \subseteq Messages \* messages in network are well-defined protocol messages  

    \* Invariant: no two RMs arrive at conflicting decisions            
    Consistent ==         
        ~ \E rm1, rm2 \in RM : /\ rmState[rm1] = "aborted"
                               /\ rmState[rm2] = "committed"

    \* Bait invariants to test TLC output      
    NotCommitted == \A rm \in RM : rmState[rm] # "committed"   

=========================
