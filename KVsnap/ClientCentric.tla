--------------------------- MODULE ClientCentric ---------------------------
EXTENDS Naturals, TLC, Sequences, FiniteSets, Util
VARIABLES Keys, Values

\* TLA+ specifications of Client Centric Isolation Specification by Crooks et al: https://dl.acm.org/doi/10.1145/3087801.3087802
\* TLA+ specifications by Tim Soethout (tim.soethout@ing.com)
\* For BSD license see: https://github.com/cwi-swat/tla-ci/blob/master/LICENSE

\* A database `State` is represented by keys with corresponding values
State == [Keys -> Values]

\* An `Operation` is a read or write of a key and value
Operation == [op: {"read", "write"}, key: Keys, value: Values]

\* Helpers representing Reads and Writes
r(k,v) == [op |-> "read",  key |-> k, value |-> v]
w(k,v) == [op |-> "write", key |-> k, value |-> v]

\* A `Transaction` is a total order of `Operation`s
\* Transaction == [ops: Seq(Operation), start: TimeStamp, commit: TimeStamp]
Transaction == Seq(Operation)
\* For simplicity we store start and commit in a lookup function
TimeStamp == Nat
TransactionTimes == [t \in Transaction |-> [start: TimeStamp, commit: TimeStamp]]

\* "An execution e for a set of transactions
\* T is a totally ordered set defined by the pair (Se,−−t \in T−→),
\* where Se is the set of states generated by applying, 
\* starting from the system’s initial state, a permutation of all the transactions in T ."
ExecutionElem == [parentState: State, transaction: Transaction]
\* resultState is the parentState of the next transaction, but not used in the isolation definitions.
\* ExecutionElem == [parentState: State, transaction: Transaction, resultState: State]
\* We represent an `Execution` as a sequence of `Transaction`s with their corresponding parent state.
\* Note: This execution does therefor not contain the "final state" of the execution, since it is not a parent state of a transaction.
Execution == Seq(ExecutionElem)

\* Seq
executionStates(execution) == [ i \in 1..Len(execution) |-> execution[i].parentState ]
\* Set
executionTransactions(execution) == { ep.transaction : ep \in SeqToSet(execution) }

\* "The parent state is the last state in the execution
\* Definition 1: s -T-> s' ≡ [(k,v) ∈ s ∧ (k,v) \notin s'] => k ∈ W_T /\ w(k,v) ∈ Σ_T => (k,v) ∈ s.
\* We refer to s as the parent state of T (denoted as sp,T ); to the
\* transaction that generated s as Ts ; and to the set of keys in which
\* s and s′ differ as ∆(s,s′)"
parentState(execution, transaction) == 
  LET ind == CHOOSE i \in 1..Len(execution): execution[i].transaction = transaction
  IN execution[ind].parentState

\* w(k,v) -to-> r(k,v)
\* check reads and writes, implicit because of "write" check in ReadStates
earlierInTransaction(transaction, op1, op2) == Index(transaction, op1) < Index(transaction, op2)

\* state1 -*-> state2
beforeOrEqualInExecution(execution, state1, state2) == 
  LET states == executionStates(execution)
  IN  Index(states, state1) <= Index(states, state2)

\* Read states: from which states can the operation read it's value
ReadStates(execution, operation, transaction) == 
  LET Se == SeqToSet(executionStates(execution))
      sp == parentState(execution, transaction)
  IN { s \in Se:
        /\ beforeOrEqualInExecution(execution, s, sp) \* s -*-> s_p: restrict the valid read states for the operations in T to be no later than sp
        /\ \/ s[operation.key] = operation.value \* (k,v) \in s
           \/ \E write \in SeqToSet(transaction): 
              /\ write.op = "write" /\ write.key = operation.key /\ write.value = operation.value
              /\ earlierInTransaction(transaction, write, operation) \* w(k,v)-to->r(k,v)
\* "By convention, write operations have read states too: for a write operation in T , they include all states in Se up to and including T ’s parent state."
           \/ operation.op = "write"
     }
        
Preread(execution, transaction) ==
  \A operation \in SeqToSet(transaction): ReadStates(execution, operation, transaction) /= {}

PrereadAll(execution, transactions) == 
  \A transaction \in transactions: Preread(execution, transaction)

\* A state `s` is complete for `T` in `e` if every operation in `T` can read from `s`
Complete(execution, transaction, state) == 
  LET setOfAllReadStatesOfOperation(transactionOperations) ==
        { ReadStates(execution, operation, transaction) : operation \in SeqToSet(transactionOperations) }
     \* readStatesForEmptyTransaction contains all previous states, to ensure that empty txns do not incorrectly invalidate the checked isolation level
      readStatesForEmptyTransaction == { s \in SeqToSet(executionStates(execution)) : beforeOrEqualInExecution(execution, s, parentState(execution, transaction)) }
  IN state \in INTERSECTION(setOfAllReadStatesOfOperation(transaction) \union { readStatesForEmptyTransaction } )

\* "the write set of T comprises the keys that T updates: WT = {k|w(k, v) ∈ ΣT }.
\* For simplicity of exposition, we assume that a transaction only writes a key once."
WriteSet(transaction) == 
  LET writes == { operation \in SeqToSet(transaction) : operation.op = "write" } 
  IN { operation.key : operation \in writes } 
\* "Denoting the set of keys in which s and s′ differ as ∆(s, s′), we express this as NO-CONF_T (s) ≡ ∆(s, sp) ∩ WT = ∅"
NoConf(execution, transaction, state) == 
  LET Sp == parentState(execution, transaction)
      delta == { key \in DOMAIN Sp : Sp[key] /= state[key] }
  IN delta \intersect WriteSet(transaction) = {}
  
\* `t1` comes before `t2` in wall clock/oracle time
ComesStrictBefore(t1, t2, timestamps) == timestamps[t1].commit < timestamps[t2].start

\* Given system state and single transaction (seq of operations), determines new state
effects(state, transaction) == 
       ReduceSeq(LAMBDA o, newState: IF o.op = "write" THEN [newState EXCEPT ![o.key] = o.value] ELSE newState, transaction, state)

\* Lists all possible permutations of executions given set of transactions
executions(initialState, transactions) == 
  \* All possible permutations
  LET orderings == PermSeqs(transactions)
\*      initialState == [k \in Keys |-> InitValue] \* makes it level-1 therefor pass it in
      accummulator == [ execution |-> <<>>, nextState |-> initialState ]
  IN { LET executionAcc == ReduceSeq(
         \*                                store ExecutionElem in accumulator
                            LAMBDA t, acc: [ execution |-> Append(acc.execution, [parentState |-> acc.nextState, transaction |-> t])
  \*                                         calcultate next state
                                           , nextState |-> effects(acc.nextState,t) 
                            ],
                            ordering, accummulator)
\*              recover ExecutionElems
       IN executionAcc.execution
     : ordering \in orderings }

\* Helper: checks if specific execution satisfies given commit test
executionSatisfiesCT(execution, commitTest(_,_)) ==
  LET transactions == executionTransactions(execution)
  IN \A transaction \in transactions: commitTest(transaction, execution)

\* tests there exists an execution for `transactions`, that satisfies the isolation level given by `commitTest`
\* "Definition 5 Given a set of transactions T and their read states, 
\* a storagesystem satisfies an isolation level I iff ∃e:∀t ∈ T :CTI(t,e)."
satisfyIsolationLevel(initialState, transactions, commitTest(_,_)) ==
  \E execution \in executions(initialState, transactions): \A transaction \in transactions:
    \* PrintT(<<"try execution:",execution>>) =>
    commitTest(transaction, execution)

\* Serializability commit test
CT_SER(transaction, execution) ==
  Complete(execution, transaction, parentState(execution, transaction))
Serializability(initialState, transactions) == satisfyIsolationLevel(initialState, transactions, CT_SER)

\*SerializabilityDebug(initialState, transactions) == 
\*  \* if no executions satify commit test, print all executions
\*  \/ (~\E execution \in executions(initialState, transactions): \A transaction \in transactions:
\*       CT_SER(transaction, execution)) => \A execution \in executions(initialState, transactions): PrintT(<<"Execution not Serializable:",execution>>)
\*  \* fall back to normal check
\*  \/ \E execution \in executions(initialState, transactions): \A transaction \in transactions: CT_SER(transaction, execution)
  
SerializabilityDebug(initialState, transactions) == 
  ~ Serializability(initialState, transactions) => Print(<<"Executions not Serializable:",  executions(initialState, transactions)>>, FALSE)

\* Snapshot Isolation
CT_SI(transaction, execution) == \E state \in SeqToSet(executionStates(execution)):
  Complete(execution, transaction, state) /\ NoConf(execution, transaction, state)
SnapshotIsolation(initialState, transactions) == satisfyIsolationLevel(initialState, transactions, CT_SI)

\* Strict Serializability: ∀T ∈T:T <s T => s_T′ -*-> s_T.
CT_SSER(timestamps, transaction, execution) ==
  LET Sp == parentState(execution, transaction)
  IN /\ Complete(execution, transaction, Sp)
     /\ \A otherTransaction \in executionTransactions(execution): 
        ComesStrictBefore(otherTransaction, transaction, timestamps) => 
          beforeOrEqualInExecution(execution, parentState(execution, otherTransaction), Sp)
\* For now inline `satisfyIsolationLevel` instead of `satisfyIsolationLevel(transactions, CT_SSER(timestamps)) because partial functions are not supported/hard`
StrictSerializability(initialState, transactions, timestamps) ==
  \E execution \in executions(initialState, transactions): \A transaction \in transactions: CT_SSER(timestamps, transaction, execution)

\* Read Committed
CT_RC(transaction, execution) == Preread(execution, transaction)
ReadCommitted(initialState, transactions) == satisfyIsolationLevel(initialState, transactions, CT_RC)

\* Read Uncommitted
CT_RU(transaction, execution) == TRUE
ReadUncommitted(initialState, transactions) == satisfyIsolationLevel(initialState, transactions, CT_RU)

\* Check types in derived specification
TypeOKT(transactions) ==
\*  /\ InitValue \in Values
  /\ transactions \subseteq Transaction

TypeOK(transactions, execution) == 
  /\ TypeOKT(transactions)
\*  /\ PrintT(State)
  /\ execution \in Execution

=============================================================================