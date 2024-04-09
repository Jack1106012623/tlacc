---- MODULE raftcc_TTrace_1710939461 ----
EXTENDS Sequences, raftcc, TLCExt, raftcc_TEConstants, Toolbox, Naturals, TLC

_expression ==
    LET raftcc_TEExpression == INSTANCE raftcc_TEExpression
    IN raftcc_TEExpression!expression
----

_trace ==
    LET raftcc_TETrace == INSTANCE raftcc_TETrace
    IN raftcc_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        votedFor = ((n1 :> Nil @@ n2 :> Nil @@ n3 :> Nil))
        /\
        currentTerm = ((n1 :> 2 @@ n2 :> 1 @@ n3 :> 1))
        /\
        votesResponded = ((n1 :> {} @@ n2 :> {} @@ n3 :> {}))
        /\
        log = ((n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>))
        /\
        votesGranted = ((n1 :> {} @@ n2 :> {} @@ n3 :> {}))
        /\
        voterLog = ((n1 :> << >> @@ n2 :> << >> @@ n3 :> << >>))
        /\
        messages = (<< >>)
        /\
        matchIndex = ((n1 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n3 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)))
        /\
        state = ((n1 :> Candidate @@ n2 :> Follower @@ n3 :> Follower))
        /\
        nextIndex = ((n1 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n3 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)))
        /\
        elections = ({})
        /\
        commitIndex = ((n1 :> 0 @@ n2 :> 0 @@ n3 :> 0))
    )
----

_init ==
    /\ elections = _TETrace[1].elections
    /\ messages = _TETrace[1].messages
    /\ matchIndex = _TETrace[1].matchIndex
    /\ log = _TETrace[1].log
    /\ state = _TETrace[1].state
    /\ commitIndex = _TETrace[1].commitIndex
    /\ currentTerm = _TETrace[1].currentTerm
    /\ votesResponded = _TETrace[1].votesResponded
    /\ nextIndex = _TETrace[1].nextIndex
    /\ votesGranted = _TETrace[1].votesGranted
    /\ voterLog = _TETrace[1].voterLog
    /\ votedFor = _TETrace[1].votedFor
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ elections  = _TETrace[i].elections
        /\ elections' = _TETrace[j].elections
        /\ messages  = _TETrace[i].messages
        /\ messages' = _TETrace[j].messages
        /\ matchIndex  = _TETrace[i].matchIndex
        /\ matchIndex' = _TETrace[j].matchIndex
        /\ log  = _TETrace[i].log
        /\ log' = _TETrace[j].log
        /\ state  = _TETrace[i].state
        /\ state' = _TETrace[j].state
        /\ commitIndex  = _TETrace[i].commitIndex
        /\ commitIndex' = _TETrace[j].commitIndex
        /\ currentTerm  = _TETrace[i].currentTerm
        /\ currentTerm' = _TETrace[j].currentTerm
        /\ votesResponded  = _TETrace[i].votesResponded
        /\ votesResponded' = _TETrace[j].votesResponded
        /\ nextIndex  = _TETrace[i].nextIndex
        /\ nextIndex' = _TETrace[j].nextIndex
        /\ votesGranted  = _TETrace[i].votesGranted
        /\ votesGranted' = _TETrace[j].votesGranted
        /\ voterLog  = _TETrace[i].voterLog
        /\ voterLog' = _TETrace[j].voterLog
        /\ votedFor  = _TETrace[i].votedFor
        /\ votedFor' = _TETrace[j].votedFor

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("raftcc_TTrace_1710939461.json", _TETrace)

=============================================================================

 Note that you can extract this module `raftcc_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `raftcc_TEExpression.tla` file takes precedence 
  over the module `raftcc_TEExpression` below).

---- MODULE raftcc_TEExpression ----
EXTENDS Sequences, raftcc, TLCExt, raftcc_TEConstants, Toolbox, Naturals, TLC

expression == 
    [
        \* To hide variables of the `raftcc` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        elections |-> elections
        ,messages |-> messages
        ,matchIndex |-> matchIndex
        ,log |-> log
        ,state |-> state
        ,commitIndex |-> commitIndex
        ,currentTerm |-> currentTerm
        ,votesResponded |-> votesResponded
        ,nextIndex |-> nextIndex
        ,votesGranted |-> votesGranted
        ,voterLog |-> voterLog
        ,votedFor |-> votedFor
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_electionsUnchanged |-> elections = elections'
        
        \* Format the `elections` variable as Json value.
        \* ,_electionsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(elections)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_electionsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].elections # _TETrace[s-1].elections
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE raftcc_TETrace ----
\*EXTENDS IOUtils, raftcc, raftcc_TEConstants, TLC
\*
\*trace == IODeserialize("raftcc_TTrace_1710939461.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE raftcc_TETrace ----
EXTENDS raftcc, raftcc_TEConstants, TLC

trace == 
    <<
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil @@ n3 :> Nil),currentTerm |-> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {} @@ n3 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {} @@ n3 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >> @@ n3 :> << >>),messages |-> << >>,matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n3 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)),state |-> (n1 :> Follower @@ n2 :> Follower @@ n3 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n3 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)]),
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil @@ n3 :> Nil),currentTerm |-> (n1 :> 2 @@ n2 :> 1 @@ n3 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {} @@ n3 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>> @@ n3 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {} @@ n3 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >> @@ n3 :> << >>),messages |-> << >>,matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0) @@ n3 :> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)),state |-> (n1 :> Candidate @@ n2 :> Follower @@ n3 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1) @@ n3 :> (n1 :> 1 @@ n2 :> 1 @@ n3 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0 @@ n3 :> 0)])
    >>
----


=============================================================================

---- MODULE raftcc_TEConstants ----
EXTENDS raftcc

CONSTANTS n1, n2, n3, v1, v2

=============================================================================

---- CONFIG raftcc_TTrace_1710939461 ----
CONSTANTS
    Server = { n1 , n2 , n3 }
    Value = { v1 , v2 }
    Follower = Follower
    Candidate = Candidate
    Leader = Leader
    Nil = Nil
    RequestVoteRequest = RequestVoteRequest
    RequestVoteResponse = RequestVoteResponse
    AppendEntriesRequest = AppendEntriesRequest
    AppendEntriesResponse = AppendEntriesResponse
    AppendEntriesResponse = AppendEntriesResponse
    Leader = Leader
    RequestVoteResponse = RequestVoteResponse
    Candidate = Candidate
    v1 = v1
    n2 = n2
    n1 = n1
    n3 = n3
    v2 = v2
    Follower = Follower
    RequestVoteRequest = RequestVoteRequest
    Nil = Nil
    AppendEntriesRequest = AppendEntriesRequest

INVARIANT
    _inv

CHECK_DEADLOCK
    \* CHECK_DEADLOCK off because of PROPERTY or INVARIANT above.
    FALSE

INIT
    _init

NEXT
    _next

CONSTANT
    _TETrace <- _trace

ALIAS
    _expression
=============================================================================
\* Generated on Wed Mar 20 20:57:43 CST 2024