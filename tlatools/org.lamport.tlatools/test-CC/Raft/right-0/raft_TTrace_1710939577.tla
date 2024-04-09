---- MODULE raft_TTrace_1710939577 ----
EXTENDS Sequences, raft_TEConstants, TLCExt, Toolbox, raft, Naturals, TLC

_expression ==
    LET raft_TEExpression == INSTANCE raft_TEExpression
    IN raft_TEExpression!expression
----

_trace ==
    LET raft_TETrace == INSTANCE raft_TETrace
    IN raft_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        votedFor = ((n1 :> n1 @@ n2 :> Nil))
        /\
        currentTerm = ((n1 :> 2 @@ n2 :> 1))
        /\
        votesResponded = ((n1 :> {} @@ n2 :> {}))
        /\
        log = ((n1 :> <<>> @@ n2 :> <<>>))
        /\
        votesGranted = ((n1 :> {} @@ n2 :> {}))
        /\
        voterLog = ((n1 :> << >> @@ n2 :> << >>))
        /\
        messages = (([mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n1] :> 0 @@ [mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n2] :> 1 @@ [mtype |-> RequestVoteResponse, mterm |-> 2, msource |-> n1, mdest |-> n1, mlog |-> <<>>, mvoteGranted |-> TRUE] :> 1))
        /\
        matchIndex = ((n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)))
        /\
        state = ((n1 :> Candidate @@ n2 :> Follower))
        /\
        nextIndex = ((n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)))
        /\
        elections = ({})
        /\
        commitIndex = ((n1 :> 0 @@ n2 :> 0))
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
    \*         IN J!JsonSerialize("raft_TTrace_1710939577.json", _TETrace)

=============================================================================

 Note that you can extract this module `raft_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `raft_TEExpression.tla` file takes precedence 
  over the module `raft_TEExpression` below).

---- MODULE raft_TEExpression ----
EXTENDS Sequences, raft_TEConstants, TLCExt, Toolbox, raft, Naturals, TLC

expression == 
    [
        \* To hide variables of the `raft` spec from the error trace,
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
\*---- MODULE raft_TETrace ----
\*EXTENDS IOUtils, raft_TEConstants, raft, TLC
\*
\*trace == IODeserialize("raft_TTrace_1710939577.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE raft_TETrace ----
EXTENDS raft_TEConstants, raft, TLC

trace == 
    <<
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil),currentTerm |-> (n1 :> 1 @@ n2 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >>),messages |-> << >>,matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)),state |-> (n1 :> Follower @@ n2 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0)]),
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil),currentTerm |-> (n1 :> 2 @@ n2 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >>),messages |-> << >>,matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)),state |-> (n1 :> Candidate @@ n2 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0)]),
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil),currentTerm |-> (n1 :> 2 @@ n2 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >>),messages |-> ([mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n1] :> 1),matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)),state |-> (n1 :> Candidate @@ n2 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0)]),
    ([votedFor |-> (n1 :> Nil @@ n2 :> Nil),currentTerm |-> (n1 :> 2 @@ n2 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >>),messages |-> ([mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n1] :> 1 @@ [mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n2] :> 1),matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)),state |-> (n1 :> Candidate @@ n2 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0)]),
    ([votedFor |-> (n1 :> n1 @@ n2 :> Nil),currentTerm |-> (n1 :> 2 @@ n2 :> 1),votesResponded |-> (n1 :> {} @@ n2 :> {}),log |-> (n1 :> <<>> @@ n2 :> <<>>),votesGranted |-> (n1 :> {} @@ n2 :> {}),voterLog |-> (n1 :> << >> @@ n2 :> << >>),messages |-> ([mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n1] :> 0 @@ [mtype |-> RequestVoteRequest, mterm |-> 2, mlastLogTerm |-> 0, mlastLogIndex |-> 0, msource |-> n1, mdest |-> n2] :> 1 @@ [mtype |-> RequestVoteResponse, mterm |-> 2, msource |-> n1, mdest |-> n1, mlog |-> <<>>, mvoteGranted |-> TRUE] :> 1),matchIndex |-> (n1 :> (n1 :> 0 @@ n2 :> 0) @@ n2 :> (n1 :> 0 @@ n2 :> 0)),state |-> (n1 :> Candidate @@ n2 :> Follower),nextIndex |-> (n1 :> (n1 :> 1 @@ n2 :> 1) @@ n2 :> (n1 :> 1 @@ n2 :> 1)),elections |-> {},commitIndex |-> (n1 :> 0 @@ n2 :> 0)])
    >>
----


=============================================================================

---- MODULE raft_TEConstants ----
EXTENDS raft

CONSTANTS n1, n2, v1, v2

=============================================================================

---- CONFIG raft_TTrace_1710939577 ----
CONSTANTS
    Server = { n1 , n2 }
    Value = { v1 , v2 }
    Follower = Follower
    Candidate = Candidate
    Leader = Leader
    Nil = Nil
    RequestVoteRequest = RequestVoteRequest
    RequestVoteResponse = RequestVoteResponse
    AppendEntriesRequest = AppendEntriesRequest
    AppendEntriesResponse = AppendEntriesResponse
    Nil = Nil
    RequestVoteRequest = RequestVoteRequest
    RequestVoteResponse = RequestVoteResponse
    AppendEntriesRequest = AppendEntriesRequest
    AppendEntriesResponse = AppendEntriesResponse
    n1 = n1
    n2 = n2
    v1 = v1
    v2 = v2
    Follower = Follower
    Candidate = Candidate
    Leader = Leader

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
\* Generated on Wed Mar 20 20:59:38 CST 2024