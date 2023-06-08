---- MODULE Paxos_TTrace_1681826100 ----
EXTENDS Sequences, TLCExt, Toolbox, Paxos_TEConstants, Naturals, TLC, Paxos

_expression ==
    LET Paxos_TEExpression == INSTANCE Paxos_TEExpression
    IN Paxos_TEExpression!expression
----

_trace ==
    LET Paxos_TETrace == INSTANCE Paxos_TETrace
    IN Paxos_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        msgs = ({})
        /\
        maxVal = ()
        /\
        maxBal = ()
        /\
        maxVBal = ()
    )
----

_init ==
    /\ maxVBal = _TETrace[1].maxVBal
    /\ msgs = _TETrace[1].msgs
    /\ maxVal = _TETrace[1].maxVal
    /\ maxBal = _TETrace[1].maxBal
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ maxVBal  = _TETrace[i].maxVBal
        /\ maxVBal' = _TETrace[j].maxVBal
        /\ msgs  = _TETrace[i].msgs
        /\ msgs' = _TETrace[j].msgs
        /\ maxVal  = _TETrace[i].maxVal
        /\ maxVal' = _TETrace[j].maxVal
        /\ maxBal  = _TETrace[i].maxBal
        /\ maxBal' = _TETrace[j].maxBal

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Paxos_TTrace_1681826100.json", _TETrace)

=============================================================================

 Note that you can extract this module `Paxos_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `Paxos_TEExpression.tla` file takes precedence 
  over the module `Paxos_TEExpression` below).

---- MODULE Paxos_TEExpression ----
EXTENDS Sequences, TLCExt, Toolbox, Paxos_TEConstants, Naturals, TLC, Paxos

expression == 
    [
        \* To hide variables of the `Paxos` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        maxVBal |-> maxVBal
        ,msgs |-> msgs
        ,maxVal |-> maxVal
        ,maxBal |-> maxBal
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_maxVBalUnchanged |-> maxVBal = maxVBal'
        
        \* Format the `maxVBal` variable as Json value.
        \* ,_maxVBalJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(maxVBal)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_maxVBalModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].maxVBal # _TETrace[s-1].maxVBal
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE Paxos_TETrace ----
\*EXTENDS IOUtils, Paxos_TEConstants, TLC, Paxos
\*
\*trace == IODeserialize("Paxos_TTrace_1681826100.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Paxos_TETrace ----
EXTENDS Paxos_TEConstants, TLC, Paxos

trace == 
    <<
    ([msgs |-> {},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1)]),
    ([msgs |-> {},maxVal |-> ,maxBal |-> ,maxVBal |-> ])
    >>
----


=============================================================================

---- MODULE Paxos_TEConstants ----
EXTENDS Paxos

CONSTANTS a1, a2, a3, v1, v2

=============================================================================

---- CONFIG Paxos_TTrace_1681826100 ----
CONSTANTS
    Acceptor = { a1 , a2 , a3 }
    Value = { v1 , v2 }
    Quorum = { { a1 , a2 } , { a1 , a3 } , { a2 , a3 } }
    Ballot = { 0 , 1 }
    None = None
    a3 = a3
    a1 = a1
    v2 = v2
    a2 = a2
    v1 = v1
    None = None

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
\* Generated on Tue Apr 18 21:55:00 CST 2023