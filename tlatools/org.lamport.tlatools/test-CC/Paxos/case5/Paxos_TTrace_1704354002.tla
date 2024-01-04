---- MODULE Paxos_TTrace_1704354002 ----
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
        msgs = ({[type |-> "2a", bal |-> 0, val |-> v1], [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1]})
        /\
        maxVal = ((a1 :> None @@ a2 :> None @@ a3 :> None))
        /\
        maxBal = ((a1 :> 0 @@ a2 :> 0 @@ a3 :> -1))
        /\
        maxVBal = ((a1 :> 0 @@ a2 :> -1 @@ a3 :> -1))
        /\
        msgsBak = ({[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]})
    )
----

_init ==
    /\ maxVal = _TETrace[1].maxVal
    /\ maxVBal = _TETrace[1].maxVBal
    /\ msgs = _TETrace[1].msgs
    /\ msgsBak = _TETrace[1].msgsBak
    /\ maxBal = _TETrace[1].maxBal
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ maxVal  = _TETrace[i].maxVal
        /\ maxVal' = _TETrace[j].maxVal
        /\ maxVBal  = _TETrace[i].maxVBal
        /\ maxVBal' = _TETrace[j].maxVBal
        /\ msgs  = _TETrace[i].msgs
        /\ msgs' = _TETrace[j].msgs
        /\ msgsBak  = _TETrace[i].msgsBak
        /\ msgsBak' = _TETrace[j].msgsBak
        /\ maxBal  = _TETrace[i].maxBal
        /\ maxBal' = _TETrace[j].maxBal

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("Paxos_TTrace_1704354002.json", _TETrace)

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
        maxVal |-> maxVal
        ,maxVBal |-> maxVBal
        ,msgs |-> msgs
        ,msgsBak |-> msgsBak
        ,maxBal |-> maxBal
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_maxValUnchanged |-> maxVal = maxVal'
        
        \* Format the `maxVal` variable as Json value.
        \* ,_maxValJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(maxVal)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_maxValModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].maxVal # _TETrace[s-1].maxVal
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
\*trace == IODeserialize("Paxos_TTrace_1704354002.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE Paxos_TETrace ----
EXTENDS Paxos_TEConstants, TLC, Paxos

trace == 
    <<
    ([msgs |-> {},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {}]),
    ([msgs |-> {},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {}]),
    ([msgs |-> {[type |-> "1a", bal |-> 0]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0]}]),
    ([msgs |-> {[type |-> "1a", bal |-> 0]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0]}]),
    ([msgs |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "2a", bal |-> 0, val |-> v1]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "2a", bal |-> 0, val |-> v1]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> -1 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}]),
    ([msgs |-> {[type |-> "2a", bal |-> 0, val |-> v1], [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1]},maxVal |-> (a1 :> None @@ a2 :> None @@ a3 :> None),maxBal |-> (a1 :> 0 @@ a2 :> 0 @@ a3 :> -1),maxVBal |-> (a1 :> 0 @@ a2 :> -1 @@ a3 :> -1),msgsBak |-> {[type |-> "1a", bal |-> 0], [type |-> "2a", bal |-> 0, val |-> v1], [type |-> "2b", bal |-> 0, acc |-> a1, val |-> v1], [type |-> "1b", bal |-> 0, acc |-> a1, mbal |-> -1, mval |-> None], [type |-> "1b", bal |-> 0, acc |-> a2, mbal |-> -1, mval |-> None]}])
    >>
----


=============================================================================

---- MODULE Paxos_TEConstants ----
EXTENDS Paxos

CONSTANTS a1, a2, a3, v1, v2

=============================================================================

---- CONFIG Paxos_TTrace_1704354002 ----
CONSTANTS
    Acceptor = { a1 , a2 , a3 }
    Value = { v1 , v2 }
    Quorum <- MCQuorum
    Ballot <- MCBallot
    None = None
    Ballot <- [ Voting ] MCBallot
    a1 = a1
    a2 = a2
    a3 = a3
    v1 = v1
    v2 = v2
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
\* Generated on Thu Jan 04 15:40:03 CST 2024