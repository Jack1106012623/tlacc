---- MODULE TwoPhase_TTrace_1710929337 ----
EXTENDS Sequences, TLCExt, TwoPhase, Toolbox, Naturals, TLC, TwoPhase_TEConstants

_expression ==
    LET TwoPhase_TEExpression == INSTANCE TwoPhase_TEExpression
    IN TwoPhase_TEExpression!expression
----

_trace ==
    LET TwoPhase_TETrace == INSTANCE TwoPhase_TETrace
    IN TwoPhase_TETrace!trace
----

_inv ==
    ~(
        TLCGet("level") = Len(_TETrace)
        /\
        msgs = ({[type |-> "Commit"]})
        /\
        tmState = ("committed")
        /\
        tmPrepared = ({})
        /\
        rmState = ((n1 :> "aborted" @@ n2 :> "committed" @@ n3 :> "working" @@ n4 :> "working" @@ n5 :> "working"))
    )
----

_init ==
    /\ msgs = _TETrace[1].msgs
    /\ rmState = _TETrace[1].rmState
    /\ tmState = _TETrace[1].tmState
    /\ tmPrepared = _TETrace[1].tmPrepared
----

_next ==
    /\ \E i,j \in DOMAIN _TETrace:
        /\ \/ /\ j = i + 1
              /\ i = TLCGet("level")
        /\ msgs  = _TETrace[i].msgs
        /\ msgs' = _TETrace[j].msgs
        /\ rmState  = _TETrace[i].rmState
        /\ rmState' = _TETrace[j].rmState
        /\ tmState  = _TETrace[i].tmState
        /\ tmState' = _TETrace[j].tmState
        /\ tmPrepared  = _TETrace[i].tmPrepared
        /\ tmPrepared' = _TETrace[j].tmPrepared

\* Uncomment the ASSUME below to write the states of the error trace
\* to the given file in Json format. Note that you can pass any tuple
\* to `JsonSerialize`. For example, a sub-sequence of _TETrace.
    \* ASSUME
    \*     LET J == INSTANCE Json
    \*         IN J!JsonSerialize("TwoPhase_TTrace_1710929337.json", _TETrace)

=============================================================================

 Note that you can extract this module `TwoPhase_TEExpression`
  to a dedicated file to reuse `expression` (the module in the 
  dedicated `TwoPhase_TEExpression.tla` file takes precedence 
  over the module `TwoPhase_TEExpression` below).

---- MODULE TwoPhase_TEExpression ----
EXTENDS Sequences, TLCExt, TwoPhase, Toolbox, Naturals, TLC, TwoPhase_TEConstants

expression == 
    [
        \* To hide variables of the `TwoPhase` spec from the error trace,
        \* remove the variables below.  The trace will be written in the order
        \* of the fields of this record.
        msgs |-> msgs
        ,rmState |-> rmState
        ,tmState |-> tmState
        ,tmPrepared |-> tmPrepared
        
        \* Put additional constant-, state-, and action-level expressions here:
        \* ,_stateNumber |-> _TEPosition
        \* ,_msgsUnchanged |-> msgs = msgs'
        
        \* Format the `msgs` variable as Json value.
        \* ,_msgsJson |->
        \*     LET J == INSTANCE Json
        \*     IN J!ToJson(msgs)
        
        \* Lastly, you may build expressions over arbitrary sets of states by
        \* leveraging the _TETrace operator.  For example, this is how to
        \* count the number of times a spec variable changed up to the current
        \* state in the trace.
        \* ,_msgsModCount |->
        \*     LET F[s \in DOMAIN _TETrace] ==
        \*         IF s = 1 THEN 0
        \*         ELSE IF _TETrace[s].msgs # _TETrace[s-1].msgs
        \*             THEN 1 + F[s-1] ELSE F[s-1]
        \*     IN F[_TEPosition - 1]
    ]

=============================================================================



Parsing and semantic processing can take forever if the trace below is long.
 In this case, it is advised to uncomment the module below to deserialize the
 trace from a generated binary file.

\*
\*---- MODULE TwoPhase_TETrace ----
\*EXTENDS IOUtils, TwoPhase, TLC, TwoPhase_TEConstants
\*
\*trace == IODeserialize("TwoPhase_TTrace_1710929337.bin", TRUE)
\*
\*=============================================================================
\*

---- MODULE TwoPhase_TETrace ----
EXTENDS TwoPhase, TLC, TwoPhase_TEConstants

trace == 
    <<
    ([msgs |-> {},tmState |-> "init",tmPrepared |-> {},rmState |-> (n1 :> "working" @@ n2 :> "working" @@ n3 :> "working" @@ n4 :> "working" @@ n5 :> "working")]),
    ([msgs |-> {},tmState |-> "init",tmPrepared |-> {},rmState |-> (n1 :> "aborted" @@ n2 :> "working" @@ n3 :> "working" @@ n4 :> "working" @@ n5 :> "working")]),
    ([msgs |-> {[type |-> "Commit"]},tmState |-> "committed",tmPrepared |-> {},rmState |-> (n1 :> "aborted" @@ n2 :> "working" @@ n3 :> "working" @@ n4 :> "working" @@ n5 :> "working")]),
    ([msgs |-> {[type |-> "Commit"]},tmState |-> "committed",tmPrepared |-> {},rmState |-> (n1 :> "aborted" @@ n2 :> "committed" @@ n3 :> "working" @@ n4 :> "working" @@ n5 :> "working")])
    >>
----


=============================================================================

---- MODULE TwoPhase_TEConstants ----
EXTENDS TwoPhase

CONSTANTS n1, n2, n3, n4, n5

=============================================================================

---- CONFIG TwoPhase_TTrace_1710929337 ----
CONSTANTS
    RM = { n1 , n2 , n3 , n4 , n5 }
    n2 = n2
    n3 = n3
    n1 = n1
    n4 = n4
    n5 = n5

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
\* Generated on Wed Mar 20 18:08:58 CST 2024