------------------------------- MODULE train -------------------------------

\* idea: first an action finds a valid starting point, then all possible train movements are executed

EXTENDS Naturals, FiniteSets, Sequences

\* if this is TRUE, we assume Edges is given in directed graph form,
\* so any Edge <<a, b>> can only be traveled along from a to b.
\* when FALSE, we create an additional opposite edge for every existing one
CONSTANT DirectedGraph
CONSTANT NumTrains

\* Kreuzung (DirectedGraph = FALSE)
Sections == {1, 2, 3, 4, 5, 6}
Edges == {<<1, 2>>, <<2, 3>>, <<4, 5>>, <<5, 6>>}
Intersections == {{2, 5}}

Phases == {"finding arrangement", "driving trains"}

VARIABLE phase, trains, green_signals
vars == <<phase, trains, green_signals>>

IsSafe(mytrains) ==
    \* no two trains on same section:
    /\ ~(\E ta, tb \in DOMAIN mytrains: ta /= tb /\ mytrains[ta].position = mytrains[tb].position)
    \* no more than 1 train at a time in an intersection:
    /\ \A int \in Intersections: Cardinality({t \in DOMAIN mytrains: mytrains[t].position \in int}) <= 1

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

FindNeighboursOf(sec, depth) ==
    LET RECURSIVE helper(_, _)
        helper(neighbours, d) ==
            LET 
                newneighbours == {s \in Sections:
                    (\E <<a, b>> \in DirectionCorrectedEdges: a \in neighbours /\ ~(b \in neighbours) /\ s = b)}
            IN
                IF d = 0 THEN neighbours ELSE 
                    helper(neighbours \union newneighbours, d - 1)
    IN helper({sec}, depth)

AllTrains ==
    [1..NumTrains -> [position: Sections]]
    \* all mappings from 1..NumTrains to train records that hold a position which is a section

FindStartingArrangement ==
    /\ phase = "finding arrangement"
    /\ green_signals' = {}
    /\ \E t \in AllTrains:
        /\ IsSafe(t)
        /\ trains' = t
        /\ phase' = "driving trains"

DriveTrain(ti) ==
    /\ phase = "driving trains"
    /\ \E <<current, next>> \in DirectionCorrectedEdges: (
            /\ trains[ti].position = current
            /\ <<current, next>> \in green_signals
            /\ trains' = [trains EXCEPT ![ti] = [trains[ti] EXCEPT !.position = next]]
        )
    /\ UNCHANGED <<phase, green_signals>>

\* This defines the rules based on which signals are turned green. For this, we only have per-section
\* measurements available [Sections -> BOOLEAN], but these measurements might be shifted longitudinally
\* or be outdated.
SignalRules(measurements) ==
    {}
    \* returns list of green signals

\* based on the current positions of all trains, this returns every set of mappings [Sections -> BOOLEAN]
\* that can occur according to the implemented error types. in SetSignals we then pick out one of these
\* possible measurement mappings, and use SignalRules to find signals we can safely turn green.
AllMeasurableSensorValues ==
    LET
        IsValidSensorValues(vals) ==
            \* is there a mapping that transmutes each trains position to a neighbouring section,
            \* that corresponds to vals?
            /\ \E tp \in [DOMAIN trains -> Sections]:
                \* by tp transmuted positions must still be in the specified radius around the actual position:
                /\ \A ti \in DOMAIN trains: tp[ti] \in FindNeighboursOf(trains[ti].position, 2)
                \* create the mapping from Sections -> BOOLEAN based on tp and check if it is vals
                /\ [s \in Sections |-> \E ti \in DOMAIN trains: tp[ti] = s] = vals
    IN
        {s \in [Sections -> BOOLEAN]: IsValidSensorValues(s)}

SetSignals ==
    /\ phase = "driving trains"
    /\ \E sensor_values \in AllMeasurableSensorValues:
        /\ green_signals' = SignalRules(sensor_values)
    /\ UNCHANGED <<trains, phase>>

Next ==
    FindStartingArrangement \/ (\E ti \in DOMAIN trains: DriveTrain(ti)) \/ SetSignals
   
Init ==
    /\ phase = "finding arrangement"
    /\ trains = <<>>
    /\ green_signals = {}

Fairness ==
    \* i would like to use DOMAIN trains here as well to keep flexibility but tla+ doesnt allow it
    /\ \A ti \in 1..NumTrains: WF_vars(DriveTrain(ti))
    /\ WF_vars(SetSignals)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

IsSafeInvariant ==
    IsSafe(trains)

TypeInvariant ==
    /\ phase \in Phases
    /\ Len(trains) = 0 \/ trains \in AllTrains
    /\ green_signals \subseteq DirectionCorrectedEdges

=============================================================================