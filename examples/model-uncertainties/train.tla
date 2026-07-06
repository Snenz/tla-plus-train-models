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
                \* d = 0 → we're done because of distance
                \* newneighbours is empty → explored entire graph
                IF d = 0 \/ Cardinality(newneighbours) = 0 THEN neighbours ELSE 
                    helper(neighbours \union newneighbours, d - 1)
    IN helper({sec}, depth)

TrainIDs ==
    1..NumTrains

AllTrains ==
    [TrainIDs -> [position: Sections, origin: Sections]]
    \* all mappings from TrainIDs to train records that hold a position and origin which are both a section

FindStartingArrangement ==
    /\ phase = "finding arrangement"
    /\ green_signals' = {}
    /\ \E t \in AllTrains:
        \A ti \in TrainIDs: t[ti].position = t[ti].origin
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
            /\ \E tp \in [TrainIDs -> Sections]:
                \* by tp transmuted positions must still be in the specified radius around the actual position:
                /\ \A ti \in TrainIDs: tp[ti] \in FindNeighboursOf(trains[ti].position, 2)
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
    FindStartingArrangement \/ (\E ti \in TrainIDs: DriveTrain(ti)) \/ SetSignals
   
Init ==
    /\ phase = "finding arrangement"
    /\ trains = <<>>
    /\ green_signals = {}

\* TODO: find out if assumptions about fairness are correct
Fairness ==
    \* for FindStartingArrangement, SF or WF will produce identical behaviour, because the action is
    \* continously enabled from the start and its preconditions will never "flicker"
    /\ WF_vars(FindStartingArrangement)
    \* DriveTrain should be SF, because the conditions on which it fires can fluctuate alot based on
    \* the surrounding rail network. with WF, the conditions must stabilize before firing, while
    \* SF guarantees the action fires eventually if conditions are met even once
    /\ \A ti \in TrainIDs: SF_vars(DriveTrain(ti))
    \* for SetSignals, SF or WF will also produce identical behaviour, because once phase is "driving
    \* trains", preconditions will not change again.
    /\ WF_vars(SetSignals)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

IsSafeInvariant ==
    IsSafe(trains)

TypeInvariant ==
    /\ phase \in Phases
    /\ Len(trains) = 0 \/ trains \in AllTrains
    /\ green_signals \subseteq DirectionCorrectedEdges

NoTrainStuck ==
    \* we need to include the phase here because otherwise we try to access trains before populating it
    \A ti \in TrainIDs: <>(phase = "driving trains" /\ trains[ti].position /= trains[ti].origin)

=============================================================================