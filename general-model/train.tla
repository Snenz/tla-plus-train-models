------------------------------- MODULE train -------------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* if this is TRUE, we assume Edges is given in directed graph form,
\* so any Edge <<a, b>> can only be traveled along from a to b.
\* when FALSE, we create an additional opposite edge for every existing one
CONSTANT DirectedGraph

CONSTANT NumTrains
CONSTANT MaxLongitudinalShift \* worst-case longitudinal error
CONSTANT MinStartingDistance \* the minimal amount of sections between trains for all starting arrangements

\* Kreuzung (DirectedGraph = FALSE)
\* Sections == {1, 2, 3, 4, 5, 6}
\* Edges == {<<1, 2>>, <<2, 3>>, <<4, 5>>, <<5, 6>>}
\* Intersections == {{2, 5}}

\* Test:
Sections == {1, 2, 3, 4, 5}
Edges == {<<1, 2>>, <<3, 4>>, <<4, 5>>}
Intersections == {}

\* Teststrecke mit Ausweichgleis, Kreis und Kreuzung (DirectedGraph = FALSE):
\* Sections == {1, 2, 3, 4, 5, 6, 7, 8}
\* Edges == {<<1, 2>>, <<1, 3>>, <<2, 4>>, <<3, 4>>, <<4, 5>>, <<5, 8>>, <<8, 6>>, <<6, 7>>, <<1, 7>>}
\* Intersections == {{5, 6}}

\* gerade Strecke (DirectedGraph = FALSE)
\* Sections == {1, 2, 3, 4, 5, 6, 7, 8}
\* Edges == {<<1, 2>>, <<2, 3>>, <<3, 4>>, <<4, 5>>, <<5, 6>>, <<6, 7>>, <<7, 8>>}
\* Intersections == {}

VARIABLE trains, green_signals
vars == <<trains, green_signals>>

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
    [TrainIDs -> [position: Sections]]
    \* all mappings from TrainIDs to train records that hold a position which is a section

DriveTrain(ti, next_section) ==
    LET
        edge == <<trains[ti].position, next_section>>
    IN
        \* checking if edge is valid shouldnt be necessary beause we check green_signals already,
        \* which is only a subset of DirectionCorrectedEdges anyways. I guess its good practice though
        /\ edge \in DirectionCorrectedEdges
        /\ edge \in green_signals
        /\ trains' = [trains EXCEPT ![ti] = [trains[ti] EXCEPT !.position = next_section]]
        /\ UNCHANGED <<green_signals>>

\* This defines the rules based on which signals are turned green. For this, we only have per-section
\* measurements available [Sections -> BOOLEAN], but these measurements might be shifted longitudinally.
SignalRules(measurements) ==
    DirectionCorrectedEdges

\* based on the current positions of all trains, this returns every set of mappings [Sections -> BOOLEAN]
\* that can occur according to the implemented error types. in SetSignals we then pick out one of these
\* possible measurement mappings, and use SignalRules to find signals we can safely turn green.
AllMeasurableSensorValues ==
    LET
        \* all within the error bounds possible sets of train positions
        shifted_train_positions ==
            {tp \in [TrainIDs -> Sections]:
                \A ti \in TrainIDs: tp[ti] \in FindNeighboursOf(trains[ti].position, MaxLongitudinalShift)}
    IN
        {[s \in Sections |-> \E ti \in TrainIDs : stp[ti] = s] : stp \in shifted_train_positions}

SetSignals ==
    /\ \E sensor_values \in AllMeasurableSensorValues:
        green_signals' = SignalRules(sensor_values)
    /\ UNCHANGED <<trains>>

Next ==
    \/ \E ti \in TrainIDs:
        \E n \in Sections: DriveTrain(ti, n)
    \/ SetSignals
   
Init ==
    /\ green_signals = {}
    /\ \E t \in AllTrains:
        /\ \A ti \in TrainIDs: 
            \* MinStartingDistance: for each train, there may not be another train that is within MinStartingDistance
            ~\E tj \in TrainIDs \ {ti}:
                t[tj].position \in FindNeighboursOf(t[ti].position, MinStartingDistance)
        /\ IsSafe(t)
        /\ trains = t

\* TODO: find out if assumptions about fairness are correct
Fairness ==
    \* DriveTrain should be SF, because the conditions on which it fires can fluctuate alot based on
    \* the surrounding rail network. with WF, the conditions must stabilize before firing, while
    \* SF guarantees the action fires eventually if conditions are met even once
    \* we now also enforce fairness over all the sections, such that if they can be visited, they will
    /\ \A ti \in TrainIDs:
        \A n \in Sections: SF_vars(DriveTrain(ti, n))
    \* for SetSignals, SF or WF will also produce identical behaviour, because there are no preconditions
    \* that might change again.
    /\ WF_vars(SetSignals)

Spec ==
    Init /\ [][Next]_vars /\ Fairness

IsSafeInvariant ==
    IsSafe(trains)

TypeInvariant ==
    /\ trains \in AllTrains
    /\ green_signals \subseteq DirectionCorrectedEdges

\* TODO: testing
AllReachableSectionsVisited ==
    \A t \in TrainIDs:
        \A s \in Sections:
            s \in FindNeighboursOf(trains[t].position, 1000000) ~> trains[t].position = s

NoTrainStuck ==
    \A t \in TrainIDs :
        \A s \in Sections :
            trains[t].position = s ~> trains[t].position /= s

=============================================================================