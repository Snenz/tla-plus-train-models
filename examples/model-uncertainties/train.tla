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
vars == <<trains, green_signals>>

IsSafe(mytrains) ==
    \* no two trains on same section:
    /\ ~(\E ta, tb \in DOMAIN mytrains: ta /= tb /\ mytrains[ta].position = mytrains[tb].position)
    \* no more than 1 train at a time in an intersection:
    /\ \A int \in Intersections: Cardinality({t \in DOMAIN mytrains: mytrains[t].position \in int}) <= 1

AllTrains ==
    [1..NumTrains -> [position: Sections]]
    \* all mappings from 1..NumTrains to train records that hold a position and destination which are both a section

FindStartingArrangement ==
    /\ phase = "finding arrangement"
    /\ green_signals' = {}
    /\ \E t \in AllTrains:
        /\ IsSafe(t)
        /\ trains' = t
        /\ phase' = "driving trains"

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

DriveTrain(ti) ==
    /\ phase = "driving trains"
    /\ \E <<current, next>> \in DirectionCorrectedEdges: (
            /\ trains[ti].position = current
            /\ <<current, next>> \in green_signals
            /\ trains' = [trains EXCEPT ![ti] = [trains[ti] EXCEPT !.position = next]]
        )
    /\ UNCHANGED <<phase, green_signals>>

AllowedNeighbourEdges(position) ==
    {<<a, b>> \in DirectionCorrectedEdges:
        /\ a = position
        /\ ~(\E <<x, y>> \in green_signals: y = b)}

SetSignals ==
    /\ phase = "driving trains"
    /\ green_signals' = UNION {AllowedNeighbourEdges(trains[ti].position): ti \in DOMAIN trains}
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