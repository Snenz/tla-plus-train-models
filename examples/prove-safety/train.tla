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

VARIABLES phase, section_occ, trains

IsSafe(mytrains, my_occ) ==
    /\ ~(\E ta, tb \in DOMAIN mytrains: ta /= tb /\ mytrains[ta].position = mytrains[tb].position)
    /\ \A int \in Intersections: Cardinality({t \in DOMAIN mytrains: mytrains[t].position \in int}) <= 1
    /\ \A s \in Sections: ((\E t \in DOMAIN mytrains: mytrains[t].position = s) <=> my_occ[s] = TRUE)
    
AllTrains ==
    [1..NumTrains -> [position: Sections]] \* all mappings from 1..NumTrains to train records that hold a position
                                           \* that is a section

AllOccupations ==
    [Sections -> BOOLEAN] \* all mappings between any Section to any Boolean

FindStartingArrangement ==
    /\ phase = "finding arrangement"
    /\ \E t \in AllTrains, o \in AllOccupations:
        /\ IsSafe(t, o)
        /\ trains' = t
        /\ section_occ' = o
        /\ phase' = "driving trains"

\* checks if the section is part of any intersection and if that intersection already has a train on it
HasOccupiedIntersection(section) ==
    \E intersection \in Intersections: (
        section \in intersection /\ (\E interelement \in intersection: section_occ[interelement] = TRUE)
    )

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

DriveTrain ==
    /\ phase = "driving trains"
    /\ \E ti \in DOMAIN trains:
        /\ \E <<current, next>> \in DirectionCorrectedEdges: (
                /\ section_occ[current] = TRUE /\ section_occ[next] = FALSE /\ trains[ti].position = current
                /\ ~HasOccupiedIntersection(next)
                /\ trains' = [trains EXCEPT ![ti] = [trains[ti] EXCEPT !.position = next]]
                /\ section_occ' = [section_occ EXCEPT ![current] = FALSE, ![next] = TRUE]
            )
    /\ UNCHANGED phase
   
Next ==
    FindStartingArrangement \/ DriveTrain
   
Init ==
    /\ phase = "finding arrangement"
    /\ trains = <<>>
    /\ section_occ = [s \in Sections |-> FALSE]

IsSafeInvariant ==
    IsSafe(trains, section_occ)

TypeInvariant ==
    /\ phase \in Phases
    /\ section_occ \in AllOccupations
    /\ Len(trains) = 0 \/ trains \in AllTrains

=============================================================================