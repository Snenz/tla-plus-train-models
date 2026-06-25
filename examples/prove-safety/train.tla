------------------------------- MODULE train -------------------------------

EXTENDS Naturals, FiniteSets

\* if this is TRUE, we assume Edges is given in directed graph form,
\* so any Edge <<a, b>> can only be traveled along from a to b.
\* when FALSE, we create an additional opposite edge for every existing one
CONSTANT DirectedGraph
CONSTANT NumTrains

\* Kreuzung (DirectedGraph = FALSE)
\* Sections == {1, 2, 3, 4, 5, 6}
\* Edges == {<<1, 2>>, <<2, 3>>, <<4, 5>>, <<5, 6>>}
\* Intersections == {{2, 5}}
\* Trains == {<<"A", <<1, 3>>>>, <<"B", <<4, 6, 5>>>>}

\* Ausweichen und Hintereinanderreihen (DirectedGraph = FALSE)
\* Sections == {1, 2, 3, 4, 5}
\* Edges == {<<1, 2>>, <<2, 4>>, <<2, 3>>, <<3, 4>>, <<5, 4>>}
\* Intersections == {}
\* Trains == {<<"A", <<2, 2>>>>, <<"B", <<5, 1>>>>}

\* triple-T (DirectedGraph = FALSE)
Sections == {1, 2, 3, 4, 5, 6, 7}
Edges == {<<1, 2>>, <<1, 5>>, <<2, 5>>, <<2, 6>>, <<2, 3>>, <<3, 6>>, <<3, 7>>, <<3, 4>>, <<4, 7>>}
Intersections == {}

TrainIds == 1..NumTrains

VARIABLES section_occ, trains

\* checks if the section is part of any intersection and if that intersection already has a train on it
HasOccupiedIntersection(section) ==
    \E intersection \in Intersections: (
        section \in intersection /\ (\E interelement \in intersection: section_occ[interelement] = TRUE)
    )

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

DriveTrain(train) ==
    /\ \E <<current, next>> \in DirectionCorrectedEdges: (
            /\ section_occ[current] = TRUE /\ section_occ[next] = FALSE /\ train.position = current
            /\ ~HasOccupiedIntersection(next)
            /\ train' = [train EXCEPT !.position = next]
            /\ section_occ' = [section_occ EXCEPT ![current] = FALSE, ![next] = TRUE]
        )
   
Next ==
    /\ \E i \in TrainIds: DriveTrain(trains[i])
   
Init ==
    /\ trains = [i \in TrainIds |-> [position |-> 1]]
    /\ section_occ = [s \in Sections |-> \E i \in TrainIds: trains[i].position = s]

IsSafe ==
    /\ ~(\E ta, tb \in TrainIds: ta /= tb /\ trains[ta].position = trains[tb].position)
    /\ \A intersection \in Intersections: Cardinality({s \in intersection: section_occ[s] = TRUE}) <= 1

=============================================================================