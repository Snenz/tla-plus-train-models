------------------------------- MODULE train -------------------------------

EXTENDS Naturals, FiniteSets, Sequences

\* if this is TRUE, we assume Edges is given in directed graph form,
\* so any Edge <<a, b>> can only be traveled along from a to b.
\* when FALSE, we create an additional opposite edge for every existing one
CONSTANT DirectedGraph

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
Trains == {<<"A", <<1, 6, 1>>>>, <<"B", <<4, 6, 4>>>>, <<"C", <<6, 6>>>>}

\* train_routes acts as a queue of destinations, last one stays on queue though
VARIABLES section_occ, train_positions, train_routes

TrainNames == {t[1] : t \in Trains}

IsTrainAtDestination(trainname) ==
    /\ Len(train_routes[trainname]) = 1
    /\ train_positions[trainname] = Head(train_routes[trainname])

\* checks if the section is part of any intersection and if that intersection already has a train on it
HasOccupiedIntersection(section) ==
    \E intersection \in Intersections: (
        section \in intersection /\ (\E interelement \in intersection: section_occ[interelement] = TRUE)
    )

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

DriveTrain(trainname) ==
    \* not necessary (?) and keeps some scenarios from being solved
    \* /\ ~IsTrainAtDestination(trainname)
    /\ \E <<current, next>> \in DirectionCorrectedEdges: (
            /\ section_occ[current] = TRUE /\ section_occ[next] = FALSE /\ train_positions[trainname] = current
            /\ ~HasOccupiedIntersection(next)
            /\ train_positions' = [train_positions EXCEPT ![trainname] = next]
            /\ section_occ' = [section_occ EXCEPT ![current] = FALSE, ![next] = TRUE]
        )
    /\ (
            (Len(train_routes[trainname]) > 1 /\ train_positions[trainname] = Head(train_routes[trainname])
            /\ train_routes' = [train_routes EXCEPT ![trainname] = Tail(train_routes[trainname])])
            \/ UNCHANGED train_routes
        )
   
Next ==
    /\ \E tname \in TrainNames: DriveTrain(tname)
   
Init ==
    /\ train_positions = [tname \in TrainNames |-> (CHOOSE t \in Trains: t[1] = tname)[2][1]]
    /\ section_occ = [s \in Sections |-> \E tname \in TrainNames: train_positions[tname] = s]
    /\ train_routes = [tname \in TrainNames |-> Tail((CHOOSE t \in Trains: t[1] = tname)[2])]

GoalNotReached ==
    ~(\A tname \in TrainNames: IsTrainAtDestination(tname))

IsSafe ==
    /\ ~(\E tna, tnb \in TrainNames: tna /= tnb /\ train_positions[tna] = train_positions[tnb])
    /\ \A intersection \in Intersections: Cardinality({s \in intersection: section_occ[s] = TRUE}) <= 1

=============================================================================
