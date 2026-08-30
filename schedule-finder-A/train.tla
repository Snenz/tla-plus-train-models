------------------------------- MODULE train -------------------------------

\* Mostly identical to train-pathfinder, but we also define how sections
\* intersect while still not being connected to each other
\* Definition: intersecting sections may not both contain a train at the same time

EXTENDS Naturals, FiniteSets, Sequences

\* TODO: find a better way to define constants
\* CONSTANTS Sections, Edges, Trains
\* Kreuzung
Sections == {1, 2, 3, 4, 5, 6}
Edges == {<<1, 2>>, <<2, 1>>, <<2, 3>>, <<3, 2>>, <<4, 5>>, <<5, 4>>, <<5, 6>>, <<6, 5>>}
Intersections == {<<2, 5>>}
Trains == {<<"A", <<1, 3, 1>>>>, <<"B", <<4, 6, 5>>>>}

VARIABLES section_occ, train_positions, train_stop_index

TrainNames == {t[1] : t \in Trains}

IsTrainAtDestination(train) ==
    LET
        last_stop_index == Len((CHOOSE td \in Trains : td[1] = train)[2])
    IN
        /\ train_stop_index[train] > last_stop_index
        /\ train_positions[train] = (CHOOSE td \in Trains : td[1] = train)[2][last_stop_index]
   
DriveTrain(train) ==
    /\ ~IsTrainAtDestination(train)
    /\ \E <<a, b>> \in Edges: (
        section_occ[a] = TRUE /\ section_occ[b] = FALSE /\ train_positions[train] = a
        /\ ~(\E <<x, y>> \in Intersections: (x = b /\ section_occ[y] = TRUE) \/ (y = b /\ section_occ[x] = TRUE))
        /\ train_positions' = [train_positions EXCEPT ![train] = b]
        /\ section_occ' = [section_occ EXCEPT ![a] = FALSE, ![b] = TRUE])
        /\ \/ /\ (CHOOSE td \in Trains : td[1] = train)[2][train_stop_index[train]] = b
              /\ train_stop_index' = [train_stop_index EXCEPT ![train] = (train_stop_index[train] + 1)]
           \/ UNCHANGED train_stop_index
   
Next ==
    /\ \E tname \in TrainNames: DriveTrain(tname)
   
Init ==
    /\ train_positions = [t \in TrainNames |-> (CHOOSE td \in Trains : td[1] = t)[2][1]]
    /\ section_occ = [s \in Sections |-> \E tname \in TrainNames: train_positions[tname] = s]
    /\ train_stop_index = [t \in TrainNames |-> 2]

GoalNotReached ==
    ~(\A tname \in TrainNames: IsTrainAtDestination(tname))

IsSafe ==
    /\ ~(\E tna, tnb \in TrainNames: tna /= tnb /\ train_positions[tna] = train_positions[tnb])
    /\ ~(\E <<a, b>> \in Intersections: (section_occ[a] = TRUE /\ section_occ[b] = TRUE))

=============================================================================
