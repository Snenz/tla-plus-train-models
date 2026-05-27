------------------------------- MODULE train -------------------------------

EXTENDS Naturals, FiniteSets

\* TODO: find a better way to define constants
\* CONSTANTS Sections, Edges, Trains
Sections == {1, 2, 3}
Edges == {<<1, 2>>, <<1, 3>>, <<3, 1>>, <<3, 2>>, <<2, 1>>, <<2, 3>>}
Trains == {<<"A", 1, 3>>, <<"B", 3, 1>>}

VARIABLES section_occ, train_positions

TrainNames == {t[1] : t \in Trains}

IsTrainAtDestination(train) ==
    train_positions[train] = (CHOOSE td \in Trains : td[1] = train)[3]
   
DriveTrain(train) ==
    /\ ~IsTrainAtDestination(train)
    /\ \E <<a, b>> \in Edges: (
        section_occ[a] = TRUE /\ section_occ[b] = FALSE /\ train_positions[train] = a
        /\ train_positions' = [train_positions EXCEPT ![train] = b]
        /\ section_occ' = [section_occ EXCEPT ![a] = FALSE, ![b] = TRUE])
   
Next ==
    /\ \E tname \in TrainNames: DriveTrain(tname)
   
Init ==
    train_positions = [t \in TrainNames |-> (CHOOSE td \in Trains : td[1] = t)[2]]
    /\ section_occ = [s \in Sections |-> \E tname \in TrainNames: train_positions[tname] = s]
    
IsGoalReached ==
    \A tname \in TrainNames: IsTrainAtDestination(tname)

GoalNotReached ==
    ~IsGoalReached

IsSafe ==
    ~(\E tna, tnb \in TrainNames: tna /= tnb /\ train_positions[tna] = train_positions[tnb])

=============================================================================
\* Modification History
\* Last modified Wed May 27 10:08:59 CEST 2026 by amos
\* Created Thu May 21 13:25:09 CEST 2026 by amos
