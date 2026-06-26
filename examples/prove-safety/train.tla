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

\* Ausweichen (DirectedGraph = FALSE)
\* Sections == {1, 2, 3}
\* Edges == {<<1, 2>>, <<1, 3>>, <<2, 3>>}
\* Intersections == {}

Phases == {"finding arrangement", "driving trains"}

VARIABLES phase, section_occ, trains
vars == <<phase, section_occ, trains>> \* needed for fairness

IsSafe(mytrains, my_occ) ==
    /\ ~(\E ta, tb \in DOMAIN mytrains: ta /= tb /\ mytrains[ta].position = mytrains[tb].position)
    /\ \A int \in Intersections: Cardinality({t \in DOMAIN mytrains: mytrains[t].position \in int}) <= 1
    /\ \A s \in Sections: ((\E t \in DOMAIN mytrains: mytrains[t].position = s) <=> my_occ[s] = TRUE)

AllTrains ==
    [1..NumTrains -> [position: Sections, destination: Sections]]
    \* all mappings from 1..NumTrains to train records that hold a position and destination which are both a section

AllOccupations ==
    [Sections -> BOOLEAN] \* all mappings between any Section to any Boolean

DirectionCorrectedEdges ==
    IF DirectedGraph THEN Edges ELSE Edges \union {<<b, a>> : <<a, b>> \in Edges}

PathExists(start, destination) ==
    LET RECURSIVE Reach(_)
        Reach(reachableset) ==
            LET neighbours == {s \in Sections: (\E <<a, b>> \in DirectionCorrectedEdges: a \in reachableset /\ s = b)}
            IN 
                LET newrs == reachableset \union neighbours
                IN
                    IF newrs = reachableset THEN reachableset \* done!
                    ELSE Reach(newrs)
    IN destination \in Reach({start})

FindStartingArrangement ==
    /\ phase = "finding arrangement"
    /\ \E t \in AllTrains, o \in AllOccupations:
        /\ IsSafe(t, o)
        /\ \A i \in DOMAIN t: PathExists(t[i].position, t[i].destination) \* path exists for every train start->destination
        /\ trains' = t
        /\ section_occ' = o
        /\ phase' = "driving trains"

\* checks if the section is part of any intersection and if that intersection already has a train on it
HasOccupiedIntersection(section) ==
    \E intersection \in Intersections: (
        section \in intersection /\ (\E interelement \in intersection: section_occ[interelement] = TRUE)
    )

\* parameterized because a DriveTrains action that goes over all trains doesn't work well with fairness
\* as we want fairness not only over executing some movement of some train, but fairness per-train so 
\* we can keep a single train from stuttering forever
DriveTrain(ti) ==
    /\ phase = "driving trains"
    /\ \E <<current, next>> \in DirectionCorrectedEdges: (
            /\ section_occ[current] = TRUE /\ section_occ[next] = FALSE /\ trains[ti].position = current
            /\ ~HasOccupiedIntersection(next)
            /\ trains' = [trains EXCEPT ![ti] = [trains[ti] EXCEPT !.position = next]]
            /\ section_occ' = [section_occ EXCEPT ![current] = FALSE, ![next] = TRUE]
        )
    /\ UNCHANGED phase
   
Next ==
    FindStartingArrangement \/ (\E ti \in DOMAIN trains: DriveTrain(ti))
   
Init ==
    /\ phase = "finding arrangement"
    /\ trains = <<>>
    /\ section_occ = [s \in Sections |-> FALSE]

Fairness ==
    \* i would like to use DOMAIN trains here as well to keep flexibility but tla+ doesnt allow it
    /\ \A ti \in 1..NumTrains: WF_vars(DriveTrain(ti))

Spec ==
    Init /\ [][Next]_vars /\ Fairness

IsSafeInvariant ==
    IsSafe(trains, section_occ)

TypeInvariant ==
    /\ phase \in Phases
    /\ section_occ \in AllOccupations
    /\ Len(trains) = 0 \/ trains \in AllTrains

AllReachDestinationEventually ==
    /\ []<>(\A i \in DOMAIN trains: trains[i].position = trains[i].destination)

=============================================================================