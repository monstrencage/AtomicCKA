Require Import Setoid.

Class Subsumption {A} := subsume : relation A.
Infix " ⊑ " := subsume (at level 80).