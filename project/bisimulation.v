From Encoding Require Export pi.

Reserved Notation "P ~ Q" (at level 70).

Inductive bisimulation : (p q : proc) :=
  | BI_IN1 : 
    forall n m. p -( a_in n m )-> p' -> 
      q -( a_in n m )-> q' /\ 
      q' ~ p

  where "P ~ Q" := (bisimulation P Q).