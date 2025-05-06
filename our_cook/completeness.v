Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
  exists P' t,
    P =()> P' /\ (P' ~~ encode t u r []) /\ (s --> t \/ s = t).
Proof.
Admitted.