Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Relations.Relation_Operators. 
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.

Theorem sound: forall s t, 
  s --> t -> 
  forall u r,
    exists P,
      (encode s u r []) =()> P /\ (P ~~ (encode t u r [])).
Proof.
  intros s t Hred.
  induction Hred.
  - admit.
  - admit.
  - intros u r.
    exists (encode s u r []).
    split.
    * eapply rt_trans.
      + apply rt_step.
        simpl.
        apply RES_TAU.
        apply RES_TAU.
        { apply COM with
            (a := a_out 0)
            (R := Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))))
            (S := Out 0 (Out 0 (Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6)))))).
          - exact 0.
          - discriminate.
          - admit.
          - simpl.
        }  
        
    * apply wb_ref.
Admitted.

Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
  exists P' t,
    P =()> P' /\ (P' ~~ encode t u r []) /\ (s --> t \/ s = t).
Proof.
Admitted.