Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators. 
From Coq Require Import Lia.
Require Import PeanoNat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.


Lemma app_complete: forall P s v u r,
  (($ App s v; u; r; [] $) -( a_tau )> P) ->
    exists P' t,
      P =()> P' /\
      P' ~~ ($ t; u; r; [] $) /\
      (App s v --> t \/ App s v = t).
Proof.
  intros P s v u r Hstep.
  inversion Hstep. contradiction. subst.
  inversion H0. contradiction. subst.
  inversion H1. contradiction. subst.
  inversion H2. contradiction. subst.
  inversion H3. contradiction. contradiction. subst.
  inversion H4. subst.
  inversion H4. contradiction. contradiction. subst.
(* H5 / R0 skal være ukendt da det er en videre enkodning, som helt korrekt er ukendt*)
  inversion H5. contradiction. contradiction. subst. (* ligner rigtig meget noget man kan få i bind og app *)
  destruct v.
  destruct n.
  simpl.
  (* admit goals with terms that are not well formed *)
  destruct s.
(*Sker noget sjovt med H*)
  destruct H.
(*Får en H5 man kan bruge, har godtnok lidt mange cases*)
(*Nået hertil^^*)

(*
  eexists. eexists.
  - split.
    simpl.

    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 0)).
    apply REP.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
*)
Admitted.

Lemma force_complete: forall v u r P,
  ($ Force v; u; r; [] $) -( a_tau )> P ->
    exists P' t,
    P =()> P' /\
    P' ~~ ($ t; u; r; [] $) /\
    (Force v --> t \/ Force v = t).
Proof.
  intros v u r p Hstep.
  inversion Hstep.
  contradiction.
  inversion H0.
  contradiction.
  subst.
  inversion H3.
  subst.
  contradiction.
  contradiction.
  subst.
  inversion H1.
  subst. (* ! *)
  inversion H1.
  subst.
  inversion H4.
  inversion H5.
  subst.
  
  eexists.
  eexists.
  split.
  - destruct v.
    destruct n.
    simpl.
    unfold pointer.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 0)).
    discriminate.
    apply REP.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 0)).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 1)).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply PAR_L.

    
    
  
  
  
  
Admitted.


Lemma tau_step_bind : forall s1 s2 u r P,
    ($ Bind s1 s2; u; r; [] $) -(a_tau)> P ->
    ( ($ s1; u; r; [] $) -(a_tau)> P ->
      exists (P1 : proc) (t1 : term),
        P =()> P1 /\ P1 ~~ ($ t1; u; r; [] $) /\ (s1 --> t1 \/ s1 = t1) ) ->
    ( ($ s2; u; r; [] $) -(a_tau)> P ->
      exists (P2 : proc) (t2 : term),
        P =()> P2 /\ P2 ~~ ($ t2; u; r; [] $) /\ (s2 --> t2 \/ s2 = t2) ) ->
    exists (P' : proc) (t : term),
      P =()> P' /\ P' ~~ ($ t; u; r; [] $) /\ (Bind s1 s2 --> t \/ Bind s1 s2 = t).
Proof.
  intros.
  inversion H. congruence.
  inversion H3. contradiction. subst.
  inversion H6. contradiction. contradiction. subst.
  inversion H4. contradiction. contradiction. subst.
  (*Ligner meget app*)

  eexists. eexists.
  split.
  - eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU). simpl.
    apply COM with (a := a_in (BN 0)).
    discriminate.
    apply PAR_R_TAU.
    apply REP.
    discriminate.
    apply IN.
    apply OUT.
    
  admit.
Admitted.



Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
    exists P' t,
      P =()> P' /\
      P' ~~ encode t u r [] /\
      (s --> t \/ s = t).
Proof.
  intros s P u r H.
  induction s as [| | s1 IH1 s2 IH2 | v | |].
  - inversion H.
  - inversion H.
  - apply app_complete; auto.
  - apply force_complete; auto.
  - inversion H.
  - apply tau_step_bind; auto.
Qed.