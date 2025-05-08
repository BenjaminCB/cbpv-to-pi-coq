Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators. 
From Coq Require Import Lia.
Require Import PeanoNat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.
From Encoding Require Export lemmaResEncoding.
From Encoding Require Export soundness.


Lemma app_complete: forall P s v u r,
  (($ App s v; u; r; [] $) -( a_tau )> P) ->
    exists P' t,
      P =()> P' /\
      P' ~~ ($ t; u; r; [] $) /\
      (App s v --> t \/ App s v = t).
Proof.
  intros.
  inversion H. contradiction.
  destruct v.
Admitted.


Lemma force_complete: forall P v u r,
  ($ Force v; u; r; [] $) -( a_tau )> P ->
    exists P' t,
    P =()> P' /\
    P' ~~ ($ t; u; r; [] $) /\
    (Force v --> t \/ Force v = t).
Proof.
Proof.
  intros P v u r Hstep.
  inversion Hstep; subst; try congruence.
  destruct v.

  simpl in *.
  exists ($ Force (Var n); u; r; [] $), (Force (Var n)).
  split.
  inversion H0; subst. congruence.
  simpl. admit.

  split.
  apply wb_ref.
  right. reflexivity.

(*Force Thunk s*)
  simpl in *.
  exists ($ (Force (Thunk s)); u; r; [] $), s.
  split.
  inversion H0; subst. congruence.
  simpl. admit.

  split.
  apply wb.
  split. intros.
  exists p'.
  inversion H.
  split.
  admit.
  apply wb_ref.

  split.
  admit.
  apply wb_ref.
  
  intros.
  simpl.
  admit.

  left. apply FORCE_THUNK.
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
  destruct H5.
  
Admitted.


Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
  exists P' t,
    P =()> P' /\ (P' ~~ encode t u r []) /\ (s --> t \/ s = t).
Proof.
  intros.
  induction s.
  - inversion H.
  - inversion H.
  - apply app_complete. apply H. 
  - apply force_complete. apply H.
  - inversion H.
  - apply tau_step_bind. apply H. apply IHs1. apply IHs2.
Admitted.