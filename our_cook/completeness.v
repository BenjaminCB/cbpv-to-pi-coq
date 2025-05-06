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
  inversion H.
Admitted.
Lemma force_complete: forall P v u r,
  ($ Force v; u; r; [] $) -( a_tau )> P ->
    exists P' t,
    P =()> P' /\
    P' ~~ ($ t; u; r; [] $) /\
    (Force v --> t \/ Force v = t).
Proof.
  intros.
  inversion H.
  congruence.
  destruct v.
  set (t := HELP).  (* a term *)
  set (P' := ($ t; u; r; [] $)).                                (* a proc *)
  exists ($ t; u; r; [] $), t.
  
  split.
  destruct H3.
  admit.
  exists ($ t; u; r; [] $), t.
  exists P. encode (Force (Thunk P)) u r [].

  split. destruct H4.
  apply rt_refl.
  split.
  apply wb.

  split.
  intros.
  (*exists (Force (Var n)).*)
  admit. 
  admit.
  right. reflexivity.

  exists P, (Force v).
  split. destruct H3.
  apply rt_refl.
  split.
  admit.
  right. reflexivity.
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
  - admit.
Admitted.