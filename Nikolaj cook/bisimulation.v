From Encoding Require Export pi.
From Encoding Require Export encoding.
Require Import Coq.Classes.DecidableClass.
Require Coq.Lists.List.
Require Import Nat.

Definition bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall (p q : proc),
    R p q ->
    (forall (p' : proc),
        p -(a_tau)> p' ->
        exists (q' : proc),
          q -(a_tau)> q' /\
          R p' q') /\
    (forall q',
        q -(a_tau)> q' ->
        exists p',
          p -(a_tau)> p' /\
          R p' q').
(**
CoInductive bisimilar : proc -> proc -> Prop :=
| bisim : forall p q,
    (forall l p',
        p -( l )> p' ->
        exists q',
          q -( l )> q' /\
          bisimilar p' q') ->
    (forall l q',
        q -( l )> q' ->
        exists p',
          p -( l )> p' /\
          bisimilar p' q') ->
    bisimilar p q.

Definition weak_bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall p q,
    R p q ->
    (forall l p',
        p -( l )> p' ->
        exists q',
          q =( l )> q' /\
          R p' q') /\
    (forall l q',
        q -( l )> q' ->
        exists p',
          p =( l )> p' /\
          R p' q').
**)
Inductive struct_cong : proc -> proc -> Prop :=
  | nil : forall p, struct_cong p (Par p Nil)
  | sym : forall p q, struct_cong (Par p q) (Par q p)
  | sg_ref : forall p, struct_cong p p
  | sg_sym : forall p q, struct_cong p q -> struct_cong q p
  | sg_trans : forall p q r, struct_cong p q -> struct_cong q r -> struct_cong p r
  | sg_rep : forall p, struct_cong (Rep p) (Par p (Rep p)).



CoInductive weak_bisimilar : proc -> proc -> Prop :=
| weak_bisim_tau : forall p q,
    (forall p',
        p -(a_tau)> p' ->
        exists q',
          weak_tau q q' /\
          weak_bisimilar p' q') ->
    (forall q',
        q -(a_tau)> q' ->
        exists p',
          p =()> p' /\
          weak_bisimilar p' q') ->
    weak_bisimilar p q

| weak_reflexive : forall p, weak_bisimilar p p
| weak_trans : forall p q r, weak_bisimilar p q -> weak_bisimilar q r -> weak_bisimilar p r
| weak_sym : forall p q, weak_bisimilar p q -> weak_bisimilar q p
| weak_struct : forall p q, struct_cong p q -> weak_bisimilar p q.

Notation "p ~~ q" := (weak_bisimilar p q) (at level 84). 



Compute encode (App (Abs (Force (Var 0))) (Thunk (Val (Var 0)))) 1 2 List.nil.

Example weak_bisimilar_Nil_Nil : weak_bisimilar Nil Nil.
Proof. apply weak_reflexive. Qed.


Lemma Nil_transition_less_tau : forall P, ~(Nil -(a_tau)> P).
Proof. intros. intro H. inversion H. Qed.

Lemma Nil_transition_less_out : forall P n m, ~(trans_out Nil n m P).
Proof. intros. intro H. inversion H. Qed.

Lemma Weak_Tau_Res : forall (P Q : proc),  P =()> Q -> (Res P) =()> (Res Q).
Proof. intros. induction H.
  - apply TPRE_INTERNAL with (r := Res r) (q := Res q). split. 
 apply RES22. apply H. destruct H. admit. 
      - apply ACTION. apply RES22. auto.
      - apply TAU.
Admitted.

Lemma Weak_Tau_Par : forall (P Q R : proc),  P =()> R -> (Par P Q) =()> (Par R Q).
Proof. intros. induction H.
  - apply TPRE_INTERNAL with (r := Par r Q) (q := Par q Q). split. 
 apply TPAR1. apply H. destruct H. admit. 
      - apply ACTION. apply TPAR1. auto.
      - apply TAU.
Admitted.
