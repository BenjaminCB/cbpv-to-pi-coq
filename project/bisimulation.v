From Encoding Require Export pi.
From Encoding Require Export encoding.
Require Import Coq.Classes.DecidableClass.
Require Coq.Lists.List.
Require Import Nat.

Definition bisimulation (R : proc -> proc -> Prop) : Prop :=
  forall p q,
    R p q ->
    (forall l p',
        p -( l )> p' ->
        exists q',
          q -( l )> q' /\
          R p' q') /\
    (forall l q',
        q -( l )> q' ->
        exists p',
          p -( l )> p' /\
          R p' q').

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

CoInductive weak_bisimilar : proc -> proc -> Prop :=
| weak_bisim : forall p q,
    (forall l p',
        p -( l )> p' ->
        exists q',
          q =( l )> q' /\
          weak_bisimilar p' q') ->
    (forall l q',
        q -( l )> q' ->
        exists p',
          p =( l )> p' /\
          weak_bisimilar p' q') ->
    weak_bisimilar p q
| weak_reflexive : forall p, weak_bisimilar p p
| weak_trans : forall p q r, weak_bisimilar p q -> weak_bisimilar q r -> weak_bisimilar p r.

Notation "p ~~ q" := (weak_bisimilar p q) (at level 84). 


Compute encode (App (Abs (Force (Var 0))) (Thunk (Val (Var 0)))) 1 2 List.nil.

CoFixpoint weak_bisimilar_Nil_Nil : weak_bisimilar Nil Nil.
Proof. apply weak_reflexive. Qed.


