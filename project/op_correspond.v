From Encoding Require Export pi.
From Encoding Require Export cbpv.
From Encoding Require Export encoding.
From Encoding Require Export bisimulation.
Require Import Coq.Classes.DecidableClass.
Require Coq.Lists.List.
Require Import Nat.
Require Coq.Lists.List.


Theorem Sound_encoding : 
forall (M N : term) (u r : nat), M --> N -> (exists (P' : proc), (encode M u r List.nil) =(a_tau)> P' /\ (P' ~~ (encode N u r List.nil))). 
Proof. intros. induction H.
  - simpl.
  induction v.
  * simpl.
  Admitted.
