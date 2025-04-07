From Encoding Require Export pi.
From Encoding Require Export cbpv.
From Encoding Require Export encoding.
From Encoding Require Export bisimulation.
Require Import Coq.Classes.DecidableClass.
Require Coq.Lists.List.
Require Import Nat.
Require Coq.Lists.List.

Lemma res_prefix_in : forall (P : proc) (V : value) (n: nat) (ref : List.list (nat * nat)),
  Res(Par (In n P) (encode_value V ref)) ~~ In n (Res(Par (P) (encode_value V ref))).
Proof. Admitted.

Lemma res_prefix_out : forall (P : proc) (V : value) (n m: nat) (ref : List.list (nat * nat)),
 ~(m = 0) -> (Res(Par (Out n m P) (encode_value V ref)) ~~ In n (Res(Par (P) (encode_value V ref)))).
Proof. Admitted.

Lemma pointer : forall (P Q : proc) (x y : nat) (V : value) (ref : List.list (nat * nat)),
  Res (Par (Par (P) (Q)) (encode_value V ref)) ~~ 
  Res (Res (Par 
            (Par ((P[[shift]])[[swap]]) (Q[[shift]]) ) 
            (Par (((encode_value V (incRefs 0 1 ref))[[shift]])[[swap]]) ((encode_value V (incRefs 0 1 ref))[[shift]])))).
Proof. Admitted.

Lemma res_rep : forall (P : proc) (V : value) (ref : List.list (nat * nat)),
Res( Par (Rep (P)) (encode_value V ref) ) ~~ Rep (Res (Par (P) (encode_value V ref))).
Proof. Admitted.

Lemma sub_lemma : forall (M : term) (V : value) (u r : nat) (ref : List.list (nat * nat)),
encode (M [l[(extend_subst_lam V Var)]l]) u r ref ~~ Res ( Par ((encode M (u+1) (r+1) (incRefs 0 1 ref))) (encode_value V ref)).  
Proof. Admitted.

Theorem Sound_encoding : 
forall (M N : term) (u r : nat), M --> N -> (exists (P' : proc), (encode M u r List.nil) =(a_tau)> P' 
  /\ (P' ~~ (encode N u r List.nil))). 
Proof. intros. induction H.
  - simpl.
  induction v. 
  * simpl.
  exists (Res(Res(
    (Par
       (Res
          
             ((Rep (In 0 (Out (n + 1) 0 Nil))[[swap]])))
       (
          (encode s (u + 2) (r + 2)
             ((0, 0) :: Datatypes.nil)[[0 |> id]])))))).
    split.
    + apply ACTION. apply RES22. apply COM22 with (n := 0).
      apply RESBOUT. apply RES1. apply OUT.
      apply IN.
    +

  Admitted.

Theorem Complete_encoding : 
forall (M : term) (P : proc) (u r : nat), (encode M u r List.nil) -(a_tau)> P 
  -> (exists (P' : proc) (N : term),  P =(a_tau)> P' 
  /\ (P' ~~ (encode N u r List.nil)) /\ (M --> N \/ M = N)).
Proof. intro. induction M. intros.
  - induction H. 
  * 
  Admitted.


