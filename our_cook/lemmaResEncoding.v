Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators. 
From Coq Require Import Lia.
Require Import PeanoNat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.

Ltac split_on_a_out n :=
  intros a;
  destruct a as [|m|m];
  [ (* a_tau *) | | destruct (Nat.eq_dec m n) ];
  try subst.

Lemma lift_swap_0  : lift_subst swap 0 = 0.
Proof.
  reflexivity.
Qed.
Lemma lift_swap_1  : lift_subst swap 1 = 2.
Proof.
  reflexivity.
Qed.
Lemma lift_swap_2  : lift_subst swap 2 = 1.
Proof.
  reflexivity.
Qed.
Lemma lift_swap_ge : forall k, 2 < k -> lift_subst swap k = k.
Proof.
  intros k Hk.
  unfold lift_subst, extend_subst.
  destruct k as [ | k ];  [ lia | ].
  destruct k as [ | k ];  [ lia | ].
  destruct k as [ | k ];  [ lia | ].
  unfold compose.
  simpl.
  lia.
Qed.
Hint Rewrite lift_swap_0 lift_swap_1 lift_swap_2 lift_swap_ge : subst.

Lemma res_step_equals:
  forall n v p',
    Res (Out (BN (S n)) ($ v; [] $)) -( a_out (BN n) )> p' ->
    p' = Res ($ v; [] $ [[swap]]).
Proof.
Admitted.

Lemma swap_swap_n:
  forall n, swap (swap n) = n.
Proof.
  intros n.
  destruct n.
  reflexivity.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Lemma iter_lift_subst_swap_swap_n:
  forall n m, 
    (Nat.iter n lift_subst swap (Nat.iter n lift_subst swap m)) = m.
Proof.
  intros n.
  induction n.
  
  (* base case *)
  simpl.
  apply swap_swap_n.
  
  (* inductive case *)
  intros m.
  simpl.
  rewrite <- IHn.
Admitted.

Lemma swap_swap_proc:
  forall p, p [[swap]] [[swap]] = p.
Proof.
Admitted.

Lemma res_swap_encode_value:
  forall v,
    Res ($ v ; [] $ [[swap]]) ~~ $ v ; [] $.
Proof.
  intros v.
  destruct v.
  
  (* v is var *)
  simpl.
  unfold pointer.
  unfold compose.
  simpl.
  
  apply wb.
  split.
  
  intros a p' Hstep.
  destruct a.
  
  
  (* v is thunk *)
Admitted.

(* TODO think the refs need to change but lets not say that for now *)
Lemma res_encoding_value:
  forall v u r refs,
    Res ($ Val v; S u; S r; refs $) ~~
    ($ Val v; u; r; refs $).
Proof.
  intros v u r refs.
  simpl.
  apply wb.
  split.
  
  
  (* bisim first clause *)
  intros a.
  destruct a.
  
  (* tau *)
  intros p' Hstep.
  inversion Hstep.
  contradiction.
  inversion H0.
  
  (* in *)
  intros p' Hstep.
  inversion Hstep.
  inversion H1.
Admitted.
(*
  (* out n and n = u *)
  destruct (Nat.eq_dec u n).
  intros p' Hstep.
  subst.
  
  subst.
  exists ($ v; [] $).
  split.
  
  (* transition *)
  eapply WT_VIS.
  discriminate.
  apply rt_refl.
  apply OUT.
  apply rt_refl.
  eapply res_step_equals in Hstep.
  inversion Hstep.
  
  (* further bisim *)
  apply res_swap_encode_value.
  
  (* out n and n <> u *)
  intros p' Hstep.
  inversion Hstep.
  inversion H1.
  contradiction.
  
  (* bisim second clause *)
Admitted.

*)

(* TODO think the refs need to change but lets not say that for now *)
Lemma res_encoding: forall s u r refs,
  (Res (encode s (S u) (S r) refs)) ~~ (encode s u r refs).
Proof.
  cofix CH.
  intros s.
  induction s.
  - apply res_encoding_value.
  - admit.
Admitted.

(* TODO think the refs need to change but lets not say that for now *)
Lemma res_n_encoding:
forall n s u r refs,
  ((Res ^^ n) (encode s (n + u) (n + r) refs)) ~~ (encode s u r refs).
Proof.
  intros n.
  induction n.
  - intros s u r refs.
    simpl.
    replace (u + 0) with u by lia.
    replace (r + 0) with r by lia.
    apply wb_ref.
  - intros s u r refs.
    eapply wb_trans.
    * simpl.
      replace (S (n + u)) with (n + S u) by lia.
      replace (S (n + r)) with (n + S r) by lia.
      apply wb_con with (c := CRes (CHole)).
      apply IHn.
    * apply res_encoding.
Qed.