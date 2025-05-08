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
  unfold shift.
  lia.
Qed.
Hint Rewrite lift_swap_0 lift_swap_1 lift_swap_2 lift_swap_ge : subst.

Lemma res_step_equals:
  forall n v p',
    Res (Out (n + 1) ($ v; [] $)) -( a_out n )> p' ->
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
  unfold shift.
  simpl.
  unfold pointer.
  
  apply wb.
  split.
  
  intros a p' Hstep.
  destruct a.
  
  
  (* v is thunk *)
Admitted.

Lemma res_encoding_value:
  forall v u r,
    Res ($ Val v; u + 1; r + 1; [] $) ~~
    ($ Val v; u; r; [] $).
Proof.
  intros v u r.
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
  unfold shift in H7.
  replace (u + 1) with (S u) in H7 by lia.
  replace (n + 1) with (S n) in H7 by lia.
  apply Nat.succ_inj in H7.
  contradiction.
  
  (* bisim second clause *)
Admitted.

Lemma res_encoding: forall s u r,
  (Res (encode s (u + 1) (r + 1) [])) ~~ (encode s u r []).
Proof.
  cofix CH.
  intros s.
  induction s.
  - apply res_encoding_value.
  - admit.
Admitted.

Lemma res_n_encoding:
forall n s u r,
  ((Res ^^ n) (encode s (u + n) (r + n) [])) ~~ (encode s u r []).
Proof.
  intros n.
  induction n.
  - intros s u r.
    simpl.
    replace (u + 0) with u by lia.
    replace (r + 0) with r by lia.
    apply wb_ref.
  - intros s u r.
    eapply wb_trans.
    * simpl.
      replace (u + S n) with ((u + 1) + n) by lia.
      replace (r + S n) with ((r + 1) + n) by lia.
      apply wb_con with (c := CRes (CHole)).
      apply IHn.
    * apply res_encoding.
Qed.