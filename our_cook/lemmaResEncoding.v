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

Lemma res_encoding: forall s u r,
  (Res (encode s (u + 1) (r + 1) [])) ~~ (encode s u r []).
Proof.
  cofix CH.
  intros s.
  induction s.
  - induction v.
    * intros u r.
      simpl.
      apply wb.
      split.
      + { split_on_a_out u.
          - intros p' Htrans.
            inversion Htrans.
            contradiction.
            inversion H0.
          - intros p' Htrans.
            inversion Htrans.
            inversion H1.
          - intros p' Htrans.
            exists 
                (Rep (In 0 (In 0 (In 1 (In (n + 4)
                  (In 0 (In 1 (Par (Link 1 4) (Link 0 3))))))))).
              split.
              + eapply WT_VIS.
                discriminate.
                apply rt_refl.
                apply OUT.
                apply rt_refl.
              + inversion Htrans.
                subst.
                inversion H1.
                subst.
                simpl.
                unfold compose, lift_subst, extend_subst, shift.
                simpl.
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
      apply wb_res.
      apply IHn.
    * apply res_encoding.
Qed.