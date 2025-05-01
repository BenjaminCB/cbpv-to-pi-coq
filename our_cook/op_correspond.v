Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators. 
From Coq Require Import Lia.
Require Import PeanoNat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.

Lemma links: forall s n m,
  (Res (Res (Par 
    (encode s 1 0 [])
    (Par
      (Link 1 (n + 2))
      (Link 0 (m + 2))
    )
  ))) ~~
  (encode s n m []).
Proof.
Admitted.

Lemma stuff: forall s u r,
  (Res ^^ 6)
    (Par
       (Par (encode s 1 0 [])
          (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]] [[shift]]))
       (Par (Link 1 (u + 6)) (Link 0 (r + 6)))) ~~ 
  ((Res ^^ 6) (Par
    (encode s 1 0 [])
    (Par (Link 1 (u + 6)) (Link 0 (r + 6)))
  )).
Proof.
Admitted.

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

Lemma force_thunk_sound: 
forall s u r,
  exists P,
    encode (Force (Thunk s)) u r [] =()> P /\ P ~~ encode s u r [].
Proof.
  intros s u r.
  exists ((Res ^^ 6)(Par
    (Par 
      (encode s 1 0 [])
      (Rep
        (In 0 (In 0 (In 1 (encode s 1 0 [])))) 
        [[shift]] [[shift]] [[shift]]
      )
    )
    (Par 
      (Link 1 (u + 6)) 
      (Link 0 (r + 6))
    )
  )).
  split.
  * eapply rt_trans.
    apply rt_step.
    simpl.
    repeat (apply RES_TAU).
    { apply COM with
        (a := a_out 1)
        (R := Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))))
        (S := Out 0 (Out 0 (Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6)))))).
      - exact 0.
      - discriminate.
      - apply OUT.
      - apply IN.
    }
    + { eapply rt_trans.
        - apply rt_step.
          repeat (apply RES_TAU).
          apply COM with
            (a := a_in 0)
            (R := Par
              (In 0 (In 1 (encode s 1 0 [])))
              (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]])
            )
            (S := Out 0 (Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6))))).
          * exact 0.
          * discriminate.
          * apply REP.
            eapply PAR_L.
            + discriminate.
            + apply IN.
          * simpl.
            apply OUT.
        - eapply rt_trans.
          * apply rt_step.
            repeat (apply RES_TAU).
            apply COM with
              (a := a_in 0)
              (R := Par
                (In 1 (encode s 1 0 []))
                (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]])
              )
              (S := Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6)))).
            + exact 0.
            + discriminate.
            + { apply PAR_L.
                - discriminate.
                - apply IN.
              }
            + simpl.
              apply OUT.
         * eapply rt_trans.
           + apply rt_step.
             repeat (apply RES_TAU).
             { apply COM with
                 (a := a_in 1)
                 (R := Par
                   (encode s 1 0 [])
                   (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]] [[shift]])
                 )
                 (S := Par (Link 1 (u + 6)) (Link 0 (r + 6))).
               - exact 0.
               - discriminate.
               - apply PAR_L.
                 * discriminate.
                 * apply IN.
               - apply OUT.
             }
           + apply rt_refl.
     }
  * eapply wb_trans.
    + apply stuff.
    + { eapply wb_trans.
        - do 4 (apply wb_res).
          replace (u + 6) with ((u + 4) + 2) by lia.
          replace (r + 6) with ((r + 4) + 2) by lia.
          apply links.
        - fold ((Res ^^ 4) (encode s (u + 4) (r + 4) [])).
          apply res_n_encoding.
      }
Qed.

Lemma bind_base_sound : 
  forall s v u r,
    exists P,
      encode (Bind (Ret v) s) u r [] =()> P /\
      P ~~ encode (s {{extend_subst_lam v Var}}) u r [].
Proof.
Admitted.

Theorem sound: forall s t, 
  s --> t -> 
  forall u r,
    exists P,
      (encode s u r []) =()> P /\ (P ~~ (encode t u r [])).
Proof.
  intros s t Hred.
  induction Hred.
  - apply bind_base_sound.
  - simpl. admit.
  - apply force_thunk_sound.
  - admit.
  - admit.
Admitted.

Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
  exists P' t,
    P =()> P' /\ (P' ~~ encode t u r []) /\ (s --> t \/ s = t).
Proof.
Admitted.