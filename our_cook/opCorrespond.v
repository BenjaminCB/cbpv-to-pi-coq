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

Lemma link: 
  forall n s u r refs,
    Res (Par (Link 0 n) ($ s ; u ; r ; refs $ [[Nat.iter n lift_subst shift]])) ~~
    $ s ; u ; r ; refs $.
Proof.
Admitted.

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

Lemma substitution:
  forall s v u r refs,
    Res (Par ($ v ; refs $) ($ s ; (u + 1) ; (r + 1) ; refs $)) ~~
    $ (s {{ extend_subst_lam v Var }}) ; u ; r ; refs$.
Proof.
Admitted.

Lemma rmIsolatedProc: forall s u r,
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
  - eapply rt_trans.
    apply rt_step.
    simpl.
    repeat (apply RES_TAU).
    apply COM with
      (a := a_out 1)
      (R := Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))))
      (S := Out 0 (Out 0 (Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6)))))).
    discriminate.
    apply OUT.
    apply IN.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with
      (a := a_in 0)
      (R := Par
        (In 0 (In 1 (encode s 1 0 [])))
        (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]])
      )
      (S := Out 0 (Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6))))).
    discriminate.
    apply REP.
    eapply PAR_L.
    discriminate.
    apply IN.
    simpl.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with
      (a := a_in 0)
      (R := Par
        (In 1 (encode s 1 0 []))
        (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]])
      )
      (S := Out 1 (Par (Link 1 (u + 6)) (Link 0 (r + 6)))).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    simpl.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with
      (a := a_in 1)
      (R := Par
        (encode s 1 0 [])
        (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]] [[shift]])
      )
      (S := Par (Link 1 (u + 6)) (Link 0 (r + 6))).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    apply rt_refl.
    
  - eapply wb_trans.
    apply rmIsolatedProc.
    eapply wb_trans.
    apply wb_con with 
      (c := CRes (CRes (CRes (CRes CHole)))).
    replace (u + 6) with ((u + 4) + 2) by lia.
    replace (r + 6) with ((r + 4) + 2) by lia.
    apply links.
    simpl.
    fold ((Res ^^ 4) (encode s (u + 4) (r + 4) [])).
    apply res_n_encoding.
Qed.

Lemma encode_value_eq :
  forall v refs,
    encode_value v refs = $ v ; refs $.
Proof.
  reflexivity.
Qed.

Lemma pointer_eq t :
  pointer t = Rep (In 0 (In 0 (In 1 t))).
Proof.
  reflexivity.
Qed.

Lemma rmUnreffedRestrictions:
  forall s v u r,
    (Res ^^ 3) (Par ($ v; [] $) ($ s; u + 3; r + 3; [] $)) ~~
    (Res (Par ($ v; [] $) ($ s; u + 1; r + 1; [] $))).
Proof.
Admitted.

Lemma bind_base_sound : 
  forall s v u r,
    exists P,
      encode (Bind (Ret v) s) u r [] =()> P /\
      P ~~ encode (s {{extend_subst_lam v Var}}) u r [].
Proof.
  intros s v u r.
  exists 
    ((Res ^^ 3) (Par ($ v; [] $) (encode s (u + 3) (r + 3) []))).
  split.
  - simpl.
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    eapply COM with (a := a_out 0).
    discriminate.
    apply OUT.
    apply IN.
    apply rt_refl.
  - eapply wb_trans.
    apply rmUnreffedRestrictions.
    apply substitution.
Qed.

Lemma shift_eq:
  forall n,
    shift n = n + 1.
Proof.
  reflexivity.
Qed.

Lemma lift_subst_eq: 
  forall subst,
    lift_subst subst = (0 []> (subst >>> shift)).
Proof.
  reflexivity.
Qed.

Lemma app_base_sound:
  forall s v u r,
    exists P,
      ($ App (Abs s) v; u; r; [] $) =()> P /\
      P ~~ ($ s {{v {}>Var}}; u; r; [] $).
Proof.
  intros s v u r.
  exists 
    ((Res ^^ 9) (Par
      (Par 
        (Link 2 (u + 9))
        (Par (Link 1 (r + 9)) (Link 0 3))
      )
      (Par
        ($ s ; 2 ; 1 ; [(0, 0)]$ [[lift_subst (lift_subst (lift_subst shift))]])
        ($v ; []$ [[lift_subst shift]] [[shift]] [[shift]] [[shift]])
      )
    )).
  split.
  - simpl.
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in 3).
    discriminate.
    apply IN.
    apply PAR_L.
    discriminate.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in 2).
    discriminate.
    apply IN.
    apply PAR_R.
    discriminate.
    simpl.
    rewrite shift_eq.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out 1).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    simpl.
    apply IN.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out 2).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    apply IN.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out 3).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    apply IN.
    
    apply rt_refl.

  - change
      (lift_subst (lift_subst (lift_subst shift)))
    with
      (Nat.iter 3 lift_subst shift).
    (* working towards applyng link *)
    eapply wb_trans.
    apply wb_con with
      (c := CRes (CRes (CRes (CRes (CRes (CRes (CRes (CRes (CRes CHole))))))))).
    eapply wb_trans.
    apply wb_struct.
    apply con_par.
    (* think there might be a problem as link requires the restriction to be moved inwards *)
    eapply wb_par.
    
    
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
  - apply app_base_sound.
  - admit.
Admitted.

Theorem complete: forall s P u r, 
  (encode s u r []) -( a_tau )> P -> 
  exists P' t,
    P =()> P' /\ (P' ~~ encode t u r []) /\ (s --> t \/ s = t).
Proof.
Admitted.