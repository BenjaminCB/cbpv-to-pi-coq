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
    exact 0.
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
    exact 0.
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
    exact 0.
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
    exact 0.
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    apply rt_refl.
  - eapply wb_trans.
    apply rmIsolatedProc.
    eapply wb_trans.
    do 4 (apply wb_res).
    replace (u + 6) with ((u + 4) + 2) by lia.
    replace (r + 6) with ((r + 4) + 2) by lia.
    apply links.
    fold ((Res ^^ 4) (encode s (u + 4) (r + 4) [])).
    apply res_n_encoding.
Qed.

Lemma bind_base_sound : 
  forall s v u r,
    exists P,
      encode (Bind (Ret v) s) u r [] =()> P /\
      P ~~ encode (s {{extend_subst_lam v Var}}) u r [].
Proof.
  intros s u v r.
  exists Nil.
  split.
  - simpl.
    eapply rt_trans.
    apply rt_step.
    apply RES_TAU.
    apply RES_TAU.
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