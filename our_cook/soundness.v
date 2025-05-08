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

Lemma link_lift: 
  forall n s u r refs,
    Res (Par (Link 0 n) ($ s ; u + 1 ; r + 1 ; refs $ [[Nat.iter n lift_subst shift]])) ~~
    $ s ; u ; r ; refs $.
Proof.
Admitted.

Lemma link_handlers: forall s n m refs,
  (Res (Res (Par 
    (encode s 1 0 refs)
    (Par
      (Link 1 (n + 2))
      (Link 0 (m + 2))
    )
  ))) ~~
  (encode s n m refs).
Proof.
Admitted.

Lemma encode_reach: 
  forall n s u r,
    n <> u -> n <> r -> ref_n_in_proc n ($ s ; u ; r ; [] $) = false.
Proof.
Admitted.

Lemma substitution:
  forall s v u r,
    Res (Par ($ v ; [] $) ($ s ; (u + 1) ; (r + 1) ; [(0,0)] $)) ~~
    $ (s {{ extend_subst_lam v Var }}) ; u ; r ; []$.
Proof.
Admitted.

Lemma ref_n_in_proc_shift:
  forall p,
    ref_n_in_proc 0 (p[[shift]]) = false.
Proof.
Admitted.

Lemma shift_extend_proc:
  forall p,
    (p [[shift]] [[0 []> id]]) = p.
Proof.
Admitted.

Lemma res_rep_in_0:
  forall p,
    Res (Rep (In 0 p)) ~~ Nil.
Proof.
Admitted.

Lemma rmIsolatedProc: forall s u r,
  (Res ^^ 6)
    (Par
       (Par (encode s 1 0 [])
          (Rep (In 0 (In 0 (In 1 (encode s 1 0 [])))) [[shift]] [[shift]] [[shift]]))
       (Par (Link 1 (u + 6)) (Link 0 (r + 6)))) ~~ 
  ((Res ^^ 5) (Par
    (encode s 1 0 [])
    (Par (Link 1 (u + 5)) (Link 0 (r + 5)))
  )).
Proof.
  intros s u r.
  eapply wb_trans.
  apply wb_struct.
  repeat (apply con_res).
  eapply sg_trans.
  apply par_flatten.
  eapply sg_trans.
  apply con_par.
  eapply sg_trans.
  apply con_par.
  apply sym.
  apply sg_ref.
  apply par_assoc.
  apply sg_ref.
  apply par_assoc.
  
  apply wb_con with 
    (c := CRes (CRes CHole)).
  eapply wb_trans.
  apply wb_struct.
  do 3 (apply con_res).
  apply sg_par_res_r.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  eapply wb_trans.
  apply wb_struct.
  do 2 (apply con_res).
  apply sg_par_res_r.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  eapply wb_trans.
  apply wb_struct.
  apply con_res.
  apply sg_par_res_r.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  
  eapply wb_trans.
  apply wb_struct.
  apply sg_par_res_l.
  replace (u + 6) with (6 + u) by lia.
  replace (r + 6) with (6 + r) by lia.
  simpl.
  rewrite encode_reach.
  reflexivity.
  discriminate.
  discriminate.
  
  eapply wb_trans.
  apply wb_par.
  apply res_rep_in_0.
  apply wb_ref.
  
  eapply wb_trans.
  apply wb_struct.
  eapply sg_trans.
  apply sym.
  apply del_nil.
  
  
Admitted.

Lemma force_thunk_sound: 
forall s u r,
  exists P,
    encode (Force (Thunk s)) u r [] =()> P /\ P ~~ encode s u r [].
Proof.
  intros s u r.
  eexists.
  split.
  - eapply rt_trans.
    apply rt_step.
    simpl.
    repeat (apply RES_TAU).
    eapply COM with (a := a_out 1).
    discriminate.
    apply OUT.
    apply IN.
    
    eapply rt_trans.
    unfold pointer.
    apply rt_step.
    repeat (apply RES_TAU).
    eapply COM with (a := a_in 0).
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
    eapply COM with (a := a_in 0).
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
      (c := CRes (CRes (CRes CHole))).
    replace (u + 5) with ((u + 3) + 2) by lia.
    replace (r + 5) with ((r + 3) + 2) by lia.
    apply link_handlers.
    simpl.
    fold ((Res ^^ 3) (encode s (u + 3) (r + 3) [])).
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
    (Res ^^ 3) (Par ($ v; [] $) ($ s; u + 3; r + 3; [(0,0)] $)) ~~
    (Res (Par ($ v; [] $) ($ s; u + 1; r + 1; [(0,0)] $))).
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
    ((Res ^^ 3) (Par ($ v; [] $) (encode s (u + 3) (r + 3) [(0,0)]))).
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

Lemma ref_n_in_proc_0_shift:
  forall p, ref_n_in_proc 0 (p[[shift]]) = false.
Proof.
  intros p.
  induction p.
Admitted.

Lemma shift_extend_id_n:
  forall n, (0 []> id) (shift n) = n.
Proof.
  intros n.
  induction n.
  reflexivity.
  simpl.
  replace (n + 1) with (S n) by lia.
  unfold id.
  reflexivity.
Qed.

Lemma shift_extend_id_proc: 
  forall p, (p [[shift]] [[0 []> id]]) = p.
Proof.
  intros.
  induction p.
  simpl.
  rewrite shift_extend_id_n.
Admitted.

Lemma we_need_this_but_is_hard:
  forall s v u r,
    Res (Par 
      ($ v; [] $ [[lift_subst shift]])
      ($ s; u + 1; r + 1; [(0, 0)] $)
    ) ~~
    (Par 
      ($ v; [] $)
      ($ s; u; r; [(0, 0)] $)
    ).
Proof.
Admitted.

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
      (c := (CRes (CRes (CRes (CRes (CRes (CRes (CRes (CRes CHole))))))))).
    eapply wb_trans.
    apply wb_struct.
    apply con_res.
    apply con_par.
    apply sym.
    apply sg_ref.
    eapply wb_trans.
    apply wb_struct.
    apply con_res.
    apply con_par.
    apply con_par.
    apply sym.
    apply sg_ref.
    apply sg_ref.
    eapply wb_trans.
    apply wb_struct.
    apply con_res.
    apply con_par.
    apply par_assoc.
    apply sg_ref.
    eapply wb_trans.
    apply wb_struct.
    apply con_res.
    apply par_swap.
    eapply wb_trans.
    apply wb_struct.
    apply sg_par_res_l.
    replace (u + 9) with (9 + u) by lia.
    replace (r + 9) with (9 + r) by lia.
    simpl.
    apply ref_n_in_proc_0_shift.
    apply wb_par.
    replace 1 with (0 + 1) by lia.
    replace (S (0 + 1)) with (1 + 1) by lia.
    apply link_lift.
    apply wb_ref.
    simpl.
    
    eapply wb_trans.
    apply wb_con with
      (c := (CRes (CRes (CRes (CRes (CRes (CRes CHole))))))).
    eapply wb_trans.
    apply wb_struct.
    repeat (apply con_res).
    eapply sg_trans.
    apply con_par.
    apply sg_ref.
    apply sym.
    eapply sg_trans.
    apply sym.
    apply par_assoc.
    eapply wb_trans.
    apply wb_struct.
    eapply sg_trans.
    apply con_res.
    apply sg_par_res_r.
    rewrite shift_extend_id_proc.
    apply ref_n_in_proc_0_shift.
    apply sg_par_res_r.
    repeat (rewrite shift_extend_id_proc).
    apply ref_n_in_proc_0_shift.
    apply wb_par.
    apply wb_ref.
    eapply wb_trans.
    apply wb_struct.
    repeat (apply con_res).
    eapply sg_trans.
    apply sym.
    apply con_par.
    apply sg_ref.
    apply sym.
    replace (u + 9) with (1 + (u + 6) + 2) by lia.
    replace (r + 9) with (1 + (r + 6) + 2) by lia.
    simpl.
    unfold id.
    apply link_handlers.
    simpl.
    repeat (rewrite shift_extend_id_proc).
    
    eapply wb_trans.
    apply wb_con with
      (c := (CRes (CRes (CRes (CRes (CRes CHole)))))).
    replace (u + 6) with ((u + 5) + 1) by lia.
    replace (r + 6) with ((r + 5) + 1) by lia.
    apply we_need_this_but_is_hard.
    simpl.
    
    eapply wb_trans.
    apply wb_con with
      (c := (CRes (CRes (CRes (CRes CHole))))).
    replace (u + 5) with ((u + 4) + 1) by lia.
    replace (r + 5) with ((r + 4) + 1) by lia.
    apply substitution.
    simpl.
    
    eapply wb_trans.
    change
      (Res (Res (Res (Res ($ s {{v {}>Var}}; u + 4; r + 4; [] $)))))
    with
      ((Res ^^ 4) ($ s {{v {}>Var}}; u + 4; r + 4; [] $)).
    apply res_n_encoding with (n := 4).
    
    apply wb_ref.
Qed.

Lemma context_weak_transition_1:
  forall p q r,
    p =()> q ->
    Res (Res (Par p r)) =()> Res (Res (Par q r)).
Proof.
Admitted.

Lemma context_weak_transition_2:
  forall p q r s,
    p =()> q ->
    (Res (Res (Res (Res (Par 
      (r)
      (Par
        (p)
        (s)
      )
    ))))) =()>
    (Res (Res (Res (Res (Par 
      (r)
      (Par
        (q)
        (s)
      )
    ))))).
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
  - intros u r.
    destruct (IHHred 1 0) as [ P [ Hstep Hsim ] ].
    exists 
      (Res (Res (Par 
        (P) 
        (In 0 ($ t; u + 3; r + 3; [(0, 0)] $)
      )))).
    simpl.
    split.
    
    apply context_weak_transition_1.
    apply Hstep.
    
    eapply wb_trans.
    apply wb_con with 
      (c := (CRes (CRes (CParL
        (CHole)
        (In 0 ($ t; u + 3; r + 3; [(0, 0)] $))
      )))).
    apply Hsim.
    simpl.
    
    apply wb_ref.
    
  - apply force_thunk_sound.
  - apply app_base_sound.
  - intros u r.
    destruct (IHHred 3 2) as [ P [ Hstep Hsim ] ].
    eexists.
    simpl.
    split.
    
    apply context_weak_transition_2.
    apply Hstep.
    
    apply wb_con with 
      (c := (CRes (CRes (CRes (CRes (CParR 
        (In 3 (In 2 (Out 1 (Out 2 (Out 3 (Par 
          (Link 2 (u + 9))
          (Par 
            (Link 1 (r + 9)) 
            (Link 0 3)
          )
        ))))))
        (CParL
          CHole
          (Out 1 ($ v; [] $))
        ) 
      )))))).
    apply Hsim.
Qed.