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
Require Import Coq.Logic.FunctionalExtensionality.

(* TODO is this premise really the correct one *)
(* Lemma 6.2 *)
Lemma link_lift: 
  forall s u r n refs,
    wf_term 1 s ->
    Res (Par (Link (BN 0) (BN n)) ($ s ; S u ; S r ; refs $ [[Nat.iter n lift_subst S]])) ~~
    $ s ; u ; r ; refs $.
Proof.
Admitted.


(* TODO is this premise really the correct one *)
(* TODO should probably have the implication n <> m *)
(* Lemma 6.4 *)
Lemma link_handlers: forall s n m refs,
  wf_term 1 s ->
  (Res (Res (Par 
    (encode s 1 0 refs)
    (Par
      (Link (BN 1) (BN (S (S n))))
      (Link (BN 0) (BN (S (S m))))
    )
  ))) ~~
  (encode s n m refs).
Proof.
Admitted.

(* Lemma 5, substitution-Lemma*)
Lemma substitution:
  forall s v,
    wf_term 1 s ->
    wf_value 0 v ->
    forall u r,
      Res (Par ($ v ; [] $) ($ s ; S u ; S r ; [(0,0)] $)) ~~
      $ (s {{ extend_subst_lam v (Var <<< BV) }}) ; u ; r ; []$.
Proof.
Admitted.

Lemma encode_reach: 
  forall n s u r,
    wf_term 0 s ->
    n <> u -> 
    n <> r -> 
    ref_n_in_proc n ($ s ; u ; r ; [] $) = false.
Proof.
Admitted.

Lemma redundant_subst_nat:
  forall n u subst,
    n > u ->
    Nat.iter n lift_subst subst u = u.
Proof.
  intros n.
  induction n; intros u subst Hgt.
  - lia.
  - simpl.
    unfold lift_subst.
    unfold extend_subst.
    destruct u.
    reflexivity.
    unfold compose.
    f_equal.
    apply IHn.
    lia.
Qed.

Lemma iter_succ:
  forall (n : nat) (f : (nat -> nat) -> nat -> nat) (g : nat -> nat),
    Nat.iter (S n) f g = f (Nat.iter n f g).
Proof.
  intros n f g.
  reflexivity.
Qed.

Scheme term_mut := Induction for term Sort Prop
with   value_mut := Induction for value Sort Prop.
Combined Scheme term_value_mutual_ind from term_mut, value_mut.

Lemma redundant_subst_mutual:
  (forall s u r refs n subst,
    wf_term 0 s ->
    n > u ->
    n > r ->
    $ s ; u ; r ; refs $ [[Nat.iter n lift_subst subst]] =
    $ s ; u ; r ; refs $) /\
  (forall v refs subst,
    wf_value 0 v ->
    $ v ; refs $ [[lift_subst subst]] =
    $ v ; refs $).
Proof.
  apply term_value_mutual_ind.
  - intros v Hv u r refs n subst Hwf HGTu HGTr.
    simpl.
    rewrite redundant_subst_nat.
    f_equal.
    apply Hv.
    inversion Hwf; subst.
    apply H1.
    apply HGTu.
  - intros s Hs u r refs n subst Hwf HGTu HGTr.
    simpl.
    unfold compose.
    repeat (rewrite <- iter_succ).
    repeat (rewrite redundant_subst_nat).
    repeat f_equal.
    * inversion Hwf; subst.
      
      
    
    all:lia.
  - intros s Hs v Hv u r refs n subst Hwf HGTu HGTr.
    inversion Hwf; subst.
    simpl.
    unfold compose.
    repeat (rewrite <- iter_succ).
    repeat (rewrite redundant_subst_nat).
    repeat f_equal.
    apply Hs.
    apply H2.
    1,2:lia.
    apply Hv.
    apply H3.
    all:lia.
  - intros v Hv u r refs n subst Hwf HGTu HGTr.
    simpl.
    unfold compose.
    repeat (rewrite <- iter_succ).
    repeat (rewrite redundant_subst_nat).
    repeat f_equal.
    apply Hv.
    inversion Hwf.
    apply H1.
    all:lia.
  - intros v Hv u r refs n subst Hwf HGTu HGTr.
    simpl.
    rewrite redundant_subst_nat.
    rewrite <- iter_succ.
    f_equal.
    apply Hv.
    inversion Hwf; subst.
    apply H1.
    lia.
  - intros s Hs t Ht u r refs n subst Hwf HGTu HGTr.
    inversion Hwf; subst.
    simpl.
    repeat (rewrite <- iter_succ).
    repeat f_equal.
    apply Hs.
    apply H2.
    1,2:lia.
    
    admit.
    
  - destruct n.
    all:intros refs subst Hwf.
    inversion Hwf; subst.
    inversion H1; subst.
    lia.
    reflexivity.
  - intros s Hs refs subst Hwf.
    simpl.
    unfold pointer.
    unfold compose.
    simpl.
    repeat f_equal.
    specialize (Hs 1 0 (incRefs 0 4 refs) 4 subst) as H.
    change
      (lift_subst (lift_subst (lift_subst (lift_subst subst)))) 
    with
      (Nat.iter 4 lift_subst subst).
    apply H.
    inversion Hwf; subst.
    apply H2.
    all:lia.
Admitted.

Definition redundant_subst_term := proj1 redundant_subst_mutual.
Definition redundant_subst_value := proj2 redundant_subst_mutual.

Lemma n_shift_n_m:
  forall n m,
    n =? (Nat.iter n lift_subst S) m = false.
Proof.
  intros n.
  induction n.
  - intros m.
    reflexivity.
  - intros m.
    destruct m.
    reflexivity.
    simpl.
    apply IHn.
Qed.

Lemma ref_n_in_proc_shift_n:
  forall p n,
    ref_n_in_proc n (p [[Nat.iter n lift_subst S]]) = false.
Proof.
  intros p.
  induction p.
  - intros n.
    destruct ch.
    all:simpl.
    rewrite n_shift_n_m.
    all:specialize (IHp (n + 1)).
    all:rewrite <- Nat.iter_succ.
    all:replace (S n) with (n + 1) by lia.
    all:apply IHp.
  - intros n.
    destruct ch.
    all:simpl.
    rewrite n_shift_n_m.
    all:specialize (IHp (n + 1)).
    all:rewrite <- Nat.iter_succ.
    all:replace (S n) with (n + 1) by lia.
    all:apply IHp.
  - intros n.
    simpl.
    specialize (IHp (n + 1)).
    rewrite <- Nat.iter_succ.
    replace (S n) with (n + 1) by lia.
    apply IHp.
  - simpl.
    apply IHp.
  - simpl.
    intros n.
    rewrite IHp1.
    rewrite IHp2.
    reflexivity.
  - destruct n.
    all:destruct m.
    all:simpl.
    1,2,3:intros m.
    1,2,3:repeat (rewrite n_shift_n_m).
    1,2,3:reflexivity.
    intros H.
    reflexivity.
  - intros n.
    simpl.
    reflexivity.
Qed.

Lemma ref_n_in_proc_shift:
  forall p,
    ref_n_in_proc 0 (p[[S]]) = false.
Proof.
  intros p.
  specialize (ref_n_in_proc_shift_n p 0) as H.
  simpl in H.
  apply H.
Qed.

Lemma lift_eq:
  forall subst,
    subst = id ->
    lift_subst subst = id.
Proof.
  intros subst H.
  rewrite H.
  apply functional_extensionality.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Lemma compose_lift_subst:
  forall subst1 subst2,
    (lift_subst subst1 >>> lift_subst subst2) = 
    (lift_subst (subst1 >>> subst2)).
Proof.
  intros subst1 subst2.
  unfold lift_subst.
  unfold compose.
  unfold extend_subst.
  apply functional_extensionality.
  intros n.
  destruct n.
  reflexivity.
  reflexivity.
Qed.

Lemma compose_init_subst:
  forall p subst1 subst2,
    (p [[subst1]] [[subst2]]) = (p [[subst1 >>> subst2]]).
Proof.
  intros p.
  induction p.
  all:intros subst1 subst2.
  - destruct ch.
    1,2:simpl.
    1,2:f_equal.
    1,2:rewrite <- compose_lift_subst.
    1,2:apply IHp.
  - destruct ch.
    1,2:simpl.
    1,2:f_equal.
    1,2:rewrite <- compose_lift_subst.
    1,2:apply IHp.
  - simpl.
    f_equal.
    rewrite <- compose_lift_subst.
    apply IHp.
  - simpl.
    f_equal.
    apply IHp.
  - simpl.
    f_equal.
    apply IHp1.
    apply IHp2.
  - destruct n.
    all:destruct m.
    all:simpl.
    all:f_equal.
  - reflexivity.
Qed.

Lemma shift_extend_id:
  ((0 []> id) <<< S) = id.
Proof.
  apply functional_extensionality.
  intros n.
  destruct n.
  all:reflexivity.
Qed.

Lemma id_proc:
  forall p,
    (p [[id]]) = p.
Proof.
  intros p.
  induction p.
  - destruct ch.
    all:simpl.
    all:f_equal.
    all:rewrite lift_eq.
    apply IHp.
    reflexivity.
    apply IHp.
    reflexivity.
  - destruct ch.
    all:simpl.
    all:f_equal.
    all:rewrite lift_eq.
    apply IHp.
    reflexivity.
    apply IHp.
    reflexivity.
  - simpl.
    f_equal.
    rewrite lift_eq.
    apply IHp.
    reflexivity.
  - simpl.
    f_equal.
    apply IHp.
  - simpl.
    f_equal.
    apply IHp1.
    apply IHp2.
  - destruct n.
    all:destruct m.
    all:simpl.
    all:reflexivity.
  - reflexivity.
Qed. 

Lemma shift_extend_proc:
  forall p,
    (p [[S]] [[0 []> id]]) = p.
Proof.
  intros p.
  rewrite compose_init_subst.
  rewrite shift_extend_id.
  apply id_proc.
Qed.

Lemma res_rep_in_0:
  forall p,
    Res (Rep (In (BN 0) p)) ~~ Nil.
Proof.
Admitted.

Lemma ref_n_in_proc_swap:
  forall s,
    wf_term 1 s ->
    ref_n_in_proc 2 ($ s; 2; 1; [(0, 0)] $ [[swap]] [[lift_subst swap]]) = false.
Proof.
Admitted.

Lemma encode_swap_lift_swap:
  forall s,
    wf_term 1 s -> 
    ($ s; 2; 1; [(0, 0)] $ [[swap]] [[lift_subst swap]]) =
    ($ s; 1; 0; [(0, 2)] $).
Proof.
Admitted.

Lemma rmIsolatedProc: forall s u r,
  wf_term 0 s ->
  (Res ^^ 6)
    (Par
       (Par (encode s 1 0 [])
          (Rep (In (BN 0) (In (BN 0) (In (BN 1) (encode s 1 0 [])))) [[S]] [[S]] [[S]]))
       (Par (Link (BN 1) (BN (6 + u))) (Link (BN 0) (BN (6 + r))))) ~~ 
  ((Res ^^ 5) (Par
    (encode s 1 0 [])
    (Par (Link (BN 1) (BN (5 + u))) (Link (BN 0) (BN (5 + r))))
  )).
Proof.
  intros s u r Hwf.
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
  simpl.
  rewrite encode_reach.
  reflexivity.
  apply Hwf.
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
  repeat (
    simpl;
    unfold compose;
    unfold id
  ).
  fold id.
  
  change
    (lift_subst (lift_subst (lift_subst (0 []> id))))
  with
    (Nat.iter 3 lift_subst (0 []> id)).
  eapply wb_trans.
  apply wb_con with
    (c := CRes (CRes (CRes (CParL
      (CParL
        CHole
        (Link (BN 1) (BN (S (S (S (S (S u)))))))
      )
      (Link (BN 0) (BN (S (S (S (S (S r)))))))
    )))).
  rewrite redundant_subst_term.
  apply wb_ref.
  apply Hwf.
  1,2:lia.
  simpl.
  
  eapply wb_trans.
  apply wb_struct.
  repeat (apply con_res).
  apply par_assoc.
  
  apply wb_ref.
Qed.

Lemma force_thunk_sound:
  forall s,
    wf_term 0 (Force (Thunk s)) ->
    forall u r,
      exists p,
        ($ Force (Thunk s); u; r; [] $) =()> p /\ p ~~ ($ s; u; r; [] $).
Proof.
  intros s Hwf u r.
  eexists.
  split.
  - eapply rt_trans.
    apply rt_step.
    simpl.
    repeat (apply RES_TAU).
    eapply COM with (a := a_out (BN 1)).
    discriminate.
    apply OUT.
    apply IN.
    
    eapply rt_trans.
    unfold pointer.
    apply rt_step.
    repeat (apply RES_TAU).
    eapply COM with (a := a_in (BN 0)).
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
    eapply COM with (a := a_in (BN 0)).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    simpl.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    eapply COM with
      (a := a_in (BN 1)).
    discriminate.
    apply PAR_L.
    discriminate.
    apply IN.
    apply OUT.
    
    apply rt_refl.
  - eapply wb_trans.
    apply rmIsolatedProc.
    inversion Hwf.
    inversion H1.
    apply H4.
    eapply wb_trans.
    apply wb_con with 
      (c := CRes (CRes (CRes CHole))).
    simpl.
    apply link_handlers.
    inversion Hwf.
    inversion H1.
    apply wf_term_extend in H4.
    apply H4.
    simpl.
    replace (S (S (S u))) with (3 + u) by lia.
    replace (S (S (S r))) with (3 + r) by lia.
    fold ((Res ^^ 3) (encode s (3 + u) (3 + r) [])).
    apply res_n_encoding.
    inversion Hwf.
    inversion H1.
    apply H4.
Qed.

Lemma bind_base_sound:
  forall s v,
    wf_term 0 (Bind (Ret v) s) ->
    forall u r,
      exists P,
        $ Bind (Ret v) s ; u ; r ; [] $ =()> P /\
        P ~~ $ (s {{v {}> Var <<< BV}}) ; u ; r ; [] $.
Proof.
  intros s v Hwf u r.
  eexists.
  split.
  - simpl.
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    eapply COM with (a := a_out (BN 0)).
    discriminate.
    apply OUT.
    apply IN.
    apply rt_refl.
  - eapply wb_trans.
    apply wb_con with
      (c := CRes (CRes CHole)).
    apply substitution.
    inversion Hwf.
    apply H3.
    inversion Hwf.
    inversion H2.
    apply H6.
    simpl.

    replace (S (S u)) with (2 + u) by lia.
    replace (S (S r)) with (2 + r) by lia.
    change 
      (Res (Res ($ s {{v {}>Var <<< BV}}; 2 + u; 2 + r; [] $)))
    with
      ((Res ^^ 2) ($ s {{v {}>Var <<< BV}}; 2 + u; 2 + r; [] $)).
    apply res_n_encoding.
    inversion Hwf.
    subst.
    apply wf_term_subst.
    apply H3.
    inversion H2.
    apply H1.
Qed.

Lemma app_base_substitution:
  forall s v u r,
    wf_term 0 (App (Abs s) v) ->
    ((Res ^^ 9) (Par
      (Par
        (Link (BN 2) (BN (9 + u)))
        (Par
          (Link (BN 1) (BN (9 + r)))
          (Link (BN 0) (BN 3))
        )
      )
      (Par
        ($ s; 2; 1; [(0, 0)] $ [[lift_subst (lift_subst (lift_subst S))]])
        ($ v; [] $ [[lift_subst S]] [[S]] [[S]] [[S]])
      )
    )) ~~
    ($ s {{v {}>Var <<< BV}}; u; r; [] $).
Proof.
  intros s v u r Hwf.
  inversion Hwf; inversion H2; subst.
  change
    (lift_subst (lift_subst (lift_subst S)))
  with
    (Nat.iter 3 lift_subst S).
  rewrite redundant_subst_value.
  eapply wb_trans.
  apply wb_struct.
  eapply sg_trans.
  repeat apply con_res.
  apply par_flatten.
  eapply sg_trans.
  do 8 (apply con_res).
  apply sg_par_res_l.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  eapply sg_trans.
  do 7 (apply con_res).
  apply sg_par_res_l.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  do 6 (apply con_res).
  apply sg_par_res_l.
  apply ref_n_in_proc_shift.
  rewrite shift_extend_proc.
  eapply wb_trans.
  apply wb_con with
    (c := CRes (CRes (CRes (CRes (CRes (CRes (CParL
      CHole
      ($ v; [] $)
    ))))))).
  eapply wb_trans.
  apply wb_struct.
  do 2 (apply con_res).
  eapply sg_trans.
  apply con_res.
  eapply sg_trans.
  apply par_assoc.
  apply con_par.
  apply sg_ref.
  apply par_assoc.
  eapply sg_trans.
  apply sg_par_res_r.
  reflexivity.
  apply con_par.
  apply sg_ref.
  apply sg_par_res_r.
  reflexivity.
  simpl.
  unfold id.
  eapply wb_trans.
  apply wb_con with
    (c := CRes (CRes (CParR
      (Link (BN 1) (BN (8 + u)))
      (CParR
        (Link (BN 0) (BN (8 + r)))
        CHole
      )
    ))).
  apply link_lift.
  apply H6.
  simpl.
  eapply wb_trans.
  apply wb_struct.
  repeat (apply con_res).
  eapply sg_trans.
  apply sym.
  eapply sg_trans.
  apply con_par.
  apply sym.
  apply sg_ref.
  eapply sg_trans.
  apply par_assoc.
  apply con_par.
  apply sg_ref.
  apply sym.
  apply link_handlers.
  apply H6.
  simpl.
  eapply wb_trans.
  apply wb_con with
    (c := CRes (CRes (CRes (CRes (CRes CHole))))).
  eapply wb_trans.
  apply wb_struct.
  apply con_res.
  apply sym.
  apply substitution.
  apply H6.
  apply H3.
  simpl.
  replace (S (S (S (S (S u))))) with (5 + u) by lia.
  replace (S (S (S (S (S r))))) with (5 + r) by lia.
  change
    (Res (Res (Res (Res (Res ($ s {{v {}> (Var <<< BV) }}; 5 + u; 5 + r; [] $))))))
  with
    ((Res ^^ 5) ($ s {{v {}> (Var <<< BV)}}; 5 + u; 5 + r; [] $)).
  apply res_n_encoding with (n := 5).
  inversion Hwf.
  apply wf_term_subst.
  inversion H2.
  apply H6.
  apply H3.
  apply H3.
Qed.

Lemma app_base_sound:
  forall s v,
    wf_term 0 (App (Abs s) v) ->
    forall u r,
      exists p,
        ($ App (Abs s) v; u; r; [] $) =()> p /\
        p ~~ ($ s {{v {}>Var <<< BV}}; u; r; [] $).
Proof.
  intros s v Hwf u r.
  eexists.
  split.
  - simpl.
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 3)).
    discriminate.
    apply IN.
    apply PAR_L.
    discriminate.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_in (BN 2)).
    discriminate.
    apply IN.
    apply PAR_R.
    discriminate.
    simpl.
    apply OUT.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out (BN 1)).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    simpl.
    apply IN.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out (BN 2)).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    apply IN.
    
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
    apply COM with (a := a_out (BN 3)).
    discriminate.
    apply OUT.
    apply PAR_L.
    discriminate.
    apply IN.
    
    apply rt_refl.

  - apply app_base_substitution.
    apply Hwf.
Qed.

Theorem sound:
  forall s,
    wf_term 0 s ->
    forall t,
      s --> t ->
      forall u r,
        exists P,
          (encode s u r []) =()> P /\ (P ~~ (encode t u r [])).
Proof.
  intros s Hwf t Hred.
  induction Hred.
  - apply bind_base_sound.
    apply Hwf.
  - intros u r.
    inversion Hwf.
    destruct (IHHred H2 1 0) as [ P [ Hstep Hsim ] ].
    subst.
    simpl.
    eexists.
    split.
    
    apply wt_tau_context with 
      (c := CRes (CRes (CParL
        CHole
        (In (BN 0) ($ t; S (S (S u)); S (S (S r)); [(0, 0)] $))
      ))).
    simpl.
    reflexivity.
    apply Hstep.

    eapply wb_trans.
    apply wb_con with 
      (c := (CRes (CRes (CParL
        (CHole)
        (In (BN 0) ($ t; 3 + u; 3 + r; [(0, 0)] $))
      )))).
    apply Hsim.
    simpl.
    
    apply wb_ref.
  - apply force_thunk_sound.
    apply Hwf.
  - apply app_base_sound.
    apply Hwf.
  - intros u r.
    inversion Hwf.
    destruct (IHHred H2 3 2) as [ P [ Hstep Hsim ] ].
    eexists.
    simpl.
    split.
    
    eapply wt_tau_context with 
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (9 + u)))
          (Par
            (Link (BN 1) (BN (9 + r)))
            (Link (BN 0) (BN 3))
          )
        ))))))
        (CParL
          CHole
          (Out (BN 1) ($ v; [] $))
        )
      ))))).
    simpl.
    reflexivity.
    apply Hstep.
    
    apply wb_con with 
      (c := (CRes (CRes (CRes (CRes (CParR 
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par 
          (Link (BN 2) (BN (9 + u)))
          (Par 
            (Link (BN 1) (BN (9 + r))) 
            (Link (BN 0) (BN 3))
          )
        ))))))
        (CParL
          CHole
          (Out (BN 1) ($ v; [] $))
        ) 
      )))))).
    apply Hsim.
Qed.