Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Basics.
Require Import Coq.Relations.Relation_Operators. 
From Coq Require Import Lia.
Require Import PeanoNat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.
From Encoding Require Export encoding.
From Encoding Require Export soundness.

Lemma app_complete: 
  forall s v u r p,
    wf_term 0 (App s v) ->
    $ App s v ; u ; r ; [] $ -( a_tau )> p ->
    ( wf_term 0 s ->
      $ s ; u ; r ; [] $ -( a_tau )> p ->
      exists q t,
        p =()> q /\
        (q ~~ $ t ; u ; r ; [] $) /\ (s --> t \/ s = t)
    ) ->
    exists q t,
      p =()> q /\
      (q ~~ $ t ; u ; r ; [] $) /\
      (App s v --> t \/ App s v = t).
Proof.
  intros s v u r p Hwf Hstep IH.
  inversion Hwf.
  
  destruct s.
  - eexists.
    exists (App (Val v1) v).
    split.
    
    

    
    
  
Admitted.

Lemma app_complete': forall P s v u r,
  (($ App s v; u; r; [] $) -( a_tau )> P) ->
    exists P' t,
      P =()> P' /\
      P' ~~ ($ t; u; r; [] $) /\
      (App s v --> t \/ App s v = t).
Proof.
  intros P s v u r Hstep.
  inversion Hstep. contradiction. subst.
  inversion H0. contradiction. subst.
  inversion H1. contradiction. subst.
  inversion H2. contradiction. subst.
  inversion H3. contradiction. contradiction. subst.
  inversion H4. subst.
  inversion H4. contradiction. contradiction. subst.
  destruct v.
  destruct n. simpl in *.
(* Here we have for all cases of the variable *)
(* Now we must unfold the R0 process *)
  destruct R0.
  eexists. eexists.
  - split.
    simpl.
  
    eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU).
  (*  specialize (wf_term 0 s). *)
  (* admit goals with terms that are not well formed *)
  (* The only cases we know that does something is:
  - R0 is a value
  - R0 communicates with In (BN 3), and is then stuck
  *)
Admitted.

Lemma nil_proc_1:
  forall u r s,
    Res
      (Res
         (Par (Res (Link (BN 0) (BN (S (S (S u))))))
            (Res (Par (Link (BN 0) (FN s)) (Link (BN 0) (BN (S (S (S r))))))))) ~~
    Nil.
Proof.
  intros u r s.
  apply wb.
  split.
  all:intros a.
  all:destruct a.
Admitted.

Lemma nil_proc_2:
  forall u r s,
    Nil ~~
    Res
      (Res
         (Par
            (Out (BN 1)
               (Rep (In (BN 0) (In (BN 0) (In (BN 1) (Link (BN 0) (FN s)))))))
            (In (BN 1)
               (Out (BN 0)
                  (Out (BN 0)
                     (Out (BN 1)
                        (Par (Link (BN 1) (BN (S (S (S (S (S (S u))))))))
                           (Link (BN 0) (BN (S (S (S (S (S (S r))))))))))))))).
Proof.
  intros u r s.
  apply wb.
  split.
  
  intros a p' Hstep.
  inversion Hstep.
  
  intros a q' Hstep.
  exists Nil.
  destruct a.
  - split.
  
    apply WT_TAU.
    apply rt_refl.
    
    inversion Hstep; subst.
    contradiction.
    inversion H0; subst.
    contradiction.
    inversion H1; subst.
    contradiction.
    contradiction.
    inversion H2; subst.
    inversion H2; subst.
    rename S into T.
    inversion H4; inversion H5; subst.
    
    
    
  
  
Admitted.

Lemma force_complete: 
  forall v,
    wf_term 0 (Force v) ->
    forall u r P,
      ($ Force v; u; r; [] $) -( a_tau )> P ->
        exists P' t,
        P =()> P' /\
        P' ~~ ($ t; u; r; [] $) /\
        (Force v --> t \/ Force v = t).
Proof.
  intros v Hwf u r p Hstep.
  inversion Hstep.
  contradiction.
  inversion H0.
  contradiction.
  subst.
  inversion H3.
  subst.
  contradiction.
  contradiction.
  subst.
  inversion H1.
  subst. (* ! *)
  inversion H1.
  subst.
  inversion H4.
  inversion H5.
  subst.
  
  destruct v.
  destruct n.
  - inversion Hwf.
    inversion H7.
    inversion H10.
    lia.
  - eexists.
    exists (Force (Var (FV s))).
    split.
    2:split.
    * simpl.
      unfold pointer.
      eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 0)).
      discriminate.
      apply REP.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 0)).
      discriminate.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 1)).
      discriminate.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      apply rt_refl.
    * eapply wb_trans.
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
      
      eapply wb_trans.
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
      reflexivity.
      
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
      
      eapply wb_trans.
      apply wb_struct.
      do 2 (apply con_res).
      eapply sg_trans.
      apply con_res.
      apply con_par.
      apply sym.
      apply sg_ref.
      eapply sg_trans.
      apply con_res.
      apply par_assoc.
      apply sg_par_res_r.
      simpl.
      reflexivity.
      simpl.
      unfold id.
      
      eapply wb_trans.
      apply wb_struct.
      apply con_res.
      apply sg_par_res_l.
      simpl.
      reflexivity.
      repeat (
        simpl;
        unfold compose;
        unfold id
      ).
      
      eapply wb_trans.
      apply wb_struct.
      eapply sg_trans.
      apply con_res.
      apply add_nil.
      eapply sg_trans.
      apply sg_par_res_r.
      simpl.
      reflexivity.
      repeat (
        simpl;
        unfold compose;
        unfold id
      ).
      eapply sg_trans.
      apply con_par.
      apply sg_ref.
      apply res_nil.
      apply del_nil.
      apply wb_ref.
      simpl.
      unfold pointer.
      
      apply wb_trans with
        (q := Nil).
      apply nil_proc_1.
      apply nil_proc_2.
    * right.
      reflexivity.
  - simpl.
    unfold pointer.
    eexists.
    exists s.
    split.
    2:split.
    * eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 0)).
      discriminate.
      apply REP.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 0)).
      discriminate.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      eapply rt_trans.
      apply rt_step.
      repeat (apply RES_TAU).
      apply COM with (a := a_in (BN 1)).
      discriminate.
      apply PAR_L.
      discriminate.
      apply IN.
      apply OUT.
      apply rt_refl.
    * inversion Hwf.
      inversion H7.
      eapply wb_trans.
      apply rmIsolatedProc.
      apply H10.
      eapply wb_trans.
      apply wb_con with
        (c := CRes (CRes (CRes CHole))).
      apply link_handlers.
      apply wf_term_extend in H10 as H11.
      apply H11.
      simpl.
      change
        (Res (Res (Res ($ s; S (S (S u)); S (S (S r)); [] $))))
      with 
        ((Res ^^ 3) (((($ s; S (S (S u)); S (S (S r)); [] $))))).
      replace (S (S (S u))) with (3 + u) by lia.
      replace (S (S (S r))) with (3 + r) by lia.
      apply res_n_encoding.
      apply H10.
    * left.
      apply FORCE_THUNK.
Qed.

Lemma tau_step_bind : forall s1 s2 u r P,
    ($ Bind s1 s2; u; r; [] $) -(a_tau)> P ->
    ( ($ s1; u; r; [] $) -(a_tau)> P ->
      exists (P1 : proc) (t1 : term),
        P =()> P1 /\ P1 ~~ ($ t1; u; r; [] $) /\ (s1 --> t1 \/ s1 = t1) ) ->
    ( ($ s2; u; r; [] $) -(a_tau)> P ->
      exists (P2 : proc) (t2 : term),
        P =()> P2 /\ P2 ~~ ($ t2; u; r; [] $) /\ (s2 --> t2 \/ s2 = t2) ) ->
    exists (P' : proc) (t : term),
      P =()> P' /\ P' ~~ ($ t; u; r; [] $) /\ (Bind s1 s2 --> t \/ Bind s1 s2 = t).
Proof.
  intros.
  inversion H. congruence.
  inversion H3. contradiction. subst.
  inversion H6. contradiction. contradiction. subst.
  inversion H4. contradiction. contradiction. subst.
  (*Ligner meget app*)

  eexists. eexists.
  split.
  - eapply rt_trans.
    apply rt_step.
    repeat (apply RES_TAU). simpl.
    apply COM with (a := a_in (BN 0)).
    discriminate.
Admitted.
(*
    apply PAR_R_TAU.
    apply REP.
    discriminate.
    apply IN.
    apply OUT.
    
  admit.
Admitted.
*)


Theorem complete: 
  forall s,
    wf_term 0 s ->
      forall P u r,
      (encode s u r []) -( a_tau )> P -> 
        exists P' t,
          P =()> P' /\
          P' ~~ encode t u r [] /\
          (s --> t \/ s = t).
Proof.
  intros s Hwf P u r H.
  induction s as [| | s1 IH1 s2 IH2 | v | |].
  - inversion H.
  - inversion H.
  - apply app_complete.
    apply Hwf.
    apply H.
    apply IH1.
  - apply force_complete; auto.
  - inversion H.
  - apply tau_step_bind; auto.
Qed.