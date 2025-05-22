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

Lemma encode_no_input:
  forall s u r refs p n,
    ($ s ; u ; r ; refs $) -( a_in n )> p -> False.
Proof.
Admitted.

Lemma encode_u_r_bn_output:
  forall s u r refs p n,
    n <> u ->
    n <> r ->
    ($ s ; u ; r ; refs $) -( a_out (BN n) )> p -> False.
Proof.
Admitted.

Lemma encode_no_fn_output:
  forall s u r refs p n,
    ($ s ; u ; r ; refs $) -( a_out (FN n) )> p -> False.
Proof.
Admitted.

Lemma app_val_bisim:
  forall v0 v u r,
    (Res
      (Par
         (In (BN 2)
            (Out (BN 1)
               (Out (BN 2)
                  (Out (BN 3)
                     (Par
                        (Link (BN 2)
                           (BN (S (S (S (S (S (S (S (S (S u)))))))))))
                        (Par
                           (Link (BN 1)
                              (BN (S (S (S (S (S (S (S (S (S r)))))))))))
                           (Link (BN 0) (BN 3))))))))
         (Par ($ v0; [] $) (Out (BN 2) ($ v; [] $ [[lift_subst S]]))))) ~~
    (Par
      (In (BN 3)
         (In (BN 2)
            (Out (BN 1)
               (Out (BN 2)
                  (Out (BN 3)
                     (Par
                        (Link (BN 2)
                           (BN (S (S (S (S (S (S (S (S (S u)))))))))))
                        (Par
                           (Link (BN 1)
                              (BN (S (S (S (S (S (S (S (S (S r)))))))))))
                           (Link (BN 0) (BN 3)))))))))
      (Par (Out (BN 3) ($ v0; [] $)) (Out (BN 1) ($ v; [] $)))).
Proof.
Admitted.

Lemma app_bind_bisim:
  forall v0,
    (Res (Par 
      ($ v0; [] $)
      (Out (BN 0) (Out (BN 0) (Out (BN 1) (Par 
        (Link (BN 1) (BN 9)) 
        (Link (BN 0) (BN 8))
      ))))
    )) ~~
    (Par 
      (Out (BN 1) ($ v0; [] $))
      (In (BN 1) (Out (BN 0) (Out (BN 0) (Out (BN 1) (Par 
        (Link (BN 1) (BN 9)) 
        (Link (BN 0) (BN 8))
      )))))
    ).
Proof.
Admitted.

Lemma app_complete: 
  forall s v u r p,
    wf_term 0 (App s v) ->
    $ App s v ; u ; r ; [] $ -( a_tau )> p ->
    ( wf_term 0 s ->
      forall p u r,
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
  
  specialize (IH H2).
  
  inversion Hstep; subst; clear Hstep.
  contradiction.
  inversion H5; subst; clear H5.
  contradiction.
  inversion H0; subst; clear H0.
  contradiction.
  inversion H1; subst; clear H1.
  contradiction.
  destruct s.
  - inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1; subst; clear H1.
    inversion H1; subst; clear H1.
    contradiction.
    contradiction.
    inversion H0; subst; clear H0.
    inversion H0; subst; clear H0.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    simpl in H.
    inversion H.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H13; subst; clear H13.
    * eexists.
      exists (App (Val v0) v).
      split.
      apply rt_refl.
      split.
      simpl.
      apply wb_con with
        (c := CRes (CRes (CRes (CRes CHole)))).
      apply app_val_bisim.
      right.
      reflexivity.
    * inversion H13.
    * inversion H11.
    * inversion H11.
    * inversion H10.
  - exists
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
      )).
    exists (s {{v {}> (Var <<< BV)}}).
    split.
    2:split.
    * inversion H0; subst; clear H0.
      contradiction.
      contradiction.
      inversion H1; subst; clear H1.
      inversion H1; subst; clear H1.
      contradiction.
      contradiction.
      inversion H0; subst; clear H0.
      inversion H0; subst; clear H0.
      inversion H5; inversion H6; subst; clear H5; clear H6.
      simpl in H.
      inversion H.
      inversion H5; inversion H6; subst; clear H5; clear H6.
      inversion H13; subst; clear H13.
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
      inversion H13; subst.
      inversion H12; subst.
      inversion H12; subst.
      inversion H12; inversion H14; subst.
      simpl in H.
      inversion H.
    * apply app_base_substitution.
      apply Hwf.
    * left.
      apply APPLICATION_BASE.
  - inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1; subst; clear H1.
    inversion H1; subst; clear H1.
    contradiction.
    contradiction.
    
    specialize (IH R0 3 2 H0) as [q [t [Htau [Hbisim Hred] ] ] ].
    eexists.
    exists (App t v).
    split.
    apply wt_tau_context with 
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (S (S (S (S (S (S (S (S (S u)))))))))))
          (Par
            (Link (BN 1) (BN (S (S (S (S (S (S (S (S (S r)))))))))))
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
    apply Htau.
    simpl.
    split.
    apply wb_con with
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (S (S (S (S (S (S (S (S (S u)))))))))))
          (Par
            (Link (BN 1) (BN (S (S (S (S (S (S (S (S (S r)))))))))))
            (Link (BN 0) (BN 3))
          )
        ))))))
        (CParL
          CHole
          (Out (BN 1) ($ v; [] $))
        )
      ))))).
    apply Hbisim.
    inversion Hred.
    left.
    apply APPLICATION_EVOLVE.
    apply H.
    right.
    rewrite H.
    reflexivity.
    inversion H0.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    destruct a.
    contradiction.
    inversion H7; subst; clear H7.
    inversion H8; subst; clear H8.
    inversion H13; subst; clear H13.
    destruct n.
    1,2:simpl in H.
    1,2:inversion H.
    inversion H13; subst; clear H13.
    exfalso.
    destruct n.
    1,2:simpl in H14.
    1,2:eapply encode_no_input.
    1,2:apply H14.
    inversion H14; subst; clear H14.
    destruct n.
    1,2:simpl in H.
    1,2:inversion H.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H8.
    1,2:inversion H8.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H9.
    1,2:inversion H9.
    destruct n.
    1,2:simpl in H6.
    1,2:inversion H6.
    inversion H7; subst; clear H7.
    inversion H8; subst; clear H8.
    inversion H13; subst; clear H13.
    destruct n.
    1,2:simpl in H.
    1,2:inversion H.
    inversion H13; subst; clear H13.
    exfalso.
    destruct n.
    1,2:simpl in H14.
    eapply encode_u_r_bn_output with
      (u := 3)
      (r := 2)
      (n := (4 + n)).
    1,2:lia.
    apply H14.
    eapply encode_no_fn_output.
    apply H14.
    inversion H14.
    destruct n.
    1,2:simpl in H.
    1,2:inversion H.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H8.
    1,2:inversion H8.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H10.
    1,2:inversion H10.
    destruct n.
    1,2:simpl in H9.
    1,2:inversion H9.
    destruct n.
    1,2:simpl in H6.
    1,2:inversion H6.
    destruct a.
    simpl in H5.
    contradiction.
    destruct n.
    1,2:simpl in H1.
    1,2:inversion H1.
    destruct n.
    1,2:simpl in H1.
    1,2:inversion H1.
    destruct a.
    simpl in H5.
    contradiction.
    destruct n.
    1,2:simpl in H5.
    1,2:inversion H5.
    destruct n.
    1,2:simpl in H5.
    1,2:inversion H5.
    inversion H11.
    rename S into T.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H13; subst; clear H13.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    inversion H7; subst; clear H7.
    inversion H8; subst; clear H8.
    inversion H13; subst; clear H13.
    inversion H13; subst; clear H13.
    simpl in H14.
    exfalso.
    eapply encode_u_r_bn_output with
      (u := 3)
      (r := 2)
      (n := 7).
    1,2:lia.
    apply H14.
    inversion H14.
    inversion H13.
    inversion H11.
    inversion H11.
    inversion H10.
  - inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1; subst; clear H1.
    inversion H1; subst; clear H1.
    contradiction.
    contradiction.
    inversion H0; subst; clear H0.
    contradiction.
    inversion H1; subst; clear H1.
    contradiction.
    inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1.
    inversion H1.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    eexists.
    exists (App (Force v0) v).
    split.
    apply rt_refl.
    split.
    simpl.
    apply wb_con with
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (S (S (S (S (S (S (S (S (S u)))))))))))
          (Par 
            (Link (BN 1) (BN (S (S (S (S (S (S (S (S (S r)))))))))))
            (Link (BN 0) (BN 3))
          )
        ))))))
        (CParL
          (CRes (CRes CHole))
          (Out (BN 1) ($ v; [] $))
        )
      ))))).
    apply app_bind_bisim.
    right.
    reflexivity.
    inversion H0.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    inversion H10; subst; clear H10.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H.
    1,2,3,4:inversion H.
    inversion H10; subst; clear H10.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H.
    1,2,3,4:inversion H.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H8.
    1,2,3,4:inversion H8.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H8.
    1,2,3,4:inversion H8.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H7.
    1,2,3,4:inversion H7.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H5.
    1,2,3,4:inversion H5.
    inversion H11.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H13; subst; clear H13.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    inversion H11.
    inversion H11.
    inversion H13.
    inversion H11.
    inversion H11.
    inversion H10.
  - inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1; subst; clear H1.
    inversion H1; subst; clear H1.
    contradiction.
    contradiction.
    inversion H0; subst; clear H0.
    inversion H0; subst; clear H0.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    simpl in H.
    inversion H.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H13; subst; clear H13.
    
    inversion H13.
    inversion H12.
    inversion H12.
    inversion H12; inversion H14; subst; clear H12; clear H14.
    inversion H.
  - inversion H0; subst; clear H0.
    contradiction.
    contradiction.
    inversion H1; subst; clear H1.
    inversion H1; subst; clear H1.
    contradiction.
    contradiction.
    
    specialize (IH R0 3 2 H0) as [q [t [Htau [Hbisim Hred] ] ] ].
    eexists.
    exists (App t v).
    split.
    apply wt_tau_context with 
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (S (S (S (S (S (S (S (S (S u)))))))))))
          (Par
            (Link (BN 1) (BN (S (S (S (S (S (S (S (S (S r)))))))))))
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
    apply Htau.
    simpl.
    split.
    apply wb_con with
      (c := CRes (CRes (CRes (CRes (CParR
        (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
          (Link (BN 2) (BN (S (S (S (S (S (S (S (S (S u)))))))))))
          (Par
            (Link (BN 1) (BN (S (S (S (S (S (S (S (S (S r)))))))))))
            (Link (BN 0) (BN 3))
          )
        ))))))
        (CParL
          CHole
          (Out (BN 1) ($ v; [] $))
        )
      ))))).
    apply Hbisim.
    inversion Hred.
    left.
    apply APPLICATION_EVOLVE.
    apply H.
    right.
    rewrite H.
    reflexivity.
    inversion H0.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    destruct a.
    contradiction.
    exfalso.
    destruct n.
    1,2:eapply encode_no_input.
    1,2:simpl in H10.
    1,2:apply H10.
    exfalso.
    destruct n.
    1,2:simpl in H10.
    eapply encode_u_r_bn_output with
      (u := 1)
      (r := 0)
      (n := S (S n)).
    1,2:lia.
    apply H10.
    eapply encode_no_fn_output.
    apply H10.
    inversion H10; subst; clear H10.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H.
    1,2,3,4:inversion H.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H8.
    1,2,3,4:inversion H8.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H8.
    1,2,3,4:inversion H8.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H7.
    1,2,3,4:inversion H7.
    destruct a.
    contradiction.
    1,2:destruct n.
    1,2,3,4:simpl in H5.
    1,2,3,4:inversion H5.
    contradiction.
    inversion H5; inversion H6; subst; clear H5; clear H6.
    inversion H13; subst; clear H13.
    inversion H1; subst; clear H1.
    inversion H6; subst; clear H6.
    exfalso.
    simpl in H11.
    eapply encode_u_r_bn_output with
      (u := 1)
      (r := 0)
      (n := 5).
    1,2:lia.
    apply H11.
    inversion H11.
    inversion H13.
    inversion H11.
    inversion H11.
    inversion H10.
Qed.

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

Lemma tau_step_bind:
  forall s1 s2 u r P,
    wf_term 0 (Bind s1 s2) ->
    ($ Bind s1 s2; u; r; [] $) -(a_tau)> P ->
    ( wf_term 0 s1 ->
      forall (P : proc) (u r : nat),
        ($ s1; u; r; [] $) -(a_tau)> P ->
        exists (P1 : proc) (t1 : term),
          P =()> P1 /\ P1 ~~ ($ t1; u; r; [] $) /\ (s1 --> t1 \/ s1 = t1)
    ) ->
    ( wf_term 0 s2 ->
      forall (P : proc) (u r : nat),
        ($ s2; u; r; [] $) -(a_tau)> P ->
        exists (P2 : proc) (t2 : term),
          P =()> P2 /\ P2 ~~ ($ t2; u; r; [] $) /\ (s2 --> t2 \/ s2 = t2)
    ) ->
    exists (P' : proc) (t : term),
      P =()> P' /\ P' ~~ ($ t; u; r; [] $) /\ (Bind s1 s2 --> t \/ Bind s1 s2 = t).
Proof.
  intros s1 s2 u r p Hwf Hstep IH1 IH2.
  inversion Hwf.
  
  specialize (IH1 H2).
  
  simpl in Hstep.
  inversion Hstep; subst; clear Hstep.
  contradiction.
  inversion H5; subst; clear H5.
  contradiction.
  inversion H0; subst; clear H0.
  - contradiction.
  - contradiction.
  - specialize (IH1 R 1 0 H1) as [ P1 [ t1 [ Hstep [ Hbisim Hred ] ] ] ].
    pose 
      (c := CRes (CRes (CParL
        CHole
        (In (BN 0) ($ s2; S (S (S u)); S (S (S r)); [(0, 0)] $))
      ))).
    eexists.
    exists (Bind t1 s2).
    split.
    apply wt_tau_context with (c := c).
    simpl.
    reflexivity.
    apply Hstep.
    simpl.
    split.
    apply wb_con with (c := c).
    apply Hbisim.
    inversion Hred.
    left; apply BINDING_EVOLVE; apply H.
    right; rewrite H; reflexivity.
  - inversion H1.
  - rename S into Q.
    destruct a.
    contradiction.
    inversion H6.
    simpl in H6.
    inversion H6; subst; clear H6.
    destruct s1.
    * simpl in H5.
      inversion H5.
    * simpl in H5.
      inversion H5.
    * simpl in H5.
      inversion H5; subst; clear H5.
      inversion H1; subst; clear H1.
      inversion H6; subst; clear H6.
      inversion H7; subst; clear H7.
      inversion H8; subst; clear H8.
      inversion H12.
      inversion H12; subst; clear H12.
      simpl in H13.
      exfalso.
      eapply encode_u_r_bn_output with
        (u := 3)
        (r := 2)
        (n := 4).
      1,2:lia.
      apply H13.
      inversion H13.
    * simpl in H5.
      inversion H5; subst; clear H5.
      inversion H1; subst; clear H1.
      inversion H6; subst; clear H6.
      inversion H10.
      inversion H10.
    * inversion H5; subst; clear H5.
      eexists.
      exists (s2 {{ v {}> Var <<< BV }}).
      split.
      apply rt_refl.
      split.
      eapply wb_trans.
      apply wb_con with 
        (c := CRes (CRes CHole)).
      apply substitution.
      apply H3.
      inversion H2.
      apply H1.
      simpl.
      eapply wb_trans.
      change 
        (Res (Res ($ s2 {{v {}>Var <<< BV}}; S (S u); S (S r); [] $)))
      with
        ((Res ^^ 2) ($ s2 {{v {}>Var <<< BV}}; S (S u); S (S r); [] $)).
      replace (S (S u)) with (2 + u) by lia.
      replace (S (S r)) with (2 + r) by lia.
      apply res_n_encoding.
      apply wf_term_subst.
      apply H3.
      inversion H2.
      apply H1.
      apply wb_ref.
      left.
      apply BINDING_BASE.
    * simpl in H5.
      inversion H5; subst; clear H5.
      inversion H1; subst; clear H1.
      inversion H6; subst; clear H6.
      simpl in H10.
      exfalso.
      eapply encode_u_r_bn_output with
        (u := 1)
        (r := 0)
        (n := 2).
      1,2:lia.
      apply H10.
      inversion H10.
Qed.

Theorem complete: 
  forall s P u r,
    wf_term 0 s ->
    (encode s u r []) -( a_tau )> P -> 
      exists P' t,
        P =()> P' /\
        P' ~~ encode t u r [] /\
        (s --> t \/ s = t).
Proof.
  intros s.
  induction s.
  all:intros P u r Hwf H.
  - inversion H.
  - inversion H.
  - apply app_complete; auto.
  - apply force_complete; auto.
  - inversion H.
  - apply tau_step_bind; auto.
Qed.