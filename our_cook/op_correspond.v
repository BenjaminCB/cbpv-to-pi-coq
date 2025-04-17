From Encoding Require Export pi.
From Encoding Require Export cbpv.
From Encoding Require Export encoding.
From Encoding Require Export bisimulation.
Require Import Coq.Classes.DecidableClass.
Require Coq.Lists.List.
Require Import Nat.
Require Coq.Lists.List.
Require Import Coq.Arith.Arith.


Lemma DB_help: forall (p : proc), (p [[lift_subst (0 |> shift)]]) = (p [[0 |> shift]]).
Proof. induction p. induction n.
  -simpl. rewrite IHp. Admitted.
  


Lemma DB_sub0 : forall (p : proc), p = (p [[0 |> shift]]).
Proof. intros. induction p.
  - induction n. simpl. rewrite -> DB_help. rewrite <- IHp. reflexivity.
  * simpl. rewrite -> DB_help. rewrite <- IHp. unfold shift. rewrite Nat.add_1_r. reflexivity.
  - simpl. rewrite <- IHp. induction n. induction m.
  * simpl. reflexivity. * simpl. unfold shift. rewrite Nat.add_1_r. reflexivity.
  * induction m. simpl. unfold shift. rewrite Nat.add_1_r. reflexivity.
  simpl. unfold shift. rewrite Nat.add_1_r. rewrite Nat.add_1_r. reflexivity.
  - simpl. rewrite -> DB_help. rewrite <- IHp. reflexivity.
  - simpl. rewrite <- IHp. reflexivity.
  - simpl. rewrite <- IHp1. rewrite <- IHp2. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma helper2 : forall (n : nat), extend_subst 0 (shift) n = n.
Proof. induction n. simpl. reflexivity.  unfold shift. simpl. rewrite Nat.add_1_r. reflexivity. Qed.   
 
Lemma res_prefix_in : forall (P : proc) (V : value) (n: nat) (ref : List.list (nat * nat)),
  Res(Par (In n P) (encode_value V ref)) ~~ In n (Res(Par (P) (encode_value V ref))).
Proof. Admitted.

Lemma res_prefix_out : forall (P : proc) (V : value) (n m: nat) (ref : List.list (nat * nat)),
 ~(m = 0) -> (Res(Par (Out n m P) (encode_value V ref)) ~~ In n (Res(Par (P) (encode_value V ref)))).
Proof. Admitted.

Lemma pointer : forall
  (P Q : proc) 
  (x y : nat) 
  (V : value) 
  (ref : List.list (nat * nat)),
  Res (Par (Par (P) (Q)) (encode_value V ref)) ~~ 
  Res (Res (Par 
    (Par ((P[[shift]])[[swap]]) (Q[[shift]]) ) 
    (Par
      (((encode_value V (incRefs 0 1 ref))[[shift]])[[swap]]) 
      ((encode_value V (incRefs 0 1 ref))[[shift]])
    )
  )).
Proof. Admitted.

Lemma split : forall
  (P Q: proc)
  (V : value)
  (ref : List.list (nat * nat)),
  Res (Res (Par
    (Par (P [[shift]] [[swap]]) (Q [[shift]]))
    (Par
      (encode_value V (incRefs 0 1 ref) [[shift]] [[swap]])
      (encode_value V (incRefs 0 1 ref) [[shift]])
    )
  )) ~~
  Par
    (Res (Par P (encode_value V ref)))
    (Res (Par Q (encode_value V ref)))
  .
Proof.
Admitted.

Lemma res_rep : forall 
  (P : proc) 
  (V : value) 
  (ref : List.list (nat * nat)),
  Res (Par (Rep (P)) (encode_value V ref) ) ~~ 
  Rep (Res (Par (P) (encode_value V ref))).
Proof.
  cofix CH.
  intros p v r.
  apply weak_trans with 
    (q := Res (Par (Par p (Rep p)) (encode_value v r))).
  - apply weak_struct. 
    apply con_res.
    apply con_par.
    * apply sg_rep.
    * apply sg_ref.
  - eapply weak_trans.
    * apply pointer.
      + exact 0.
      + exact 1.
    * apply weak_sym.
      eapply weak_trans.
      + apply weak_struct. apply sg_rep.
      + { apply weak_sym.
          eapply weak_trans.
          - apply split.
          - apply weak_par1.
            * apply weak_reflexive.
            * apply CH.
        }
Qed.

Lemma sub_lemma : forall (M : term) (V : value) (u r : nat) (ref : List.list (nat * nat)),
encode (M [l[(extend_subst_lam V Var)]l]) u r ref ~~ Res ( Par ((encode M (u+1) (r+1) (incRefs 0 1 ref))) (encode_value V ref)).  
Proof. Admitted.

Lemma res_weak : forall (P P': proc), P =()> P' -> Res P =()> Res P'.
Proof. intros. induction H.
- apply TPRE_INTERNAL with (r := Res r) (q := Res q).
 split. apply RES22. apply H. apply TPRE_INTERNAL with (q := q). destruct H. admit.
- apply ACTION. apply RES22. apply H.
- apply TAU.
Admitted.

Lemma weak_par : forall (P Q P': proc), P =()> P' -> Par P Q =()> Par P' Q.
Proof. intros. induction H.
- apply TPRE_INTERNAL with (r := Par r Q) (q := Par q Q).
 split. apply TPAR1. apply H. apply TPRE_INTERNAL with (q := q). destruct H. admit.
- apply ACTION. apply TPAR1. apply H.
- apply TAU.
Admitted.


Theorem Sound_encoding : 
forall (M N : term), M --> N -> (forall (u r : nat),(exists (P' : proc), (encode M u r List.nil) =()> P' 
  /\ (P' ~~ (encode N u r List.nil)))). 
Proof. intro. intro. intro. induction H.
  - simpl. intros. 
  exists (Res(Res(
    (Par
       (Res
          
             (encode_value v Datatypes.nil [[swap]]) )
       (
          ((encode s (u + 2) (r + 2)
             ((0, 0) :: Datatypes.nil)[[0 |> shift]]))))))).
    split.
    + apply ACTION. apply RES22. apply COM22 with (n := 0).
    * apply BORESBOUT with (n := 0). apply BORES1.  apply OUT.
    * apply INB with (m := 0).
    +  admit. 
  - intros. destruct (IHreduction 0 1). simpl.  exists (Res
    (Par (Res (x))
       (In 0 (encode t (u + 2) (r + 2) ((0, 0) :: Datatypes.nil))))).
  split.
  + simpl. apply res_weak. apply weak_par. apply res_weak. apply H0. 
  + apply weak_res. apply weak_par1. apply weak_res. apply H0. apply weak_reflexive.
- simpl. intros. exists (Res (Res (Res (Par (Par ((encode s (u+3) (r+3) Datatypes.nil)) ((Rep(In 0 (In 0 (In 1 (encode s 1 0 Datatypes.nil)))))[[shift]]))  (Nil) )))).
  split. eapply TPRE_INTERNAL. 
  split. apply RES22. apply COM22 with (n := 0). apply BORES1. apply OUT.
  apply INB. eapply TPRE_INTERNAL.
  split. apply RES22. apply RES22. eapply COM21. apply IBREP. apply IBPAR1. apply INB.
  apply BORES1. apply OUT. eapply TPRE_INTERNAL.
  split. apply RES22. apply RES22. apply RES22. eapply COM11. apply IPAR1. apply IN.
  apply OUT. fold int_subst.
  apply ACTION. apply RES22. apply RES22. apply RES22. eapply COM11. apply IPAR1. (** apply IN **)
  
  
  Admitted.

Theorem Complete_encoding : 
forall (M : term) (P : proc) (u r : nat), (encode M u r List.nil) -(a_tau)> P 
  -> (exists (P' : proc) (N : term),  P =()> P' 
  /\ (P' ~~ (encode N u r List.nil)) /\ (M --> N \/ M = N)).
Proof. intro. induction M. intros.
  - induction H. 
  * 
  Admitted.


