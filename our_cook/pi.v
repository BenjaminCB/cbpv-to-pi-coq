Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Coq.Relations.Relation_Operators.
From Coq Require Import String Ascii.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive name : Type :=
| BN (n : nat)
| FN (s : string).

Inductive proc : Type :=
| In (ch : name) (p : proc)
| Out (ch : name) (p : proc)
| Res (p : proc)
| Rep (p : proc)
| Par (p q : proc)
| Link (n m : name)
| Nil.

Inductive wf_name : nat -> name -> Prop :=
  | WF_BN (limit : nat) (n : nat):
    n < limit -> wf_name limit (BN n)
  | WF_FN (limit : nat) (s : string):
    wf_name limit (FN s).

Inductive wf_proc : nat -> proc -> Prop :=
  | WF_IN (limit : nat) (ch : name) (p : proc):
    wf_name limit ch ->
    wf_proc (S limit) p ->
    wf_proc limit (In ch p)
  | WF_OUT (limit : nat) (ch : name) (p : proc):
    wf_name limit ch ->
    wf_proc (S limit) p ->
    wf_proc limit (Out ch p)
  | WF_RES (limit : nat) (p : proc):
    wf_proc (S limit) p ->
    wf_proc limit (Res p)
  | WF_REP (limit : nat) (p : proc):
    wf_proc limit p ->
    wf_proc limit (Rep p)
  | WF_PAR (limit : nat) (p q : proc):
    wf_proc limit p ->
    wf_proc limit q ->
    wf_proc limit (Par p q)
  | WF_LINK (limit : nat) (n m : name):
    wf_name limit n ->
    wf_name limit m ->
    wf_proc limit (Link n m)
  | WF_NIL (limit : nat):
    wf_proc limit Nil.

Inductive context : Type :=
| CHole 
| CIn (ch : name) (c : context)
| COut (ch : name) (c : context)
| CRes (c : context)
| CRep (c : context)
| CParL (c : context) (p : proc)
| CParR (p : proc) (c : context).

Fixpoint plug (c : context) (p : proc) :=
  match c with
  | CHole => p
  | CIn n c' => In n (plug c' p)
  | COut n c' => Out n (plug c' p)
  | CRes c' => Res (plug c' p)
  | CRep c' => Rep (plug c' p)
  | CParL c' p' => Par (plug c' p) p'
  | CParR p' c' => Par p' (plug c' p)
  end.

Definition id (n : nat) := n.

Definition swap (n : nat) :=
  match n with
  | 0 => 1
  | S 0 => 0
  | S n => S n
  end.

Definition extend_subst (s : nat) (subst : nat -> nat) (n : nat) := 
  match n with
  | 0 => s
  | S n => subst n
  end.

Definition lift_subst (subst : nat -> nat) := 
  extend_subst 0 (subst >>> S).

Fixpoint int_subst (p : proc) (subst : nat -> nat) :=
  match p with
  | In (FN n) p => In (FN n) (int_subst p (lift_subst subst))
  | In (BN n) p => In (BN (subst n)) (int_subst p (lift_subst subst))
  | Out (FN n) p => Out (FN n) (int_subst p (lift_subst subst))
  | Out (BN n) p => Out (BN (subst n)) (int_subst p (lift_subst subst))
  | Res p => Res (int_subst p (lift_subst subst))
  | Rep p => Rep (int_subst p subst)
  | Par p q => Par (int_subst p subst) (int_subst q subst)
  | Link (FN n) (FN m) => Link (FN n) (FN m)
  | Link (FN n) (BN m) => Link (FN n) (BN (subst m))
  | Link (BN n) (FN m) => Link (BN (subst n)) (FN m)
  | Link (BN n) (BN m) => Link (BN (subst n)) (BN (subst m))
  | Nil => Nil
  end.

Notation "p [[ subst ]]" := (int_subst p subst) (at level 90, left associativity).
Notation "v []> subst" := (extend_subst v subst) (at level 81, left associativity).

Inductive act : Set :=
  | a_tau : act
  | a_in: name -> act
  | a_out: name -> act.
  
Definition dual_act (a : act) := 
  match a with
  | a_tau => a_tau
  | a_in ch => a_out ch
  | a_out ch => a_in ch
  end.
  
Notation "~ a ~" := (dual_act a) (at level 90, left associativity).

Definition int_subst_act (a : act) (subst : nat -> nat) :=
  match a with
  | a_tau => a_tau
  | a_in (FN n) => a_in (FN n)
  | a_in (BN n) => a_in (BN (subst n))
  | a_out (FN n) => a_out (FN n)
  | a_out (BN n) => a_out (BN (subst n))
  end.
  
Notation "a (+1)" := (int_subst_act a S) (at level 90, left associativity).

Definition incName (n : name) := 
  match n with
  | FN n => FN n
  | BN n => BN (S n)
  end.

Reserved Notation "P -( a )> Q" (at level 70).

Inductive trans: proc -> act -> proc -> Prop := 
  | OUT (n : name) (P : proc): 
    (Out n P) -( a_out n )> P
  | IN (n : name) (P: proc): 
    (In n P) -( a_in n )> P
  | PAR_L (a : act) (P Q R : proc):
    a <> a_tau -> P -( a )> R -> Par P Q -( a )> Par R (Q[[S]])
  | PAR_R (a : act) (P Q R : proc):
    a <> a_tau -> Q -( a )> R -> Par P Q -( a )> Par (P[[S]]) R
  | PAR_L_TAU (P Q R : proc):
    P -( a_tau )> R -> Par P Q -( a_tau )> Par R Q
  | PAR_R_TAU (P Q R : proc):
    Q -( a_tau )> R -> Par P Q -( a_tau )> Par P R
  | RES (a : act) (P Q : proc):
    a <> a_tau -> P -( a (+1) )> Q -> Res P -( a )> Res (Q[[swap]])
  | RES_TAU (P Q : proc):
    P -( a_tau )> Q -> Res P -( a_tau )> Res Q
  | COM (a : act) (P Q R S : proc):
    a <> a_tau -> P -( a )> R -> Q -( ~a~ )> S -> Par P Q -( a_tau )> Res (Par R S)
  | REP (a : act) (P Q : proc): 
    (Par P (Rep P)) -( a )> Q -> (Rep P) -( a )> Q
  | LINK (n m : name) (P : proc):
    Rep (In n (Out (incName m) (Link (BN 0) (BN 1)))) -( a_in n )> P -> Link n m -( a_in n )> P

  where "P -( a )> Q" := (trans P a Q).

Definition tau_step (P Q : proc) := P -( a_tau )> Q.

Notation "P -()> Q"   := (tau_step P Q) (at level 60).
Notation "P =()> Q"  := (clos_refl_trans _ tau_step P Q) (at level 60).

Reserved Notation "P =( a )> Q" (at level 70).

Inductive weak_trans: proc -> act -> proc -> Prop := 
  | WT_TAU (P Q : proc):
    P =()> Q -> P =( a_tau )> Q
  | WT_VIS (P P' Q' Q : proc) (a : act) :
    a <> a_tau -> P =()> P' -> P' -(a)> Q' -> Q' =()> Q -> P =( a )> Q
 
  where "P =( a )> Q" := (weak_trans P a Q).

Reserved Notation "P --( A )> Q" (at level 70).

Fixpoint hup (c : context) :=
  match c with
  | CHole => false
  | CIn _ _ => true
  | COut _ _ => true
  | CRes c => hup c
  | CRep c => hup c
  | CParL c _ => hup c
  | CParR _ c => hup c
  end.

Lemma wt_tau_context:
  forall c p q,
    hup c = false ->
    p =()> q ->
    plug c p =()> plug c q.
Proof.
Admitted.

Fixpoint ref_n_in_proc (n : nat) (p : proc) : bool :=
  match p with
  | In (BN m) q =>
      if n =? m
      then true
      else ref_n_in_proc (n + 1) q
  | In (FN _) q => ref_n_in_proc (n + 1) q
  | Out (BN m) q =>
      if (n =? m)
      then true
      else ref_n_in_proc n q
  | Out (FN _) q => ref_n_in_proc (n + 1) q
  | Res q => ref_n_in_proc (n + 1) q
  | Rep q => ref_n_in_proc n q
  | Par q q' => (ref_n_in_proc n q) || (ref_n_in_proc n q')
  | Link (FN _) (FN _) => false
  | Link (FN _) (BN m) => (n =? m)
  | Link (BN m) (FN _) => (n =? m)
  | Link (BN m) (BN m') => (n =? m) || (n =? m')
  | Nil => false
  end.

Fixpoint applier (constructor : proc -> proc) (n : nat) (p : proc) :=
  match n with
  | 0 => p
  | S n => constructor (applier constructor n p)
  end.

Notation "constructor ^^ n" := (applier constructor n) (at level 90, left associativity).

Reserved Notation "P === Q" (at level 70).

Inductive struct_cong : proc -> proc -> Prop :=
  | add_nil : forall p, p === (Par p Nil)
  | del_nil : forall p, (Par p Nil) === p
  | res_nil : (Res Nil) === Nil
  | sym : forall p q, (Par p q) === (Par q p)
  | con_par : forall p q r s, p === r -> q === s -> (Par p q) === (Par r s) 
  | con_res : forall p q, p === q -> (Res p) === (Res q)
  | sg_ref : forall p, p === p
  | sg_sym : forall p q, p === q -> q === p
  | sg_trans : forall p q r, p === q -> q === r -> p === r
  | sg_rep : forall p, (Rep p) === (Par p (Rep p))
  | sg_par_res_r : forall p q, ref_n_in_proc 0 p = false -> (Res (Par p q)) === (Par (p[[0 []> id]]) (Res q))
  | sg_par_res_l : forall p q, ref_n_in_proc 0 q = false -> (Res (Par p q)) === (Par (Res p) (q[[0 []> id]]))
  | par_assoc : forall p q r, (Par (Par p q) r) === (Par p (Par q r))
  | par_swap : forall p q r s, (Par (Par p q) (Par r s)) === (Par (Par p r) (Par q s))
  | par_flatten : forall p q r s, (Par (Par p q) (Par r s)) === (Par (Par (Par p q) r) s)

  where "P === Q" := (struct_cong P Q).
 
Reserved Notation "P ~~ Q" (at level 70).

CoInductive weak_bisimilar : proc -> proc -> Prop :=
  | wb : forall p q,
      (forall a p',
        p -( a )> p' ->
        exists q',
          q =( a )> q' /\
          weak_bisimilar p' q') /\
      (forall a q',
        q -( a )> q' ->
        exists p',
          p =( a )> p' /\
          weak_bisimilar p' q') ->
      weak_bisimilar p q
  | wb_struct : forall p q, p === q -> p ~~ q
  | wb_con : forall c p q, p ~~ q -> (plug c p) ~~ (plug c q)

  where "P ~~ Q" := (weak_bisimilar P Q).
  
Lemma wb_ref:
  forall p, 
    p ~~ p.
Proof.
  cofix CH.
  intros p.
  apply wb.
  split.
  - intros a p' Htrans.
    exists p'.
    split.
    destruct a.
    apply WT_TAU.
    apply rt_step.
    apply Htrans.
    eapply WT_VIS.
    discriminate.
    apply rt_refl.
    apply Htrans.
    apply rt_refl.
    eapply WT_VIS.
    discriminate.
    apply rt_refl.
    apply Htrans.
    apply rt_refl.
    apply CH.
  - intros a p' Htrans.
    exists p'.
    split.
    destruct a.
    apply WT_TAU.
    apply rt_step.
    apply Htrans.
    eapply WT_VIS.
    discriminate.
    apply rt_refl.
    apply Htrans.
    apply rt_refl.
    eapply WT_VIS.
    discriminate.
    apply rt_refl.
    apply Htrans.
    apply rt_refl.
    apply CH.
Qed.

Lemma wb_sym:
  forall p q,
    p ~~ q -> q ~~ p.
Proof.
  cofix CH.
  intros p q Hbisim.
  inversion Hbisim.
  destruct H as [Hpq Hqp].
  
  apply wb.
  split.
  intros a p' Htrans.
  destruct (Hqp _ _ Htrans) as [r [HqStep HqBisim] ].
  exists r.
  split.
  apply HqStep.
  apply CH.
  apply HqBisim.
  intros a p' Htrans.
  destruct (Hpq _ _ Htrans) as [r [HqStep HqBisim] ].
  exists r.
  split.
  apply HqStep.
  apply CH.
  apply HqBisim.
  
  (* unguarded i think *)
  apply CH.
  apply Hbisim.
  
  apply wb_con.
  apply CH.
  apply H.
Admitted.


Lemma wb_trans:
  forall p q r,
    p ~~ q -> q ~~ r -> p ~~ r.
Proof.
Admitted.

Lemma wb_par:
  forall p q r s,
    p ~~ q -> r ~~ s -> Par p r ~~ Par q s.
Proof.
Admitted.