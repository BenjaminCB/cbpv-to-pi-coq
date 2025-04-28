Require Import Coq.Program.Basics.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Nat.
Require Import Bool.
Require Import Coq.Relations.Relation_Operators. 

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive proc : Type :=
| In (n : nat) (p : proc)
| Out (n : nat) (p : proc)
| Res (p : proc)
| Rep (p : proc)
| Par (p q : proc)
| Link (n m : nat)
| Nil.

Definition id (n : nat) := n.

Definition shift (n : nat) := n + 1.

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
  extend_subst 0 (subst >>> shift).

Fixpoint int_subst (p : proc) (subst : nat -> nat) :=
  match p with
  | In n p => In (subst n) (int_subst p (lift_subst subst))
  | Out n p => Out (subst n) (int_subst p (lift_subst subst))
  | Res p => Res (int_subst p (lift_subst subst))
  | Rep p => Rep (int_subst p subst)
  | Par p q => Par (int_subst p subst) (int_subst q subst)
  | Link n m => Link (subst n) (subst m)
  | Nil => Nil
  end.

Notation "p [[ subst ]]" := (int_subst p subst) (at level 90, left associativity).
Notation "v |> subst" := (extend_subst v subst) (at level 81, left associativity).

Inductive act : Set :=
  | a_tau : act
  | a_in: nat -> act
  | a_out: nat -> act.
  
Definition dual_act (a : act) := 
  match a with
  | a_tau => a_tau
  | a_in n => a_out n
  | a_out n => a_in n
  end.
  
Notation "~ a ~" := (dual_act a) (at level 90, left associativity).

Definition int_subst_act (a : act) (subst : nat -> nat) :=
  match a with
  | a_tau => a_tau
  | a_in n => a_in (subst n)
  | a_out n => a_out (subst n)
  end.
  
Notation "a (+1)" := (int_subst_act a shift) (at level 90, left associativity).

Reserved Notation "P -( a )> Q" (at level 70).

Inductive trans: proc -> act -> proc -> Prop := 
  | OUT   (n : nat) (P : proc): 
    (Out n P) -( a_out n )> P
  | IN    (n : nat) (P: proc): 
    (In n P) -( a_in n )> P
  | PAR_L (a : act) (P Q R : proc):
    a <> a_tau -> P -( a )> R -> Par P Q -( a )> Par R (Q[[shift]])
  | PAR_R (a : act) (P Q R : proc):
    a <> a_tau -> Q -( a )> R -> Par P Q -( a )> Par (P[[shift]]) R
  | PAR_L_TAU (P Q R : proc):
    P -( a_tau )> R -> Par P Q -( a_tau )> Par R Q
  | PAR_R_TAU (P Q R : proc):
    Q -( a_tau )> R -> Par P Q -( a_tau )> Par P R
  | RES (a : act) (P Q : proc):
    a <> a_tau -> P -( a (+1) )> Q -> Res P -( a )> Res (Q[[swap]])
  | RES_TAU (P Q : proc):
    P -( a_tau )> Q -> Res P -( a_tau )> Res Q
  | COM (a : act) (n : nat) (P Q R S : proc):
    a <> a_tau -> P -( a )> R -> Q -( ~a~ )> S -> Par P Q -( a_tau )> Res (Par R S)
  | REP (a : act) (P Q : proc): 
    (Par P (Rep P)) -( a )> Q -> (Rep P) -( a )> Q
  | LINK (n m : nat) (P : proc):
    In n (Out (m + 1) (Link 0 1)) -( a_in n )> P -> Link n m -( a_in n )> P

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

Fixpoint ref_n_in_proc (n : nat) (p : proc) : bool :=
  match p with
  | In m q =>
      if n =? m
      then true
      else ref_n_in_proc (n + 1) q
  | Out m q =>
      if (n =? m)
      then true
      else ref_n_in_proc n q
  | Res q => ref_n_in_proc (n + 1) q
  | Rep q => ref_n_in_proc n q
  | Par q q' => (ref_n_in_proc n q) || (ref_n_in_proc n q')
  | Link m m' => (n =? m) || (n =? m')
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
  | nil : forall p, p === (Par p Nil)
  | sym : forall p q, (Par p q) === (Par q p)
  | con_par : forall p q r s, p === r -> q === s -> (Par p q) === (Par r s) 
  | con_res : forall p q, p === q -> (Res p) === (Res q)
  | sg_ref : forall p, p === p
  | sg_sym : forall p q, p === q -> q === p
  | sg_trans : forall p q r, p === q -> q === r -> p === r
  | sg_rep : forall p, (Rep p) === (Par p (Rep p))
  | sg_par_res_r : forall p q, ref_n_in_proc 0 p = false -> (Res (Par p q)) === (Par (p[[0 |> id]]) (Res q))
  | sg_par_res_l : forall p q, ref_n_in_proc 0 q = false -> (Res (Par p q)) === (Par (Res p) (q[[0 |> id]]))
  | par_assoc : forall p q r, (Par (Par p q) r) === (Par p (Par q r))
  | par_swap : forall p q r s, (Par (Par p q) (Par r s)) === (Par (Par p r) (Par q s))

  where "P === Q" := (struct_cong P Q).

Reserved Notation "P ~~ Q" (at level 70).

CoInductive weak_bisimilar : proc -> proc -> Prop :=
  | wb : forall p q,
      (forall a p',
        p -( a )> p' ->
        exists q',
          q =( a )> q' /\
          weak_bisimilar p' q') ->
      (forall a q',
        q -( a )> q' ->
        exists p',
          p =( a )> p' /\
          weak_bisimilar p' q') ->
      weak_bisimilar p q
  | wb_ref : forall p, weak_bisimilar p p
  | wb_trans : forall p q r, weak_bisimilar p q -> weak_bisimilar q r -> weak_bisimilar p r
  | wb_sym : forall p q, weak_bisimilar p q -> weak_bisimilar q p
  | wb_struct : forall p q, struct_cong p q -> weak_bisimilar p q
  | wb_res : forall p q, weak_bisimilar p q -> weak_bisimilar (Res p) (Res q)
  | wb_par : forall p q r s, weak_bisimilar p q -> weak_bisimilar r s -> weak_bisimilar (Par p r) (Par q s)
  | wb_in : forall n p q, weak_bisimilar p q -> weak_bisimilar (In n p) (In n q)
  | wb_out : forall n p q, weak_bisimilar p q -> weak_bisimilar (Out n p) (Out n q)
  | wb_rep : forall p q, weak_bisimilar p q -> weak_bisimilar (Rep p) (Rep q)

  where "P ~~ Q" := (weak_bisimilar P Q).
  