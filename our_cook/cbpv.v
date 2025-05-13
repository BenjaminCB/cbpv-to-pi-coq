Require Import Coq.Program.Basics.
From Coq Require Import String Ascii.
Require Import PeanoNat.
From Coq Require Import Lia.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive var : Type :=
| BV (n : nat)
| FV (s : string).

Inductive term : Type :=
| Val (v : value)
| Abs (s : term)
| App (s : term) (v : value)
| Force (v : value)
| Ret (v : value)
| Bind (s t : term)

with value : Type :=
| Var (n : var)
| Thunk (s : term).

Inductive wf_var : nat -> var -> Prop :=
  | WF_BV (limit : nat) (n : nat):
    n < limit -> wf_var limit (BV n)
  | WF_FV (limit : nat) (s : string):
    wf_var limit (FV s).
    
Inductive wf_term : nat -> term -> Prop :=
  | WF_VAL (limit : nat) (v : value):
    wf_value limit v ->
    wf_term limit (Val v)
  | WF_ABS (limit : nat) (s : term):
    wf_term (S limit) s ->
    wf_term limit (Abs s)
  | WF_APP (limit : nat) (s : term) (v : value):
    wf_term limit s ->
    wf_value limit v ->
    wf_term limit (App s v)
  | WF_FORCE (limit : nat) (v : value):
    wf_value limit v ->
    wf_term limit (Force v)
  | WF_RET (limit : nat) (v : value):
    wf_value limit v ->
    wf_term limit (Ret v)
  | WF_BIND (limit : nat) (s t : term):
    wf_term limit s ->
    wf_term (S limit) t ->
    wf_term limit (Bind s t)

with wf_value : nat -> value -> Prop :=
  | WF_VAR (limit : nat) (n : var):
    wf_var limit n ->
    wf_value limit (Var n)
  | WF_THUNK (limit : nat) (s : term):
    wf_term limit s ->
    wf_value limit (Thunk s).

Definition id (n : nat) := n.

Definition extend_rn (s : nat) (rn : nat -> nat) (n : nat) := 
  match n with
  | 0 => s
  | S n => rn n
  end.

Definition lift_rn (rn : nat -> nat) := extend_rn 0 (rn >>> S).

Fixpoint int_rn (s : term) (rn : nat -> nat) :=
  match s with
  | Val v => Val (int_rn_value v rn)
  | Abs s => Abs (int_rn s (lift_rn rn))
  | App s v => App (int_rn s rn) (int_rn_value v rn)
  | Force v => Force (int_rn_value v rn)
  | Ret v => Ret (int_rn_value v rn)
  | Bind s t => Bind (int_rn s rn) (int_rn t (lift_rn rn))
  end

with int_rn_value (v : value) (rn : nat -> nat) :=
  match v with
  | Var (BV n) => Var (BV (rn n))
  | Var (FV n) => Var (FV n)
  | Thunk s => Thunk (int_rn s rn)
  end.

Notation "s << rn >>" := (int_rn s rn) (at level 90, left associativity).
Notation "v <.< rn >.>" := (int_rn_value v rn) (at level 90, left associativity).

Definition extend_subst_lam (v : value) (subst : nat -> value) (n : nat) := 
  match n with
  | 0 => v
  | S n' => subst n'
  end.

Notation "v {}> subst" := (extend_subst_lam v subst) (at level 81, left associativity).

Definition compose_subst_int_rn 
  (subst : nat -> value)
  (rn : nat -> nat)
  (n : nat) 
  := int_rn_value (subst n) rn.

Definition lift_subst (subst : nat -> value) := 
  extend_subst_lam (Var (BV 0)) (compose_subst_int_rn subst S).

Notation "^ subst" := (lift_subst subst) (at level 81, left associativity).

Fixpoint int_subst (s : term) (subst : nat -> value) :=
  match s with
  | Val v => Val (int_subst_value v subst)
  | Abs s => Abs (int_subst s (lift_subst subst))
  | App s v => App (int_subst s subst) (int_subst_value v subst)
  | Force v => Force (int_subst_value v subst)
  | Ret v => Ret (int_subst_value v subst)
  | Bind s t => Bind (int_subst s subst) (int_subst t (lift_subst subst))
  end

with int_subst_value (v : value) (subst : nat -> value) :=
  match v with
  | Var (BV n) => subst n
  | Var (FV n) => Var (FV n)
  | Thunk s => Thunk (int_subst s subst)
  end.

Notation "s {{ subst }}" := (int_subst s subst) (at level 90, left associativity).
Notation "v {.{ subst }.}" := (int_subst_value v subst) (at level 90, left associativity).

Definition compose_subst_int_subst
  (subst subst' : nat -> value)
  (n : nat) 
  := (subst n){.{subst'}.}.
  
(* TODO verify that substitution works correctly *)

Reserved Notation "s --> t" (at level 70).

Inductive reduction: term -> term -> Prop :=
  | BINDING_BASE (v : value) (s : term): 
    (Bind (Ret v) s) --> (s {{v {}> (Var <<< BV)}})
  | BINDING_EVOLVE (s t s' : term):
    s --> s' -> (Bind s t) --> (Bind s' t)
  | FORCE_THUNK (s : term):
    (Force (Thunk s)) --> (s)
  | APPLICATION_BASE (s : term) (v : value):
    (App (Abs s) v) -->(s {{v {}> (Var <<< BV)}})
  | APPLICATION_EVOLVE (s t : term) (v : value):
    s --> t -> (App s v) --> (App t v)
  
  where "s --> t" := (reduction s t).

Lemma wf_red:
  forall s t,
    wf_term 0 s ->
    s --> t ->
    wf_term 0 t.
Proof.
  intros s t Hwf Hred.
  induction Hred.
  - inversion Hwf.
    inversion H2.
    subst.
    induction s.
    * destruct v0.
      destruct n.
      destruct n.
      simpl.
      inversion H2.
      apply WF_VAL.
      apply H1.
      
      inversion H3.
      inversion H1.
      inversion H7.
      lia.
      
      simpl.
      apply WF_VAL.
      apply WF_VAR.
      apply WF_FV.
      
      simpl.
      apply WF_VAL.
      apply WF_THUNK.
Admitted.

Lemma wf_term_extend:
  forall n s,
    wf_term n s -> wf_term (S n) s.
Proof.
Admitted.

Lemma wf_term_subst:
  forall s v,
    wf_term 1 s ->
    wf_value 0 v ->
    wf_term 0 (s {{v {}> Var <<< BV}}).
Proof.
Admitted.

