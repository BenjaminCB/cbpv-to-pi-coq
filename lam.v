Require Import Coq.Program.Basics.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive term : Type :=
| Var (n : nat)
| Abs (s : term)
| App (s t : term).

Definition id (n : nat) := n.

Definition shift (n : nat) := n + 1.

Definition extend_rn (s : nat) (rn : nat -> nat) (n : nat) := 
  match n with
  | 0 => s
  | S n => rn n
  end.

Definition lift_rn (rn : nat -> nat) := extend_rn 0 (rn >>> shift).

(* Int stands for instantiate *)
Fixpoint int_rn (s : term) (rn : nat -> nat) :=
  match s with
  | Var n => Var (rn n)
  | Abs s => Abs (int_rn s (lift_rn rn))
  | App s t => App (int_rn s rn) (int_rn t rn)
  end.

Notation "s << rn >>" := (int_rn s rn) (at level 90, left associativity).

Definition extend_subst (s : term) (subst : nat -> term) (n : nat) := 
  match n with
  | 0 => s
  | S n => subst n
  end.

Notation "s |> subst" := (extend_subst s subst) (at level 81, left associativity).

Definition compose_subst_int_rn 
  (subst : nat -> term)
  (rn : nat -> nat)
  (n : nat) 
  := (subst n)<<rn>>.

Definition lift_subst (subst : nat -> term) := 
  extend_subst (Var 0) (compose_subst_int_rn subst shift).

Notation "^ subst" := (lift_subst subst) (at level 81, left associativity).

Fixpoint int_subst (s : term) (subst : nat -> term) :=
  match s with
  | Var n => subst n
  | Abs s => Abs (int_subst s (lift_subst subst))
  | App s t => App (int_subst s subst) (int_subst t subst)
  end.

Notation "s [[ subst ]]" := (int_subst s subst) (at level 90, left associativity).

Definition compose_subst_int_subst
  (subst subst' : nat -> term)
  (n : nat) 
  := (subst n)[[subst']].

Theorem stable_substitution:
  forall (s t : term), 
  forall subst : nat -> term, 
  ((s[[^ subst]])[[(t[[subst]]) |> Var]]) = 
    ((s[[t |> Var]])[[subst]]).
Proof.
  intros s t subst.
  induction s as [ v | s' ih | s' t' ih ].
  - admit.
  - admit.
  - admit.
Qed.
  
  

