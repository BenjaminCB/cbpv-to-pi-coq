Require Import Coq.Program.Basics.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive term : Type :=
| Val (v : value)
| Abs (s : term)
| App (s : term) (v : value)
| Force (v : value)
| Ret (v : value)
| Bind (s t : term)

with value : Type :=
| Var (n : nat)
| Thunk (s : term).

Definition id (n : nat) := n.

Definition shift (n : nat) := n + 1.

Definition extend_rn (s : nat) (rn : nat -> nat) (n : nat) := 
  match n with
  | 0 => s
  | S n => rn n
  end.

Definition lift_rn (rn : nat -> nat) := extend_rn 0 (rn >>> shift).

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
  | Var n => Var (rn n)
  | Thunk s => Thunk (int_rn s rn)
  end.

Notation "s << rn >>" := (int_rn s rn) (at level 90, left associativity).
Notation "v <.< rn >.>" := (int_rn_value v rn) (at level 90, left associativity).

Definition extend_subst (v : value) (subst : nat -> value) (n : nat) := 
  match n with
  | 0 => v
  | S n => subst n
  end.

Notation "v |> subst" := (extend_subst v subst) (at level 81, left associativity).

Definition compose_subst_int_rn 
  (subst : nat -> value)
  (rn : nat -> nat)
  (n : nat) 
  := int_rn_value (subst n) rn.

Definition lift_subst (subst : nat -> value) := 
  extend_subst (Var 0) (compose_subst_int_rn subst shift).

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
  | Var n => subst n
  | Thunk s => Thunk (int_subst s subst)
  end.

Notation "s [[ subst ]]" := (int_subst s subst) (at level 90, left associativity).
Notation "v [.[ subst ].]" := (int_subst_value v subst) (at level 90, left associativity).

Definition compose_subst_int_subst
  (subst subst' : nat -> value)
  (n : nat) 
  := (subst n)[.[subst'].].


Theorem stable_substitution:
  forall (s : term), 
  forall (v : value),
  forall subst : nat -> value, 
  ((s[[^ subst]])[[(v[.[subst].]) |> Var]]) = 
    ((s[[v |> Var]])[[subst]]).
Proof.
  intros s t subst.
  induction s as [ v | s' ih | s' t' ih ].
  - admit.
  - admit.
  - admit.
Qed.