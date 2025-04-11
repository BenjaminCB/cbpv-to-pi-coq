Require Import Coq.Program.Basics.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive proc : Type :=
| In (n : nat) (p : proc)
| Out (n m : nat) (p : proc)
| Res (p : proc)
| Rep (p : proc)
| Par (p q : proc)
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
  | Out n m p => Out (subst n) (subst m) (int_subst p subst)
  | Res p => Res (int_subst p (lift_subst subst))
  | Rep p => Rep (int_subst p subst)
  | Par p q => Par (int_subst p subst) (int_subst q subst)
  | Nil => Nil
  end.

Notation "p [[ subst ]]" := (int_subst p subst) (at level 90, left associativity).
Notation "v |> subst" := (extend_subst v subst) (at level 81, left associativity).

Inductive act : Set :=
  | a_tau : act
  | a_out: nat -> nat -> act
  | a_in: nat -> nat -> act
  | a_bout: nat -> act.

Reserved Notation "P -( a )> Q" (at level 70).

Inductive trans: proc -> act -> proc -> Prop := 
  | OUT   (n m : nat) (P : proc): 
    trans (Out n m P) (a_out n m) P  
  | IN    (n m : nat) (P: proc): 
    trans (In n P) (a_in n m) (P[[m |> id]])
  | PAR1 (a : act) (n m : nat) (P Q R: proc):
    a = a_in n m \/ a = a_tau \/ a = a_out n m ->
    trans P a R -> trans (Par P Q) a (Par R Q)
  | PAR12 (a : act) (n m : nat) (P Q R: proc):
    a = a_in n m \/ a = a_tau \/ a = a_out n m ->
    trans Q a R -> trans (Par P Q) a (Par P R)
  | PAR2  (a : act) (n : nat) (P Q R : proc):
    trans P (a_bout n) R -> trans (Par P Q) (a_bout n) (Par R (Q[[shift]]))
  | RES1  (n : nat) (P R : proc):
    trans P (a_out (n + 1) 0 ) R -> trans (Res P) (a_bout n) R
  | RES21 (a : nat -> nat -> act) (n m : nat) (P Q : proc) :
    a = a_out \/ a = a_in ->
    trans P (a (n + 1) (m + 1)) Q -> 
    trans (Res P) (a n m) (Res Q)
  | RES22 (P Q : proc) :
    trans P (a_tau) Q -> 
    trans (Res P) (a_tau) (Res Q)
  | RESBOUT (n : nat) (P Q : proc) :
    trans P (a_bout (n+1)) Q -> trans (Res P) (a_bout n) (Res (Q[[swap]]))
  | COM11  (n m : nat) (P Q R S : proc) :
    trans P (a_in n m) R ->
    trans Q (a_out n m) S ->
    trans (Par P Q) a_tau (Par (R) S)
  | COM12  (n m : nat) (P Q R S : proc) :
    trans P (a_out n m) R ->
    trans Q (a_in n m) S ->
    trans (Par P Q) a_tau (Par R (S))
  | COM21  (n : nat) (P Q R S : proc) :
    trans P (a_in n 0) R ->
    trans Q (a_bout n) S ->
    trans (Par P Q) a_tau (Res (Par R S))
  | COM22  (n : nat) (P Q R S : proc) :
    trans P (a_bout n) R ->
    trans Q (a_in n 0) S ->
    trans (Par P Q) a_tau (Res (Par R S))
  | REP   (a : act) (P Q: proc) : 
    trans (Par P (Rep P)) a Q -> trans (Rep P) a Q
 
  where "P -( a )> Q" := (trans P a Q).

Reserved Notation "P =( a )> Q" (at level 70).

Inductive weak_trans: proc -> act -> proc -> Prop := 
  | PRE_INTERNAL (p q r : proc) (a : act) :
    p -( a_tau )> q /\ q =( a )> r -> p =( a )> r
  | ACTION (p q : proc) (a : act) :
    p -( a )> q -> p =( a )> q
  | POST_INTERNAL (p q r : proc) (a : act) :
    p -( a )> q /\ q =( a_tau )> r -> p =( a )> r
  | TAU (p : proc) :
    p =( a_tau )> p
 
  where "P =( a )> Q" := (weak_trans P a Q).


Example comuni:
  (Out 1 0 Nil) -(a_out 1 0)> Nil.
Proof. apply OUT. Qed.


Example comunication:
 Par (Out 1 0 Nil) (In 1 Nil) -(a_tau)> Par Nil Nil.
Proof. apply COM12 with (P := Out 1 0 Nil) (Q := In 1 Nil) (R := Nil) (S := Nil) (n := 1) (m := 0). 
  apply OUT. apply IN with (n := 1).
Qed.

Lemma fef:
  forall (P Q R S : proc) (n m : nat), P-(a_out n m)> R -> Q-(a_in n m)> S -> Par Q P -(a_tau)> Par S R.
Proof. intros. apply COM11 with (Q := P) (P := Q) (R := S) (S := R) (m := m) (n := n). apply H0. apply H.
Qed.

