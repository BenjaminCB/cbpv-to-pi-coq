Require Import Coq.Program.Basics.
Require Import Nat.
Require Import Bool.

Notation "f >>> g" := (compose g f) (at level 40, left associativity).
Notation "g <<< f" := (compose g f) (at level 40, left associativity).

Inductive proc : Type :=
| In (n : nat) (p : proc)
| Out (n m : nat) (p : proc)
| Res (p : proc)
| Rep (p : proc)
| Par (p q : proc)
| Nil.

Fixpoint isReffed (n : nat) (p : proc) : bool :=
  match p with
  | In m q =>
      if n =? m
      then true
      else isReffed (n + 1) q
  | Out m m' q =>
      if (n =? m) || (n =? m')
      then true
      else isReffed n q
  | Res q => isReffed (n + 1) q
  | Rep q => isReffed n q
  | Par q q' => (isReffed n q) || (isReffed n q')
  | Nil => false
  end.


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

Reserved Notation "P -(a_tau)> Q" (at level 70).
Reserved Notation "P -(a_in)> n m Q" (at level 70, n at next level, m at next level, Q at next level).
Reserved Notation "P -(a_out)> n m Q" (at level 78, n at next level, m at next level, Q at next level).
Reserved Notation "P -(a_bout)> n Q" (at level 70).
Reserved Notation "P -(a_inb)> n m Q" (at level 70).
 
Inductive trans_in: proc -> nat -> nat -> proc -> Prop :=  
  | IN    (n m : nat) (P: proc): 
    trans_in (In n P) n m (P[[m |> id]])
  | IPAR1 (n m : nat) (P Q R: proc):
    trans_in P n m R -> trans_in (Par P Q) n m (Par R Q)
  | IPAR12 (n m : nat) (P Q R: proc):
    trans_in Q n m R -> trans_in (Par P Q) n m (Par P R)
  | IRES21 (n m : nat) (P Q : proc) :
    trans_in P (n + 1) (m + 1) Q -> 
    trans_in (Res P) n m (Res Q)
  | IREP   (P Q: proc) (n m : nat) : 
    trans_in (Par P (Rep P)) n m Q -> trans_in (Rep P) n m Q

  where "P -(a_in)> n m Q" := (trans_in P n m Q).

Inductive trans_inb: proc -> nat -> nat -> proc -> Prop :=  
  | INB    (n m : nat) (P: proc): 
    trans_inb (In n P) n m (P[[m |> shift]])
  | IBPAR1 (n m : nat) (P Q R: proc):
    trans_inb P n m R -> trans_inb (Par P Q) n m (Par R (Q[[shift]]))
  | IBPAR12 (n m : nat) (P Q R: proc):
    trans_inb Q n m R -> trans_inb (Par P Q) n m (Par (P[[shift]]) R)
  | IBRES21 (n m : nat) (P Q : proc) :
    trans_inb P (n + 1) (m + 1) Q -> 
    trans_inb (Res P) n m (Res Q)
  | IBREP   (P Q: proc) (n m : nat) : 
    trans_inb (Par P (Rep P)) n m Q -> trans_inb (Rep P) n m Q

  where "P -(a_inb)> n m Q" := (trans_inb P n m Q).

Inductive trans_out: proc -> nat -> nat -> proc -> Prop :=  
  | OUT   (n m : nat) (P : proc): 
    trans_out (Out n m P) n m P  
  | OPAR1 (n m : nat) (P Q R: proc):
    trans_out P n m R -> trans_out (Par P Q) n m (Par R Q)
  | OPAR12 (n m : nat) (P Q R: proc):
    trans_out Q n m R -> trans_out (Par P Q) n m (Par P R)
  | ORES21 (n m : nat) (P Q : proc) :
    trans_out P (n + 1) (m + 1) Q -> 
    trans_out (Res P)  n m (Res Q)
  | OREP (n m : nat)(P Q: proc) : 
    trans_out (Par P (Rep P)) n m Q -> trans_out (Rep P) n m Q
  where "P -(a_out)> n m Q" := (trans_out P n m Q).

Inductive trans_bout: proc -> nat -> proc -> Prop :=  
  | BOPAR2  (n : nat) (P Q R : proc):
    trans_bout P n R -> trans_bout (Par P Q) n (Par R (Q[[shift]]))
  | BORES1  (n : nat) (P R : proc):
    trans_out P (n + 1) 0 R -> trans_bout (Res P) n R
  | BORESBOUT (n : nat) (P Q : proc) :
    trans_bout P (n+1) Q -> trans_bout (Res P) n (Res (Q[[swap]]))
  | BOREP   (n : nat) (P Q: proc) : 
    trans_bout (Par P (Rep P)) n Q -> trans_bout (Rep P) n Q
  where "P -(a_bout)> n Q" := (trans_bout P n Q).


Inductive trans: proc -> proc -> Prop := 
  | TPAR1 (P Q R: proc):
    trans P R -> trans (Par P Q) (Par R Q)
  | TPAR2  (P Q R: proc):
    trans Q R -> trans (Par P Q) (Par P R)
  | RES22 (P Q : proc) :
    trans P Q -> 
    trans (Res P) (Res Q)
  | COM11  (n m : nat) (P Q R S : proc) :
    trans_in P n m R ->
    trans_out Q n m S ->
    trans (Par P Q) (Par R S)
  | COM12  (n m : nat) (P Q R S : proc) :
    trans_out P n m R ->
    trans_in Q n m S ->
    trans (Par P Q) (Par R S)
  | COM21  (n : nat) (P Q R S : proc) :
    trans_inb P n 0 R ->
    trans_bout Q n S ->
    trans (Par P Q) (Res (Par R S))
  | COM22  (n : nat) (P Q R S : proc) :
    trans_bout P n R ->
    trans_inb Q n 0 S ->
    trans (Par P Q) (Res (Par R S))
  | REP (P Q: proc) : 
    trans (Par P (Rep P)) Q -> trans (Rep P) Q
 
  where "P -(a_tau)> Q" := (trans P Q).

Reserved Notation "P =()> Q" (at level 70).

Inductive weak_tau: proc -> proc -> Prop := 
  | TPRE_INTERNAL (p q r : proc) :
    p -(a_tau)> q /\ q =()> r -> p =()> r
  | ACTION (p q : proc) :
    p -(a_tau)> q -> p =()> q
  | TAU (p : proc) :
    p =()> p
 where "P =()> Q" := (weak_tau P Q).

Inductive weak_trans: proc -> action -> proc -> Prop := 
  | WT_PRE (p q r : proc) (l : action):
    p -(a_tau)> q /\ q =(l)> r -> p =(l)> r
  | WT_ACTION (p q : proc) (l : action):
    p -(l)> q -> p =(a_tau)> q
  | WT_TAU (p : proc):
    p =(l)> p
 where "P =()> Q" := (weak_tau P Q).

Reserved Notation "P =(a_out n m )> Q" (at level 71).

Inductive weak_out: proc -> nat -> nat -> proc -> Prop := 
  
  | OPRE_INTERNAL (p q r : proc) (n m : nat):

    p -(a_tau)> q /\ 
    weak_out q n m r -> 
    weak_out p n m r

  | OPOST_INTERNAL (p q r : proc) (n m : nat):
    weak_out p n m q /\ 
    q -(a_tau)> r ->     
    weak_out p n m r
 
   | OACTION (p q : proc) (n m : nat):
    trans_out p n m q -> 
    weak_out p n m q 

 where "P =(a_out n m )> Q" := (weak_out P n m Q).

Inductive weak_in: proc -> nat -> nat -> proc -> Prop := 
  
  | IPRE_INTERNAL (p q r : proc) (n m : nat):

    p -(a_tau)> q /\ 
    weak_in q n m r -> 
    weak_in p n m r

  | IPOST_INTERNAL (p q r : proc) (n m : nat):
    weak_in p n m q /\ 
    q -(a_tau)> r ->     
    weak_in p n m r
 
   | IACTION (p q : proc) (n m : nat):
    trans_in p n m q -> 
    weak_in p n m q.

Inductive weak_bout: proc -> nat -> proc -> Prop := 
  
  | BOPRE_INTERNAL (p q r : proc) (n : nat):

    p -(a_tau)> q /\ 
    weak_bout q n r -> 
    weak_bout p n r

  | BOPOST_INTERNAL (p q r : proc) (n : nat):
    weak_bout p n q /\ 
    q -(a_tau)> r ->     
    weak_bout p n r
 
   | BACTION (p q : proc) (n : nat):
    trans_bout p n q -> 
    weak_bout p n q.

Fixpoint not_in (p : proc) (n : nat) : Prop :=
  match p with
  | Res p' => not_in p' (n+1)
  | Par q r => (not_in q n) /\ (not_in r n)
  | Rep p' => (not_in p' n)
  | In m p' => ~(m = n) /\ (not_in p' (n+1))  
  | Out m l p' => ~(m = n) /\ ~(l = n) /\ (not_in p' (n+1))
  | Nil => True
end.

Example comuni:
  trans_out (Out 1 0 Nil) 1 0 Nil.
Proof. apply OUT. Qed.


Example comunication:
 Par (Out 1 0 Nil) (In 1 Nil) -(a_tau)> Par Nil Nil.
Proof. apply COM12 with (P := Out 1 0 Nil) (Q := In 1 Nil) (R := Nil) (S := Nil) (n := 1) (m := 0). 
  apply OUT. apply IN with (n := 1).
Qed.



