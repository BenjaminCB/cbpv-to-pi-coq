Require Import Coq.Init.Nat.

Inductive proc : Type := 
 | Nil
 | Rep (P : proc)
 | Res (P : proc)
 | Par (P Q : proc)
 | In (n : nat) (P : proc)
 | Out (n m : nat) (P : proc).

Fixpoint c_swap (n : nat) (P : proc) : proc :=
  match P with
  | Nil => Nil
  | Rep Q => Rep (c_swap n Q)
  | Res Q => Res (c_swap (n+1) Q)
  | Par Q R => Par (c_swap n Q) (c_swap n R)
  | In a Q => In (if (a =? n) then (n+1) 
              else (if a =? (n+1) then n else a)) (c_swap (n+1) Q)
  | Out a b Q => Out (if a =? n then (n+1) else (if a =? (n+1) then n else a)) (if b =? n then (n+1) else (if b =? (n+1) then n else b)) (c_swap n Q)
  end.

Definition swap (P: proc) : proc := c_swap 0 P.

Example swap_thing:
  swap (Res (Out 1 0 (Nil))) = Res(Out 2 0 (Nil)). 
Proof. simpl. reflexivity. Qed.

Example swap_thing1:
  swap (Out 1 7 (Nil)) = Out 0 7 (Nil).
Proof. simpl. reflexivity. Qed.


Fixpoint c_push (n : nat) (P : proc) : proc := 
  match P with 
  | Nil => Nil
  | Par Q R => Par (c_push n Q) (c_push n R)
  | Res Q => Res (c_push (n+1) Q)
  | In m Q => In (if leb n m then (m+1) else m) (c_push (n+1) Q)
  | Out m l Q => Out (if leb n m then (m+1) else m) (if leb n l then (l+1) else l) (c_push n Q)
  | Rep Q => Rep (c_push n Q)
  end.

Definition pushN (n m : nat) : nat := (if (ltb m n) then m else m+1 ).
Definition push (P : proc) : proc := c_push 0 P.

(*Notation "'popN' n t c" :=
  (if (leb n c) then n - 1 else (if (eqb n c) then t else n))(at level 200).
*)

Definition popN (n t c : nat) : nat :=
  (if (ltb c n) then n - 1 else (if (eqb n c) then t else n)).

Fixpoint c_pop (n c: nat) (P : proc) : proc :=
 match P with
  | Nil => Nil
  | Par Q R => Par (c_pop n c Q) (c_pop n c R)
  | Rep Q => Rep (c_pop n c Q) 
  | Out m o Q => Out (popN m n c) (popN o n c) (c_pop n c Q)
  | In m Q => In (popN m n c) (c_pop (n+1) (c+1) Q)
  | Res Q => Res (c_pop (n+1) (c+1) Q)
  end.

Definition pop (n : nat) (P : proc) : proc := c_pop n 0 P.

Example pop_thing1:
  pop 4 (Res (Out 1 0 (Nil))) = Res(Out 5 0 (Nil)). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Example pop_thing2:
  pop 4 (In 0 (Res (Out 1 0 (Nil)))) = In 4 (Res(Out 1 0 (Nil))). 
Proof. simpl. unfold popN. simpl. reflexivity. Qed.


Inductive act : Set :=
  | a_tau : act
  | a_out: nat -> nat -> act
  | a_in: nat -> nat -> act
  | a_bout: nat -> act.

Reserved Notation "P -( a )> Q" (at level 70).

Inductive trans: proc -> act -> proc -> Prop := 
 
  | OUT   (n m : nat) (P : proc): trans (Out n m P) (a_out n m) P
 
  | IN    (n m : nat) (P: proc): trans (In n P) (a_in n m) (pop m P)
 
  | PAR1 (a : act) (n m : nat) (P Q R: proc): 
    a = a_in n m \/ a = a_tau \/ a = a_out n m ->
    trans P a R -> trans (Par P Q) a (Par R Q)
 
  | PAR2  (a : act) (n : nat) (P Q R : proc):
     trans P (a_bout n) R -> trans (Par P Q) (a_bout n) (Par R (push Q))
 
  | RES1  (n : nat) (P R : proc):
    trans P (a_out (n + 1) 0 ) R -> trans (Res P) (a_bout n) R
 
  | RES21 (a : nat -> nat -> act) (n m : nat) (P Q : proc) :
     a = a_out \/ a = a_in ->
     trans P (a (n + 1) (m + 1)) Q -> 
     trans (Res P) (a_out n m) (Res Q)
 
  | RES22 (P Q : proc) :
    trans P (a_tau) Q -> 
    trans (Res P) (a_tau) (Res Q)
 
  | RESBOUT (n : nat) (P Q : proc) :
    trans P (a_bout (n+1)) Q -> trans (Res P) (a_bout n) (Res (swap Q))


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
    trans Q (a_bout n) S 
 
  | COM22  (n : nat) (P Q R S : proc) :
    trans P (a_bout n) R ->
    trans Q (a_in n 0) S ->
    trans (Par P Q) a_tau (Res (Par R S))
 
  | REP   (a : act) (P Q: proc) : 
    trans (Par P (Rep P)) a Q -> trans (Rep P) a Q
 
  where "P -( a )> Q" := (trans P a Q).

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

Inductive exp : Type :=
  | lambda : exp -> exp
  | app : exp -> value -> exp
  | force : value -> exp
  | val: value -> exp
  | retur: value -> exp
  | bind: exp -> exp -> exp
with value: Set :=
  | var : nat ->  value
  | thunk : exp -> value.

Fixpoint incre_exp (m : exp) (c : nat) : exp :=
  match m with
  | lambda M => lambda (incre_exp M (c+1))
  | app M V => app (incre_exp M c) (incre_val V c)
  | force V => force (incre_val V c)
  | val V => val (incre_val V c)
  | retur V => retur (incre_val V c)
  | bind M N => bind (incre_exp M c) (incre_exp N (c+1))
  end
  with incre_val (v : value) (c:nat) : value :=
  match v with
  | var n => if leb n c then var n else var (n+1)
  | thunk M => thunk (incre_exp M c)
  end.


Fixpoint c_sub_e (v : value) (c : nat) (m : exp) {struct m} : exp :=
   match m with
  | lambda M => lambda (c_sub_e (incre_val v 0) (c+1) M) 
  | app M N => app (c_sub_e v (c) M) (c_sub_v v (c) N)
  | force V => force (c_sub_v v c V)
  | val V => val (c_sub_v v c V)
  | retur V => retur (c_sub_v v c V)
  | bind M N => bind (c_sub_e v c M) (c_sub_e (incre_val v 0) (c+1) N)
end

  with c_sub_v (v1 : value) (c : nat) (v2 : value) {struct v2} : value :=
  match v2 with
  | var n => if eqb n c then v1 else v2
  | thunk M => thunk (c_sub_e v1 c M)
  end.

Example substitution_simple:
  c_sub_e (var 2) (0) (val (var 0)) = val (var 2). 
Proof. simpl. reflexivity. Qed.


