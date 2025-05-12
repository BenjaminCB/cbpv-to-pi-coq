Require Import Coq.Lists.List.
Import ListNotations.
Require Import Nat.
From Encoding Require Export cbpv.
From Encoding Require Export pi.

Fixpoint incRefs (n : nat) (m : nat) (refs : list (nat * nat)) :=
  match refs with
  | [] => []
  | (n', m') :: ps => (n + n', m + m') :: (incRefs n m ps)
  end.

Fixpoint findRef (n : nat) (refs : list (nat * nat)) :=
  match refs with
  | [] => 42 (* this case should never happen *)
  | (x, y) :: ps =>
      if n =? x 
      then y
      else findRef n ps
  end.
  
Definition pointer (p : proc) :=
  Rep (In (BN 0) (In (BN 0) (In (BN 1) p))).

Fixpoint encode (s : term) (u r : nat) (refs : list (nat * nat)) :=
  match s with
  | Abs s => Out (BN u) (In (BN 0) (In (BN 1) (In (BN 2) (encode s 2 1 ((0,0) :: incRefs 1 4 refs)))))
  | App s v => (Res ^^ 4) (Par 
      (In (BN 3) (In (BN 2) (Out (BN 1) (Out (BN 2) (Out (BN 3) (Par
        (Link (BN 2) (BN (9 + u)))
        (Par
          (Link (BN 1) (BN (9 + r)))
          (Link (BN 0) (BN 3))
        )
      ))))))
      (Par
        (encode s 3 2 (incRefs 0 4 refs))
        (Out (BN 1) (encode_value v (incRefs 0 4 refs)))
      )
    )
  | Force v => (Res ^^ 2) (Par
      (Out (BN 1) (encode_value v (incRefs 0 2 refs)))
      (In (BN 1) (Out (BN 0) (Out (BN 0) (Out (BN 1) (Par
        (Link (BN 1) (BN (6 + u)))
        (Link (BN 0) (BN (6 + r)))
      )))))
    )
  | Ret v => Out (BN r) (encode_value v refs)
  | Bind s t => (Res ^^ 2) (Par
      (encode s 1 0 (incRefs 0 2 refs))
      (In (BN 0) (encode t (3 + u) (3 + r) ((0,0) :: incRefs 1 3 refs)))
    )
  | Val v => Out (BN u) (encode_value v refs)
  end

with encode_value (v : value) (refs : list (nat * nat)) :=
  pointer(
    match v with
    | Var n => 
      match n with
      | (BV m) => Link (BN 0) (BN (findRef m refs + 4))
      | (FV m) => Link (BN 0) (FN m)
      end
    | Thunk s => encode s 1 0 (incRefs 0 4 refs)
    end
  ).
  
Notation "$ v ; refs $" := (encode_value v refs) (at level 90, left associativity).

Notation "$ s ; u ; r ; refs $" := (encode s u r refs) (at level 90, left associativity).

Definition encode' (s : term) := Res (Res ($ s ; 1 ; 0 ; [] $)).

Lemma wf_encoding:
  forall s, wf_term 0 s -> wf_proc 0 (encode' s).
Proof.
Admitted.