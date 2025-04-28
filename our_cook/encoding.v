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
  | [] => n 
  | (x, y) :: ps => 
      if n =? x 
      then y
      else findRef n ps
  end.

Fixpoint encode (s : term) (u r : nat) (refs : list (nat * nat)) :=
  match s with
  | Abs s => Out u (In 0 (In 1 (In 2 (encode s 2 1 ((0,0) :: incRefs 1 4 refs)))))
  | App s v => (Res ^^ 4) (Par 
      (In 3 (In 2 (Out 1 (Out 2 (Out 3 (Par
        (Link 2 (u + 9))
        (Par
          (Link 1 (r + 9))
          (Link 0 3)
        )
      ))))))
      (Par
        (encode s 3 2 (incRefs 0 4 refs))
        (encode_value v 1 0 (incRefs 0 4 refs))
      )
    )
  | Force v => (Res ^^ 2) (Par
      (encode_value v 1 0 (incRefs 0 2 refs))
      (In 1 (Out 0 (Out 0 (Out 1 (Par
        (Link 1 (u + 6))
        (Link 0 (r + 6))
      )))))
    )
  | Ret v => encode_value v r r refs
  | Bind s t => (Res ^^ 2) (Par
      (encode s 1 0 (incRefs 0 2 refs))
      (In 0 (encode t (u + 3) (r + 3) (incRefs 1 3 refs)))
    )
  | Val v => encode_value v u r refs
  end

with encode_value (v : value) (u r : nat) (refs : list (nat * nat)) :=
  match v with
  | Var n => Out u (Rep (In 0 (In 0 (In 1 (In (n + 4) (In 0 (In 1 (Par
      (Link 1 4)
      (Link 0 3)
    ))))))))
  | Thunk s => Out u (Rep (In 0 (In 0 (In 1 (encode s 1 0 (incRefs 0 4 refs))))))
  end.