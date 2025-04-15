From Encoding Require Export cbpv.
From Encoding Require Export pi.
Require Coq.Lists.List.
Require Import Nat.

Definition incProduct (n : nat) (m : nat) (pair : nat * nat) := 
  match pair with
  | (n', m') => (n + n', m + m')
  end.

Fixpoint incRefs (n : nat) (m : nat) (refs : List.list (nat * nat)) :=
  match refs with
  | List.nil => List.nil
  | List.cons p ps => List.cons 
      (incProduct n m p)
      (incRefs n m ps)
  end.

Fixpoint findRef (n : nat) (refs : List.list (nat * nat)) :=
  match refs with
  | List.nil => n 
  | List.cons (x, y) ps => 
      if n =? x 
      then y
      else findRef n ps
  end.

Fixpoint encode (s : term) (u r : nat) (refs : List.list (nat * nat)) :=
  match s with
  | Val v => Res (Out (u+1) 0 (encode_value v (incRefs 0 1 refs)))
  | Abs s => In u (In 0 (In 1 (In 2 (encode s 2 1 (List.cons (0,0) (incRefs 1 4 (refs)))))))
  | App s v => Res (Res (Par 
      (encode s 1 0 (incRefs 0 2 refs)) 
      (Res (Out 2 0 (Out 0 (u + 3) (Out 0 (r + 3) 
        ( ( Res (Out (u+4) 0 (encode_value v (incRefs 0 4 refs) ))))
      ))))
    ))
  | Force v => Res (Par 
      (Res ( Out (1) 0(encode_value v (incRefs 0 1 refs)) ))
      (In 0 (Res (Out 1 0 (Out 0 (u + 3) (Out 0 (r + 3) (Nil))))))
    )
  | Ret v => (Res (Out (r+1) 0 (encode_value v (incRefs 0 1 refs))))
  | Bind s t => Res (Par 
      (Res (encode s 0 1 (incRefs 0 2 refs))) 
      (In 0 (encode t (u + 2) (r + 2) (List.cons (0,0)(incRefs 1 2 refs))))
    )
  end

with encode_value (v : value) (refs : List.list (nat * nat)) :=
  match v with
  | Var n => Rep (In 0 (Out ((findRef n refs) + 1) 0 Nil))
  | Thunk s => (Rep (In 0 (In 0 (In 1 
      (encode s 1 0 (incRefs 0 3 refs))
    ))))
  end.
