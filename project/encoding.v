From Encoding Require Export cbpv.
From Encoding Require Export pi.
Require Coq.Lists.List.

Fixpoint encode (s : term) (u r : nat) (refs : List.list (nat * nat)) :=
  match s with
  | Val v => encode_value v u refs
  | Abs s => In u (In 0 (In 1 (In 2 (encode s 2 1 refs))))
  | App s v => Res (Res (Par (encode s 1 0 refs) (Res (Out 2 0 (Out 0 (u + 3) (Out 0 (r + 3) (encode_value v 0 refs)))))))
  | Force v => Res (Par (encode_value v 0 refs) (In 0 (Res (Out 1 0 (Out 0 u (Out 0 r (Nil)))))))
  | Ret v => encode_value v r refs
  | Bind s t => Res (Par (Res (encode s 0 1 refs)) (In 0 (encode t u r refs)))
  end

with encode_value (v : value) (u : nat) (refs : List.list (nat * nat)) :=
  match v with
  | Var n => Res (Out u 0 (Rep (In 0 (Out n 0 Nil))))
  | Thunk s => Res (Out u 0 (Rep (In 0 (In 0 (In 1 (encode s 1 0 refs))))))
  end.