(*
Trying to proof something for effects research:
language with effect handlers and escape analysis should be good.

What does it mean to be good?
- Progress
- Preservation

Is there any code that I can reuse?
*)

Inductive syntax : Set :=
  | var (idx : nat)
  | app (lhs : syntax) (args : list syntax)
  | lam (body : syntax).

Inductive type : Set :=
  | tvar (idx : nat)
  | tfun (args : list type) (res : type).

Definition ctx := partial_map

(* Inductive typing : ctx -> syntax -> type :=
  in_ctx :  *)
