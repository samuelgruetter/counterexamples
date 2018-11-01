(* note: T is a parameter (the same for all results of the constructors),
   but still can vary in the recursive uses *)
Inductive Expr(T: Type): Type :=
| Cst(x: T): Expr T
| Fst(e: Expr (T * T)): Expr T
| Snd(e: Expr (T * T)): Expr T.

Arguments Cst {_} _.
Arguments Fst {_} _.
Arguments Snd {_} _.

Fixpoint interp{T: Type}(e: Expr T): T :=
  match e with
  | Cst x => x
  | Fst y => fst (interp y)
  | Snd y => snd (interp y)
  end.

Eval cbv in (interp (Fst (Snd (Cst ((1, 2), (3, 4)))))).
