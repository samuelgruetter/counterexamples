Require Import Coq.Lists.List. Import ListNotations.

Inductive stmt{varname funcname: Type}: Type :=
| SAdd(res arg1 arg2: varname)
| SSet(x: varname)(v: nat)
| SCall(f: funcname)(res: varname)(args: list varname).

Definition collect_varnames{V F}(s: stmt (varname:=V) (funcname:=F)): list V :=
  match s with
  | SAdd res arg1 arg2 => [res; arg1; arg2]
  | SSet x v => [x]
  | SCall f res args => res :: args
  end.

Inductive empty_funcname: Type := .

Definition simple_stmt := stmt (varname:=nat) (funcname:=empty_funcname).

Lemma number_of_vars_bound: forall (s: simple_stmt),
    length (collect_varnames s) <= 2.
Proof.
  (* call counterexample generator here *)

(* for <= 3: *)
  intros.
  destruct s; simpl; repeat constructor. destruct f.
Qed.
