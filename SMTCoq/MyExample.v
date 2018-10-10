Require Import SMTCoq.SMTCoq.
Local Open Scope Z_scope.

Import FArray.
Local Open Scope farray_scope.

Instance oZord: OrdType (option Z) := {|
  lt o1 o2 := match o1, o2 with
                | Some z1, Some z2 => z1 < z2
                | None, Some z2 => True
                | Some z1, None => False
                | None, None => False
              end;
|}.
all: intros.
- destruct x; destruct y; destruct z; try omega. auto.
- destruct x; destruct y; intro; try omega.
  + inversion H0.
    omega.
  + discriminate.
Defined.

Instance oZcomp: Comparable (option Z) := {|
  compare o1 o2 := match o1, o2 with
                   | Some z1, Some z2 => _
                   | None, Some z2 => _
                   | Some z1, None => _
                   | None, None => _
                   end;
|}.
- destruct (z1 ?= z2) eqn: E.
  + apply OrderedType.EQ.
    apply Z.compare_eq in E.
    congruence.
  + apply OrderedType.LT.
    rewrite Z.compare_lt_iff in E.
    simpl.
    assumption.
  + apply OrderedType.GT.
    rewrite Z.compare_gt_iff in E.
    simpl.
    assumption.
- apply OrderedType.GT. simpl. auto.
- apply OrderedType.LT. simpl. auto.
- apply OrderedType.EQ. simpl. auto.
Defined.

Instance ioz: Inhabited (option Z) := {|
  default_value := None;
|}.

Goal forall (a b c d: farray Z Z),
    b[0 <- (4)] = c  ->
    d = b[0 <- (4)][1 <- (4)]  ->
    a = d[1 <- b[1]]  ->
    a <> c.
Proof.
  cvc4.
(*
In nested Ltac calls to "cvc4" and "cvc4_bool", last call failed.
Error:
CVC4 returned sat. Here is the model:

a := (const_farray 0)[0 <- 4][1 <- -1]
b := (const_farray 0)[1 <- -1]
c := (const_farray 0)[0 <- 4][1 <- -1]
d := (const_farray 0)[0 <- 4][1 <- 4]
*)
Abort.

Goal forall (a b c d: farray Z (option Z)),
    b[0 <- (Some 4)] = c  ->
    d = b[0 <- (Some 4)][1 <- (Some 4)]  ->
    a = d[1 <- b[1]]  ->
    a <> c.
Proof.
  cvc4.
  (*
In nested Ltac calls to "cvc4" and "cvc4_bool", last call failed.
Error: Could not reconstruct model
*)
Abort.
