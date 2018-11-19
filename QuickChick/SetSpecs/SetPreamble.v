Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

From QuickChick Require Import QuickChick.

(* should be in QuickChick library: *)
Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; intuition auto.
Defined.


(** List Sets *)

(* this would normally be kept abstract as a section variable,
   but for testing, we make it concrete *)
Definition E := nat.
Definition eeq: forall (e1 e2: E), {e1 = e2} + {e1 <> e2} := Nat.eq_dec.

Definition set: Type -> Type := list.

Definition contains(A: set E)(e: E): Prop := List.In e A.
