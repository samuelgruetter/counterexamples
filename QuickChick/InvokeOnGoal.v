Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
From QuickChick Require Import QuickChick.

Definition TODO{T: Type}: T. Admitted.

(* (This one should be in the QuickChick library) *)
Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; intuition auto.
Defined.


Definition E := nat.
Definition eeq: forall (e1 e2: E), {e1 = e2} + {e1 <> e2} := Nat.eq_dec.

Definition set: Type -> Type := list.

Definition contains(A: set E)(e: E): Prop := List.In e A.

Definition union(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A B.

Lemma union_spec: forall (x: E) (A B: set E),
    contains (union A B) x <-> contains A x \/ contains B x.
Proof.
  intros.
  (* In a more complex proof, assume that getting here would have taken many
     lines of tactics script, which might have taken a few minutes of
     time to process, and now I'm here at a simple goal about sets.
     Before attempting to prove this goal, I'd like to quickchick it,
     by issuing just one vernac command, eg "QuickChick." without arguments.
     The closest I can get to that is the following hack:
*)

  repeat match goal with
         | x: _ |- _ => revert x
         end.
  abstract (apply TODO).
  QuickCheck union_spec_subproof.

(*
This answers

QuickChecking union_spec_subproof
+++ Passed 10000 tests (0 discards)

which makes me confident that I should work on proving this lemma.
*)
