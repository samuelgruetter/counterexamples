From Hammer Require Import Hammer Reconstr.

Require Import Arith.

(* disable the preliminary crush-like tactic *)
Set Hammer CrushLimit 0.

Set Hammer Eprover.
Set Hammer Vampire.
Set Hammer Z3.

Lemma good1: forall n, n + n = 2 * n.
Proof.
  hammer.
(*
Extracting features...
Running provers (using 8 threads)...
Z3 succeeded
 - dependencies: Coq.Arith.PeanoNat.Nat.double_twice
 - definitions: Coq.Init.Nat.double
Trying tactic Reconstr.reasy...
Tactic Reconstr.reasy succeeded.
Replace the hammer tactic with:
        Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.double_twice) (@Coq.Init.Nat.double).
*)
  Restart.
  Reconstr.reasy (@Coq.Arith.PeanoNat.Nat.double_twice) (@Coq.Init.Nat.double).
Qed.

Lemma bad1: forall n, n + n + n = 2 * n.
Proof.
  hammer.
(*
Error: Hammer failed: ATPs failed to find a proof
 *)
Abort.
