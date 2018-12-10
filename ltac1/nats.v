Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical_Prop.

(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

Lemma EE: forall AA (P: AA -> Prop), (exists a: AA, ~ P a) <-> ~ forall (a: AA), P a.
Proof.
  intros. split.
  - intros. destruct H as [a H]. intro. apply H. auto.
  - intro. destruct (classic (exists a : AA, ~ P a)) as [C | C]; [assumption|].
    exfalso. apply H. intro. destruct (classic (P a)) as [D | D]; [assumption |].
    exfalso. apply C. exists a. assumption.
Qed.

Ltac negate :=
  (* revert all *)
  repeat match goal with
         | x: _ |- _ => revert x
         end;
  (* negate goal *)
  match goal with
  | |- ?P => assert (~P); [|admit]
  end;
  (* "not forall" to "exists such that not" *)
  repeat match goal with
         | |- context[~ (forall (x: ?T), _)] =>
           (assert (forall (P: T -> Prop), (exists x: T, ~ P x) <-> ~ (forall x: T, P x)) as EEE
               by apply EE);
           setoid_rewrite <- EEE;
           clear EEE
         end.







































Ltac solver :=
  repeat match goal with
         | x: _ |- _ => subst x
         end;
  lia.

Ltac try_nats :=
  repeat multimatch goal with
  | |- exists (x: nat), _ => pose (x := 0); exists x
  | |- exists (x: nat), _ => pose (x := 1); exists x
  | |- exists (x: nat), _ => pose (x := 2); exists x
  end.

Ltac find_counterexample := negate; try_nats; test (solve [solver]).

Goal forall a b, min (a + 2) b < max (a + 2) b.
  intros.
  find_counterexample.

  solver.
