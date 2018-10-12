Ltac destruct_ex_keepnames :=
  repeat match goal with
         | [ H: exists x, _ |- _ ] =>
           let x' := fresh x in destruct H as [x' H]
         end.

Goal forall (a: nat),
    (exists b, a = 2 * b) ->
    (exists b, a = 3 * b) ->
    (exists b, a = 6 * b).
Proof.
  intros a D2 D3.
  destruct_ex_keepnames.




Goal exists (p: nat * nat), fst p = snd p.
  lazymatch goal with
  | [ |- exists (x: nat), _ ] => exists 0
  | [ |- exists (x: nat * nat), _ ] => exists 0 (* <- intended failure *)
  end.
(*
Error:
Ltac call to "exists (ne_bindings_list)" failed.
The term "0" has type "nat" while it is expected to have type "(nat * nat)%type".
*)
