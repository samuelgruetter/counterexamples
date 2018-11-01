(* less relevant because rather esoteric: *)

Require Coq.Vectors.Vector.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. Import ListNotations.

Fixpoint multiarrow(n: nat): Type :=
  match n with
  | O => Type
  | S m => Type -> (multiarrow m)
  end.

Fixpoint apply{n: nat}: multiarrow n -> (Vector.t Type n) -> Type :=
  match n as n0 return multiarrow n0 -> (Vector.t Type n0) -> Type with
  | O => fun m args => m
  | S n' => fun m args => apply (m (Vector.hd args)) (Vector.tl args)
  end.

Inductive Foo(n: nat)(x: multiarrow n): Type :=
  | mkFoo(types: Vector.t Type n)(arg: apply x types).

Example foo0: Foo 0 nat :=
  mkFoo 0 nat (Vector.nil Type) 12.

Example foo1: Foo 1 list :=
  mkFoo 1 list (Vector.cons Type nat 0 (Vector.nil Type))
        [1; 2; 3; 4].

Example foo2: Foo 2 prod :=
  mkFoo 2 prod (Vector.cons Type nat 1 (Vector.cons Type string 0 (Vector.nil Type)))
        (42, "hello").

Check (fun (T: Type) => (list T, T)).
Check prod.
