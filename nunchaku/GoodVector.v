Require Coq.Vectors.Vector.

Module WithoutImplicitArgs.

    Inductive GoodVector(A: Type): forall (n: nat), Vector.t A n -> Prop :=
    | GVOne: forall (a: A),
        GoodVector A 1 (Vector.cons A a 0 (Vector.nil A))
    | GVCombine: forall (n: nat) (v1 v2: Vector.t A n),
        GoodVector A n v1 ->
        GoodVector A n v2 ->
        GoodVector A (n + n) (Vector.append v1 v2).

End WithoutImplicitArgs.

Module WithSomeImplicitArgs.

    Inductive GoodVector{A: Type}: forall {n: nat}, Vector.t A n -> Prop :=
    | GVOne: forall (a: A),
        GoodVector (Vector.cons A a 0 (Vector.nil A))
    | GVCombine: forall (n: nat) (v1 v2: Vector.t A n),
        GoodVector v1 ->
        GoodVector v2 ->
        GoodVector (Vector.append v1 v2).

End WithSomeImplicitArgs.
