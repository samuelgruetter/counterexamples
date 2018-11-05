Require Coq.Vectors.Vector.

Inductive SimilarLength: Type -> Type -> Prop :=
| Same: forall A n,
    SimilarLength (Vector.t A n) (Vector.t A (S n))
| LeftOneMore: forall A n,
    SimilarLength (Vector.t A (S n)) (Vector.t A n)
| RightOneMore: forall A n,
    SimilarLength (Vector.t A n) (Vector.t A (S n)).

Inductive Arity: Type -> nat -> Prop :=
| AOne: forall A, Arity A 1
| APair: forall A1 A2 n1 n2,
    Arity A1 n1 ->
    Arity A2 n2 ->
    Arity (A1 * A2)%type (n1 + n2)
| AVec: forall A n m,
    Arity A n ->
    Arity (Vector.t A m) (n * m)%nat.
