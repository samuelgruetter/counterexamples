Fixpoint Tree(A: Type)(d: nat): Type :=
  match d with
  | O => A
  | S n => Tree A n * Tree A n
  end.

Definition ChildType(A: Type)(d: nat): Type :=
  match d with
  | O => unit
  | S n => Tree A n
  end.

Definition leftChild{A: Type}{d: nat}(t: Tree A d): ChildType A d :=
  match d as n return (Tree A n -> ChildType A n) with
  | O => fun _ => tt
  | S n => fun t => fst t
  end t.
