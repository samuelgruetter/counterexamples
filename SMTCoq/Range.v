Require Import SMTCoq.SMTCoq.
Local Open Scope Z_scope.

Import FArray.
Local Open Scope farray_scope.

Parameter fset: Type -> Type.
Parameter contains: forall {E: Type}, fset E -> E -> Prop.

Section DomAndRange.
  Context {K V: Type}.
  Context {orderedInst: OrdType K}.
  Context {kcomp: Comparable K}.
  Context {inhInstOptV: Inhabited (option V)}.

  Parameter domain: farray K (option V) -> fset K.
  Parameter range: farray K (option V) -> fset V.

  Lemma in_domain: forall a k v,
    a[k] = Some v -> contains (domain a) k.
  Proof.
    (* smt. *)
  Abort.

  Lemma in_range: forall a k v,
    a[k] = Some v -> contains (range a) v.
  Proof.
    (* smt. *)
  Abort.

End DomAndRange.
