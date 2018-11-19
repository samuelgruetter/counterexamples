Load "../SetSpecs/SetPreamble.v".
Load "../SetSpecs/empty_set_correct.v".
Load "../SetSpecs/singleton_set_correct.v".
Load "../SetSpecs/union_correct.v".
Load "../SetSpecs/intersect_correct.v".
Load "../SetSpecs/diff_correct.v".

(** Additional functions for sets defined in terms of the primitive ones *)

Definition add(s: set E)(e: E) := union (singleton_set e) s.
Definition remove_elem(s: set E)(e: E) := diff s (singleton_set e).
Definition subset(s1 s2: set E) := forall x, contains s1 x -> contains s2 x.
Definition disjoint(s1 s2: set E) := forall x, (~ contains s1 x) \/ (~ contains s2 x).
