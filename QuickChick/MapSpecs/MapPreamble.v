Load "../SetSpecs/SetPreamble.v".
Load "../SetSpecs/empty_set_correct.v".
Load "../SetSpecs/singleton_set_correct.v".
Load "../SetSpecs/union_correct.v".
Load "../SetSpecs/intersect_correct.v".
Load "../SetSpecs/diff_correct.v".

(* this would normally be kept abstract as a section variable,
   but for testing, we make it concrete *)
Definition K: Type := nat.
Definition V: Type := nat.
Definition keq: forall (k1 k2: K), {k1 = k2} + {k1 <> k2} := Nat.eq_dec.
Definition veq: forall (v1 v2: V), {v1 = v2} + {v1 <> v2} := Nat.eq_dec.

Definition tupleeq: forall (t1 t2: K * V), {t1 = t2} + {t1 <> t2}.
  refine (fun '(k1, v1) '(k2, v2) =>
            match keq k1 k2, veq v1 v2 with
            | left _, left _ => left _
            | _, _ => right _
            end).
  all: congruence.
Defined.

Definition map(K V: Type): Type := list (K * V).

Definition empty_map: map K V := nil.

Definition get(M: map K V)(k: K): option V :=
  match find (fun '(ki, vi) => if keq ki k then true else false) M with
  | Some (_, v) => Some v
  | None => None
  end.

Definition remove(M: map K V)(k: K): map K V :=
  filter (fun '(ki, vi) => if keq k ki then false else true) M.

Definition put(M: map K V)(k: K)(v: V): map K V := (k, v) :: (remove M k).

Definition restrict(M: map K V)(A: set K): map K V :=
  filter (fun '(ki, vi) => if in_dec keq ki A then true else false) M.

Definition domain(M: map K V): set K := List.map fst M.

Definition domain_and_range(M: map K V): set K * set V :=
  fold_left (fun '(d, r) '(ki, vi) =>
               if in_dec keq ki d then (d, r) else (ki :: d, vi :: r)
            ) M (empty_set, empty_set).

Definition preimage(M: map K V)(vs: set V): set K :=
  filter (fun ki => match get M ki with
                    | Some vi => if in_dec veq vi vs then true else false
                    | None => false
                    end)
         (domain M).

Definition remove_keys(M: map K V)(ks: set K): map K V :=
  filter (fun '(ki, vi) => if in_dec keq ki ks then false else true) M.
