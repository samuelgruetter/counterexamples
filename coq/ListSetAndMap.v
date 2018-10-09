Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

From QuickChick Require Import QuickChick.


Notation "'instantiate1' lemma func0" :=
  (ltac:(let r := eval unfold lemma in (lemma func0) in exact r))
  (at level 10, only parsing, lemma at next level, func0 at next level).


(** List Sets *)

(* this would normally be kept abstract as a section variable,
   but for testing, we make it concrete *)
Definition E := nat.
Definition eeq: forall (e1 e2: E), {e1 = e2} + {e1 <> e2} := Nat.eq_dec.

Definition set: Type -> Type := list.

Definition contains(A: set E)(e: E): Prop := List.In e A.

Definition empty_set: set E := nil.

Definition singleton_set(e: E): set E := (cons e nil).

Definition union_c0(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A B.

Definition union_w0(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A nil.

Definition intersect_c0(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a B then a :: res else res) A nil.

Definition intersect_w0(A B: list E): list E :=
  fold_left (fun res a => if in_dec eeq a B then res else a :: res) A nil.

Definition diff_c0(A B: list E): list E :=
  fold_left (fun res b => remove eeq b res) B A.

Definition diff_w0(A B: list E): list E :=
  fold_left (fun res b => remove eeq b res) A B.


(** Specs of set operations in terms of "contains" *)

Conjecture empty_set_spec_c0: forall (x: E), contains empty_set x <-> False.

Conjecture singleton_set_spec_c0: forall (x y: E),
    contains (singleton_set y) x <-> x = y.

Section union_spec.
  Variable union: set E -> set E -> set E.
  Definition generic_union_spec := forall (x: E) (A B: set E),
    contains (union A B) x <-> contains A x \/ contains B x.
End union_spec.
Conjecture union_spec_c0: instantiate1 generic_union_spec union_c0.
Conjecture union_spec_w0: instantiate1 generic_union_spec union_w0.

Section intersect_spec.
  Variable intersect: set E -> set E -> set E.
  Definition generic_intersect_spec := forall (x: E) (A B: set E),
    contains (intersect A B) x <-> contains A x /\ contains B x.
End intersect_spec.
Conjecture intersect_spec_c0: instantiate1 generic_intersect_spec intersect_c0.
Conjecture intersect_spec_w0: instantiate1 generic_intersect_spec intersect_w0.

Section diff_spec.
  Variable diff: set E -> set E -> set E.
  Definition generic_diff_spec := forall (x: E) (A B: set E),
    contains (diff A B) x <-> contains A x /\ ~ contains B x.
End diff_spec.
Conjecture diff_spec_c0: instantiate1 generic_diff_spec diff_c0.
Conjecture diff_spec_w0: instantiate1 generic_diff_spec diff_w0.


(* QuickChick setup: *)
Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; intuition auto.
Defined.


QuickChick union_spec_c0.
QuickChick union_spec_w0.
QuickChick intersect_spec_c0.
QuickChick intersect_spec_w0.
QuickChick diff_spec_c0.
QuickChick diff_spec_w0.


(** List Maps *)

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

Definition range(M: map K V): set V := List.map fst M.

Definition reverse_get(M: map K V)(v: V): option K :=
  match find (fun '(ki, vi) => if veq vi v then true else false) M with
  | Some (k, _) => Some k
  | None => None
  end.

Definition intersect_map(M1 M2: map K V): map K V :=
  fold_left (fun res a => if in_dec tupleeq a M2 then a :: res else res) M1 nil.

Definition remove_by_value(M: map K V)(v: V): map K V :=
  filter (fun '(ki, vi) => if veq vi v then false else true) M.

Definition remove_values(M: map K V)(vs: set V): map K V :=
  filter (fun '(ki, vi) => if in_dec veq vi vs then false else true) M.

Definition update_map(M1 M2: map K V): map K V :=
  (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then false (*true*) else true (*false*)) M2)
             then false else true) M1) ++ M2.

Conjecture empty_is_empty: forall (k: K),
    get empty_map k = None.
Conjecture get_remove_same: forall m k,
    get (remove m k) k = None.
Conjecture get_remove_diff: forall m k1 k2,
    k1 <> k2 -> get (remove m k1) k2 = get m k2.
Conjecture get_put_same: forall (m: map K V) (k: K) (v: V),
    get (put m k v) k = Some v.
Conjecture get_put_diff: forall (m: map K V) (k1 k2: K) (v: V),
    k1 <> k2 -> get (put m k1 v) k2 = get m k2.
Conjecture get_restrict_in: forall m k ks,
    contains ks k -> get (restrict m ks) k = get m k.
Conjecture get_restrict_notin: forall m k ks,
    ~ contains ks k -> get (restrict m ks) k = None.
Conjecture in_domain: forall m k v,
    get m k = Some v -> contains (domain m) k.
Conjecture not_in_domain: forall m k,
    get m k = None -> ~ contains (domain m) k.
Conjecture in_range: forall m k v,
    get m k = Some v -> contains (range m) v.
Conjecture not_in_range: forall m v,
    (forall k, get m k <> Some v) -> ~ contains (range m) v.
Conjecture reverse_get_Some: forall m k v,
    reverse_get m v = Some k -> get m k = Some v.
Conjecture reverse_get_None: forall m v,
    reverse_get m v = None -> forall k, get m k <> Some v.
Conjecture intersect_map_spec: forall k v m1 m2,
    get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v.
Conjecture remove_by_value_same: forall k v m,
    get m k = Some v -> get (remove_by_value m v) k = None.
Conjecture remove_by_value_diff: forall k v m,
    get m k <> Some v -> get (remove_by_value m v) k = get m k.
Conjecture remove_values_never_there: forall m k vs,
    get m k = None ->
    get (remove_values m vs) k = None.
Conjecture remove_values_removed: forall m k v vs,
    get m k = Some v ->
    contains vs v ->
    get (remove_values m vs) k = None.
Conjecture remove_values_not_removed: forall m k v vs,
    get m k = Some v ->
    ~ contains vs v ->
    get (remove_values m vs) k = Some v.
Conjecture get_update_map_l: forall m1 m2 k,
    get m2 k = None ->
    get (update_map m1 m2) k = get m1 k.
Conjecture get_update_map_r: forall m1 m2 k v,
    get m2 k = Some v ->
    get (update_map m1 m2) k = Some v.


QuickChick empty_is_empty.
QuickChick get_remove_same.
QuickChick get_remove_diff.
QuickChick get_put_same.
QuickChick get_put_diff.
QuickChick get_restrict_in.
QuickChick get_restrict_notin.
QuickChick in_domain.
QuickChick not_in_domain.
QuickChick in_range. (* reveals copy paste bug *)
(* QuickChick not_in_range. TODO *)
QuickChick reverse_get_Some. (* doesn't hold as such *)
(* QuickChick reverse_get_None. TODO *)
QuickChick intersect_map_spec. (* reveals bug related to duplicate keys *)
QuickChick remove_by_value_same. (* reveals bug related to duplicate keys *)
QuickChick remove_by_value_diff.
QuickChick remove_values_never_there.
QuickChick remove_values_removed.  (* reveals bug related to duplicate keys *)
QuickChick remove_values_not_removed.
(* reveals bug (switched true/false), TODO try with Z instead of nat*)
QuickChick get_update_map_l.
QuickChick get_update_map_r.
