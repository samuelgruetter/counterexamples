Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.

From QuickChick Require Import QuickChick.

(* should be in QuickChick library: *)
Global Instance Dec_iff {P Q} {H : Dec P} {I : Dec Q} : Dec (P <-> Q).
Proof.
  constructor. unfold ssrbool.decidable.
  destruct H as [D]; destruct D;
    destruct I as [D]; destruct D; intuition auto.
Defined.


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

Definition union(A B: list E): list E :=
  (*! *)
  fold_left (fun res a => if in_dec eeq a res then res else a :: res) A B
  (*!! initial accumulator in union nil instead of B *)
  (*! fold_left (fun res a => if in_dec eeq a res then res else a :: res) A nil *)
  (*!! then/else branch swapped in union *)
  (*! fold_left (fun res a => if in_dec eeq a res then a :: res else res) A B *)
.

Definition intersect(A B: list E): list E :=
  (*! *)
  fold_left (fun res a => if in_dec eeq a B then a :: res else res) A nil
  (*!! then/else branch swapped in intersect *)
  (*! fold_left (fun res a => if in_dec eeq a B then res else a :: res) A nil *)
.

Definition diff(A B: list E): list E :=
  (*! *)
  fold_left (fun res b => remove eeq b res) B A
  (*!! traversee and accumulator swapped in diff *)
  (*! fold_left (fun res b => remove eeq b res) A B *)
.


(** Specs of set operations in terms of "contains" *)

Conjecture empty_set_spec: forall (x: E), contains empty_set x <-> False.
(* TC_FAIL QuickChick empty_set_spec. *)

Conjecture singleton_set_spec: forall (x y: E),
    contains (singleton_set y) x <-> x = y.
(*! QuickChick singleton_set_spec. *)

Conjecture union_spec: forall (x: E) (A B: set E),
    contains (union A B) x <-> contains A x \/ contains B x.
(*! QuickChick union_spec. *)

Conjecture intersect_spec: forall (x: E) (A B: set E),
    contains (intersect A B) x <-> contains A x /\ contains B x.
(*! QuickChick intersect_spec. *)

Conjecture diff_spec: forall (x: E) (A B: set E),
    contains (diff A B) x <-> contains A x /\ ~ contains B x.
(*! QuickChick diff_spec. *)




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

Definition domain_and_range(M: map K V): set K * set V :=
  fold_left (fun '(d, r) '(ki, vi) =>
               if in_dec keq ki d then (d, r) else (ki :: d, vi :: r)
            ) M (empty_set, empty_set).

Definition range(M: map K V): set V :=
  (*! *)
  snd (domain_and_range M)
  (*!! range returning values of shadowed keys *)
  (*! List.map snd M *)
  (*!! range copy pasted body of domain *)
  (*! List.map fst M *)
.

Definition reverse_get(M: map K V)(v: V): option K :=
  (*! *)
  snd (fold_left (fun '(seen_keys, res) '(ki, vi) =>
                    if in_dec keq ki seen_keys then (seen_keys, res)
                    else (ki :: seen_keys, if veq vi v then Some ki else res))
                 M (empty_set, None))
  (*!! reverse_get returning values of shadowed keys *)
  (*! match find (fun '(ki, vi) => if veq vi v then true else false) M with
     | Some (k, _) => Some k
     | None => None
     end *)
.

Definition intersect_map(M1 M2: map K V): map K V :=
  (*! *)
  filter (fun '(k1, v1) => match get M1 k1, get M2 k1 with
                           | Some v1', Some v2 => if veq v1' v1
                                                  then if veq v1 v2 then true else false
                                                  else false
                           | _, _ => false
                           end) M1
  (*!! intersect_map containing shadowed keys v2 *)
  (*! filter (fun '(k1, v1) => match get M2 k1 with
                           | Some v2 => if veq v1 v2 then true else false
                           | None => false
                           end) M1 *)
  (*!! intersect_map containing shadowed keys v1 *)
  (*! fold_left (fun res a => if in_dec tupleeq a M2 then a :: res else res)
      M1 nil *)
.

Definition preimage(M: map K V)(vs: set V): set K :=
  filter (fun ki => match get M ki with
                    | Some vi => if in_dec veq vi vs then true else false
                    | None => false
                    end)
         (domain M).

Definition remove_keys(M: map K V)(ks: set K): map K V :=
  filter (fun '(ki, vi) => if in_dec keq ki ks then false else true) M.

Definition remove_by_value(M: map K V)(v: V): map K V :=
  (*! *)
  remove_keys M (preimage M (singleton_set v))
  (*!! remove_by_value reactivates a shadowed key *)
  (*! filter (fun '(ki, vi) => if veq vi v then false else true) M *)
.

Definition remove_values(M: map K V)(vs: set V): map K V :=
  (*! *)
  remove_keys M (preimage M vs)
  (*!! remove_values might reactivate a shadowed key *)
  (*! filter (fun '(ki, vi) => if in_dec veq vi vs then false else true) M *)
.

Definition update_map(M1 M2: map K V): map K V :=
  (*! *)
  (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then true else false) M2)
             then false else true) M1) ++ M2
  (*!! update_map with then/else switched *)
  (*! (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then false else true) M2)
             then false else true) M1) ++ M2 *)
.

Conjecture empty_is_empty: forall (k: K),
    get empty_map k = None.
(*! QuickChick empty_is_empty. *)

Conjecture get_remove_same: forall m k,
    get (remove m k) k = None.
(*! QuickChick get_remove_same. *)

Conjecture get_remove_diff: forall m k1 k2,
    k1 <> k2 -> get (remove m k1) k2 = get m k2.
(*! QuickChick get_remove_diff. *)

Conjecture get_put_same: forall (m: map K V) (k: K) (v: V),
    get (put m k v) k = Some v.
(*! QuickChick get_put_same. *)

Conjecture get_put_diff: forall (m: map K V) (k1 k2: K) (v: V),
    k1 <> k2 -> get (put m k1 v) k2 = get m k2.
(*! QuickChick get_put_diff. *)

Conjecture get_restrict_in: forall m k ks,
    contains ks k -> get (restrict m ks) k = get m k.
(*! QuickChick get_restrict_in. *)

Conjecture get_restrict_notin: forall m k ks,
    ~ contains ks k -> get (restrict m ks) k = None.
(*! QuickChick get_restrict_notin. *)

Conjecture in_domain: forall m k v,
    get m k = Some v -> contains (domain m) k.
(*! QuickChick in_domain. *)

Conjecture not_in_domain: forall m k,
    get m k = None -> ~ contains (domain m) k.
(*! QuickChick not_in_domain. *)

Conjecture in_range: forall m k v,
    get m k = Some v -> contains (range m) v.
(*! QuickChick in_range. *)

Conjecture not_in_range: forall m v,
    (forall k, get m k <> Some v) -> ~ contains (range m) v.
(* TC_FAIL QuickChick not_in_range. *)

Conjecture reverse_get_Some: forall m k v,
    reverse_get m v = Some k -> get m k = Some v.
(*! QuickChick reverse_get_Some. *)

Conjecture reverse_get_None: forall m v,
    reverse_get m v = None -> forall k, get m k <> Some v.
(* TC_FAIL QuickChick reverse_get_None. *)

Conjecture intersect_map_spec: forall k v m1 m2,
    get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v.
(*! QuickChick intersect_map_spec. *)

Conjecture remove_by_value_same: forall k v m,
    get m k = Some v -> get (remove_by_value m v) k = None.
(*! QuickChick remove_by_value_same. *)

Conjecture remove_by_value_diff: forall k v m,
    get m k <> Some v -> get (remove_by_value m v) k = get m k.
(*! QuickChick remove_by_value_diff. *)

Conjecture remove_values_never_there: forall m k vs,
    get m k = None ->
    get (remove_values m vs) k = None.
(*! QuickChick remove_values_never_there. *)

Conjecture remove_values_removed: forall m k v vs,
    get m k = Some v ->
    contains vs v ->
    get (remove_values m vs) k = None.
(*! QuickChick remove_values_removed. *)

Conjecture remove_values_not_removed: forall m k v vs,
    get m k = Some v ->
    ~ contains vs v ->
    get (remove_values m vs) k = Some v.
(*! QuickChick remove_values_not_removed. *)

Conjecture get_update_map_l: forall m1 m2 k,
    get m2 k = None ->
    get (update_map m1 m2) k = get m1 k.
(*! QuickChick get_update_map_l. *)

Conjecture get_update_map_r: forall m1 m2 k v,
    get m2 k = Some v ->
    get (update_map m1 m2) k = Some v.
(*! QuickChick get_update_map_r. *)
