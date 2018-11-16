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

Conjecture range_spec: forall m v,
    contains (range m) v <-> exists k, get m k = Some v.
(* TC_FAIL QuickChick range_spec. *)

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
