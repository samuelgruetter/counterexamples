Conjecture empty_spec: forall (k: K),
    get empty_map k = None.

Conjecture remove_spec1: forall m k,
    get (remove m k) k = None.

Conjecture remove_spec2: forall m k1 k2,
    k1 <> k2 -> get (remove m k1) k2 = get m k2.

Conjecture put_spec1: forall (m: map K V) (k: K) (v: V),
    get (put m k v) k = Some v.

Conjecture put_spec2: forall (m: map K V) (k1 k2: K) (v: V),
    k1 <> k2 -> get (put m k1 v) k2 = get m k2.

Conjecture restrict_spec1: forall m k ks,
    contains ks k -> get (restrict m ks) k = get m k.

Conjecture restrict_spec2: forall m k ks,
    ~ contains ks k -> get (restrict m ks) k = None.

Conjecture domain_spec1: forall m k v,
    get m k = Some v -> contains (domain m) k.

Conjecture domain_spec2: forall m k,
    get m k = None -> ~ contains (domain m) k.

Conjecture range_spec1: forall m k v,
    get m k = Some v -> contains (range m) v.

Conjecture range_spec2: forall m v,
    (forall k, get m k <> Some v) -> ~ contains (range m) v.

Conjecture range_spec3: forall m v,
    contains (range m) v <-> exists k, get m k = Some v.

Conjecture reverse_spec1: forall m k v,
    reverse_get m v = Some k -> get m k = Some v.

Conjecture reverse_spec2: forall m v,
    reverse_get m v = None -> forall k, get m k <> Some v.

Conjecture intersect_map_spec: forall k v m1 m2,
    get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v.

Conjecture remove_by_value_spec1: forall k v m,
    get m k = Some v -> get (remove_by_value m v) k = None.

Conjecture remove_by_value_spec2: forall k v m,
    get m k <> Some v -> get (remove_by_value m v) k = get m k.

Conjecture remove_values_spec1: forall m k vs,
    get m k = None ->
    get (remove_values m vs) k = None.

Conjecture remove_values_spec2: forall m k v vs,
    get m k = Some v ->
    contains vs v ->
    get (remove_values m vs) k = None.

Conjecture remove_values_spec3: forall m k v vs,
    get m k = Some v ->
    ~ contains vs v ->
    get (remove_values m vs) k = Some v.

Conjecture update_map_spec1: forall m1 m2 k,
    get m2 k = None ->
    get (update_map m1 m2) k = get m1 k.

Conjecture update_map_spec2: forall m1 m2 k v,
    get m2 k = Some v ->
    get (update_map m1 m2) k = Some v.
