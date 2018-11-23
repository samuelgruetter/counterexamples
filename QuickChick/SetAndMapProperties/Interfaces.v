(* for presentation purposes, copied from https://github.com/tchajed/map-automation/blob/master/slow_maps_v0.v, which is in turn copied from bedrock2 *)

Class SetFunctions(E: Type) := mkSet {
  set: Type;
  contains: set -> E -> Prop;
  empty_set: set;
  singleton_set: E -> set;
  union: set -> set -> set;
  intersect: set -> set -> set;
  diff: set -> set -> set;
}.

Arguments set E {_}.

Notation "x '\in' s" := (contains s x) (at level 70, no associativity).

Section SetDefinitions.
  Context {E: Type}.
  Context {setInst: SetFunctions E}.
  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
End SetDefinitions.


Class MapFunctions(K V: Type) := mkMap {
  map: Type;
  map_domain_set: SetFunctions K;
  map_range_set: SetFunctions V;
  get: map -> K -> option V;
  empty_map: map;
  put: map -> K -> V -> map;
  restrict: map -> set K -> map;
  domain: map -> set K;
  range: map -> set V;
  reverse_get: map -> V -> option K;
  intersect_map: map -> map -> map; (* treats maps as sets of tuples *)
  remove_key: map -> K -> map;
  remove_keys: map -> set K -> map;
  remove_by_value: map -> V -> map;
  remove_values: map -> set V -> map;
  update_map: map -> map -> map;  (* rhs overrides lhs *)
}.

Arguments map _ _ {_}.
Existing Instance map_domain_set.
Existing Instance map_range_set.

Definition extends{K V: Type}{KVmap: MapFunctions K V}(s1 s2: map K V) :=
    forall x w, get s2 x = Some w -> get s1 x = Some w.

Module MoreReal.

Section MapDefinitionsAll.
  Context {K V: Type}.
  Context {KVmap: MapFunctions K V}.
  Definition extends(s1 s2: map K V) := forall x w, get s2 x = Some w -> get s1 x = Some w.
  Definition only_differ(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs \/ get s1 x = get s2 x.
  Definition agree_on(s1: map K V)(vs: set K)(s2: map K V) :=
    forall x, x \in vs -> get s1 x = get s2 x.
  Definition undef_on(s: map K V)(vs: set K) := forall x, x \in vs -> get s x = None.
End MapDefinitionsAll.

End MoreReal.


Section SampleQueries.
Context {K V: Type}.
Context {KVmap: MapFunctions K V}.

(* query3 *)
Goal
forall (g1 g2 r : map K V) (p1 p2 : set V),
subset (range g1) p1 ->
subset (range g2) p2 ->
subset (range (intersect_map g1 g2))
       (union p1 p2) ->
extends (update_map (remove_values r p1) g1)
        (update_map (remove_values r (union p1 p2))
                    (intersect_map g1 g2)).
Abort.

(* remove_values_not_removed *)
Goal
forall (m : map K V) (k : K) (v : V) (vs : set V),
get m k = Some v ->
~ v \in vs ->
get (remove_values m vs) k = Some v.
Abort.

End SampleQueries.
