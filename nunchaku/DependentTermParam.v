Module MarkedAsTypeclass.

  Class Map(K V map: Type) := {
    empty: map;
    get: map -> K -> option V;
    put: map -> K -> V -> map;
  }.

  Inductive GoodMap{K M: Type}{MI: Map K nat M}: M -> Prop :=
  | GMEmpty: GoodMap empty
  | GMAddSmall: forall k n m,
      n < 10 ->
      GoodMap m ->
    GoodMap (put m k n)
  | GMDouble: forall k n m,
      get m k = Some n ->
      GoodMap m ->
      GoodMap (put m k n).

End MarkedAsTypeclass.

Module NotMarkedAsTypeclass.

  Inductive MapFunctions(K V map: Type): Type :=
  | Build_MapFunctions(empty: map)
                      (get: map -> K -> option V)
                      (put: map -> K -> V -> map).

  Definition empty{K V map}(mf: MapFunctions K V map): map :=
    match mf with
    | Build_MapFunctions _ _ _ res _ _ => res
    end.

  Definition get{K V map}(mf: MapFunctions K V map): map -> K -> option V :=
    match mf with
    | Build_MapFunctions _ _ _ _ res _ => res
    end.

  Definition put{K V map}(mf: MapFunctions K V map): map -> K -> V -> map :=
    match mf with
    | Build_MapFunctions _ _ _ _ _ res => res
    end.

  Inductive GoodMap{K M: Type}{mf: MapFunctions K nat M}: M -> Prop :=
  | GMEmpty: GoodMap (empty mf)
  | GMAddSmall: forall k n m,
      n < 10 ->
      GoodMap m ->
    GoodMap (put mf m k n)
  | GMDouble: forall k n m,
      get mf m k = Some n ->
      GoodMap m ->
      GoodMap (put mf m k n).

End NotMarkedAsTypeclass.
