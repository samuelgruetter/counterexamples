Module FirstWay.

    Class Map(K V map: Type) := {
      empty: map;
      get: map -> K -> option V;
      put: map -> K -> V -> map;
    }.

    Check Build_Map. (*
    Build_Map
     : forall K V map : Type,
       map -> (map -> K -> option V) -> (map -> K -> V -> map) -> Map K V map
    *)

End FirstWay.

Module SecondWay.

    Class Map(K V: Type) := {
      map: Type;
      empty: map;
      get: map -> K -> option V;
      put: map -> K -> V -> map;
    }.

    Check Build_Map. (*
    Build_Map
     : forall K V map : Type,
       map -> (map -> K -> option V) -> (map -> K -> V -> map) -> Map K V
    *)

End SecondWay.
