(* range returning values of shadowed keys *)
Definition range(M: map K V): set V :=
  List.map snd M.
