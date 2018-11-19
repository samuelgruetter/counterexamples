(* returning values of shadowed keys *)
Definition reverse_get(M: map K V)(v: V): option K :=
  match find (fun '(ki, vi) => if veq vi v then true else false) M with
     | Some (k, _) => Some k
     | None => None
     end.
