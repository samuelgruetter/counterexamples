(* intersect_map containing shadowed keys version 1 *)
Definition intersect_map(M1 M2: map K V): map K V :=
  filter (fun '(k1, v1) => match get M2 k1 with
                           | Some v2 => if veq v1 v2 then true else false
                           | None => false
                           end) M1.
