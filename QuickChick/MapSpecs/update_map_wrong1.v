(* then/else switched *)
Definition update_map(M1 M2: map K V): map K V :=
  (filter (fun '(k1, v1) =>
             if (find (fun '(k2, v2) => if keq k1 k2 then false else true) M2)
             then false else true) M1) ++ M2.
