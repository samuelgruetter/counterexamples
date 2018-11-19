(* remove_by_value reactivates a shadowed key *)
Definition remove_by_value(M: map K V)(v: V): map K V :=
  filter (fun '(ki, vi) => if veq vi v then false else true) M.
