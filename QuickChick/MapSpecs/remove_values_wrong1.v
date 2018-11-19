(* remove_values might reactivate a shadowed key *)
Definition remove_values(M: map K V)(vs: set V): map K V :=
  filter (fun '(ki, vi) => if in_dec veq vi vs then false else true) M.
