Definition reverse_get(M: map K V)(v: V): option K :=
  snd (fold_left (fun '(seen_keys, res) '(ki, vi) =>
                    if in_dec keq ki seen_keys then (seen_keys, res)
                    else (ki :: seen_keys, if veq vi v then Some ki else res))
                 M (empty_set, None)).
