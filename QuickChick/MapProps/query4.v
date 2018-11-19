Conjecture query4: forall u1 u2 m p1 g1 p2 g2,
  extends u1 (update_map (remove_values m p1) g1) ->
  extends u2 (update_map (remove_values m p2) g2) ->
  extends (intersect_map u1 u2)
    (update_map (remove_values m (union p1 p2)) (intersect_map g1 g2)).
