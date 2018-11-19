Conjecture query2: forall g1 g2 p1 p2 r,
  subset (range g1) p1 ->
  subset (range g2) p2 ->
  extends (update_map (remove_values r p1) g1)
    (update_map (remove_values r (union p1 p2)) (intersect_map g1 g2)).
