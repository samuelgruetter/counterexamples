From QuickChick Require Import QuickChick.
Require Import SetAndMapLib.

Conjecture query1: forall m1 m2,
    disjoint (domain (remove_values m1 (range m2))) (domain m2).

(*! QuickChick query1. *)

(*
QuickChecking query1
[(2,5); (1,2); (0,1)]
[(0,0); (0,1)]
0
*** Failed after 13 tests and 12 shrinks. (0 discards)
*)

(* Isabelle:
Auto Quickcheck found a counterexample:
  m1 = [a2 -> a2]
  m2 = [a2 -> a1]
*)


Conjecture query2: forall g1 g2 p1 p2 r,
  subset (range g1) p1 ->
  subset (range g2) p2 ->
  extends (update_map (remove_values r p1) g1)
    (update_map (remove_values r (union p1 p2)) (intersect_map g1 g2)).

(* TC_FAIL QuickChick query2. *)

(* Isabelle:
Auto Quickcheck found a counterexample:
  g1 = [a2 -> a1]
  p1 = {a1}
  g2 = Map.empty
  p2 = {}
  r = [a2 -> a2]
*)


Conjecture query3: forall g1 p1 g2 p2 r,
  subset (range g1) p1 ->
  subset (range g2) p2 ->
  subset (range (intersect_map g1 g2)) (union p1 p2) ->
  extends (update_map (remove_values r p1) g1)
          (update_map (remove_values r (union p1 p2)) (intersect_map g1 g2)).

(* TC_FAIL QuickChick query3. *)

(* Isabelle:
Auto Quickcheck found a counterexample:
  g1 = [a2 -> a1]
  p1 = {a1}
  g2 = Map.empty
  p2 = {}
  r = [a2 -> a2]
*)


Conjecture query4: forall u1 u2 m p1 g1 p2 g2,
  extends u1 (update_map (remove_values m p1) g1) ->
  extends u2 (update_map (remove_values m p2) g2) ->
  extends (intersect_map u1 u2)
    (update_map (remove_values m (union p1 p2)) (intersect_map g1 g2)).

(* TC_FAIL QuickChick query4. *)

(* Isabelle:
Auto Quickcheck found a counterexample:
  u1 = [a2 ↦ a1]
  m = [a2 ↦ a1]
  p1 = {}
  g1 = Map.empty
  u2 = [a2 ↦ a2]
  p2 = {}
  g2 = [a2 ↦ a2]
*)
