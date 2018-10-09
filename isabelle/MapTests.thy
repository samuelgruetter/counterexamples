theory MapTests
  imports Main Set Map
begin

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "disjoint A B \<equiv> (A \<inter> B = {})"

definition remove_values :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'v set \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "remove_values M A \<equiv> (\<lambda>k. case M k of
                               None \<Rightarrow> None
                             | Some a \<Rightarrow> if a \<in> A then None else Some a)"

definition extends :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> bool" where
  "extends M1 M2 \<equiv> M2 \<subseteq>\<^sub>m M1"

definition subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset s1 s2 \<equiv> s1 \<subseteq> s2"

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "union s1 s2 \<equiv> s1 \<union> s2"

definition update_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "update_map m1 m2 \<equiv> m1 ++ m2"

definition intersect_map :: "('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v) \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "intersect_map m1 m2 \<equiv> \<lambda>k. case m1 k of 
                                None \<Rightarrow> None
                              | Some v1 \<Rightarrow> (case m2 k of
                                  None \<Rightarrow> None
                                | Some v2 \<Rightarrow> if v1 = v2 then Some v1 else None)"

lemma test : "disjoint (dom (remove_values m1 (ran m2))) (dom m2)"
(*
Auto Quickcheck found a counterexample:
  m1 = [a\<^sub>2 \<mapsto> a\<^sub>2]
  m2 = [a\<^sub>2 \<mapsto> a\<^sub>1]
*)
  oops

lemma test: "
  subset (ran g1) p1 \<Longrightarrow>
  subset (ran g2) p2 \<Longrightarrow>
  extends (update_map (remove_values r p1) g1)
    (update_map (remove_values r (union p1 p2)) (intersect_map g1 g2))
"
  nitpick
(*
Nitpick found a counterexample for card 'a = 3 and card 'b = 3:

  Free variables:
    g1 = [b\<^sub>1 \<mapsto> a\<^sub>1, b\<^sub>2 \<mapsto> a\<^sub>1]
    g2 = [b\<^sub>1 \<mapsto> a\<^sub>1, b\<^sub>3 \<mapsto> a\<^sub>1]
    p1 = {a\<^sub>1}
    p2 = {a\<^sub>1}
    r = [b\<^sub>2 \<mapsto> a\<^sub>3, b\<^sub>3 \<mapsto> a\<^sub>1]
  Skolem constant:
    ??.Ball.x = b\<^sub>2
*)
(*
Auto Quickcheck found a counterexample:
  g1 = [a\<^sub>2 \<mapsto> a\<^sub>1]
  p1 = {a\<^sub>1}
  g2 = Map.empty
  p2 = {}
  r = [a\<^sub>2 \<mapsto> a\<^sub>2]
*)
  oops

lemma test: "
  subset (ran g1) p1 \<Longrightarrow>
  subset (ran g2) p2 \<Longrightarrow>
  subset (ran (intersect_map g1 g2)) (union p1 p2) \<Longrightarrow>
  extends (update_map (remove_values r p1) g1)
    (update_map (remove_values r (union p1 p2)) (intersect_map g1 g2))
"
(*
Auto Quickcheck found a counterexample:
  g1 = [a\<^sub>2 \<mapsto> a\<^sub>1]
  p1 = {a\<^sub>1}
  g2 = Map.empty
  p2 = {}
  r = [a\<^sub>2 \<mapsto> a\<^sub>2]
*)
  oops

lemma test: "
  extends u1 (update_map (remove_values m p1) g1) \<Longrightarrow>
  extends u2 (update_map (remove_values m p2) g2) \<Longrightarrow>
  extends (intersect_map u1 u2)
    (update_map (remove_values m (union p1 p2)) (intersect_map g1 g2))
"
(*
Auto Quickcheck found a counterexample:
  u1 = [a\<^sub>2 \<mapsto> a\<^sub>1]
  m = [a\<^sub>2 \<mapsto> a\<^sub>1]
  p1 = {}
  g1 = Map.empty
  u2 = [a\<^sub>2 \<mapsto> a\<^sub>2]
  p2 = {}
  g2 = [a\<^sub>2 \<mapsto> a\<^sub>2]
*)
  oops
