theory MapTests
  imports Main Set Map
begin

definition empty_set ::  "'a set" where
  "empty_set \<equiv> {}"

definition singleton_set :: "'a \<Rightarrow> 'a set" where
  "singleton_set x \<equiv> { x }"

definition disjoint :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "disjoint A B \<equiv> (A \<inter> B = {})"

definition diff :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "diff A B \<equiv> A - B"

definition get :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "get m ki \<equiv> m ki"

definition put :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "put m ki vi k0 \<equiv> if k0 = ki then Some vi else m k0"

definition domain :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set" where
  "domain M \<equiv> dom M"

definition range :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'v set" where
  "range M \<equiv> ran M"

definition remove_keys :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'k set \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "remove_keys M ks = (\<lambda>k. if k \<in> ks then None else M k)"

(*
definition reverse_get :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'v \<Rightarrow> 'k option " where
  "reverse_get M v0 \<equiv> if (\<exists> k0. M k0 = Some v0) then Some k0 else None"
*)

definition remove_values :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'v set \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "remove_values M A \<equiv> (\<lambda>k. case M k of
                               None \<Rightarrow> None
                             | Some a \<Rightarrow> if a \<in> A then None else Some a)"

definition remove_by_value :: "('k \<rightharpoonup> 'v) \<Rightarrow> 'v \<Rightarrow> ('k \<rightharpoonup> 'v)" where
  "remove_by_value M v0 \<equiv> remove_values M (singleton_set v0)"

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

lemma test : "disjoint (domain (remove_values m1 (range m2))) (domain m2)"
(*
Auto Quickcheck found a counterexample:
  m1 = [a\<^sub>2 \<mapsto> a\<^sub>2]
  m2 = [a\<^sub>2 \<mapsto> a\<^sub>1]
*)
  oops

lemma test: "
  subset (range g1) p1 \<Longrightarrow>
  subset (range g2) p2 \<Longrightarrow>
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

lemma foo: "\<not> (\<forall> m. \<forall> n. subset m n)"
(* sledgehammer:
Proof found... 
"e": Try this: by (meson empty_iff insert_subset subset_def) (5 ms) 
"spass": Try this: by (meson empty_iff insert_subset subset_def) (4 ms) 
"z3": Try this: by (metis Un_absorb2 Un_insert_right empty_iff singletonI subset_Un_eq subset_def) (12 ms) 
"cvc4": Try this: by (meson empty_iff insert_subset subset_def) (12 ms)
*)
  by (meson empty_iff insert_subset subset_def)

lemma foo2: "\<not> (\<forall> m. \<forall> n. (subset m n \<longrightarrow> subset n m))"
  by (meson empty_iff empty_subsetI insert_subset subset_def)

lemma foo2a: "(\<forall> m. \<forall> n. (subset m n \<longrightarrow> subset n m))"
(* Auto Quickcheck finds a counterexample, and sledgehammer times out *)
  oops

lemma test: "
  subset (range g1) p1 \<Longrightarrow>
  subset (range g2) p2 \<Longrightarrow>
  subset (range (intersect_map g1 g2)) (union p1 p2) \<Longrightarrow>
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

lemma test: "
  extends u1 (update_map (remove_values m p1) g1) \<Longrightarrow>
  extends u2 (update_map (remove_values m p2) g2) \<Longrightarrow>
  subset (range g1) p1 \<Longrightarrow>
  subset (range g2) p2 \<Longrightarrow>
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
  p2 = {a\<^sub>2}
  g2 = [a\<^sub>2 \<mapsto> a\<^sub>2]
*)
  oops

lemma test: "
  extends u1 (update_map (remove_keys (remove_values m ps1) pi1) g1) \<Longrightarrow>
  extends u2 (update_map (remove_keys (remove_values m ps2) pi2) g2) \<Longrightarrow>
  subset (range g1) ps1 \<Longrightarrow>
  subset (range g2) ps2 \<Longrightarrow>
  subset (domain g1) pi1 \<Longrightarrow>
  subset (domain g2) pi2 \<Longrightarrow>
  extends (intersect_map u1 u2)
    (update_map (remove_keys (remove_values m (union ps1 ps2)) (union pi1 pi2))
       (intersect_map g1 g2))
"
  (* Auto Quickcheck doesn't say anything *)
  (* nitpick [timeout = 500] *) (* Nitpick found no counterexample *)
  oops

lemma test: "
  extends (f2 (f1 m)) (update_map (remove_keys (remove_values (f1 m) ps2) pi2) g2) \<Longrightarrow>
  extends (f1 m) (update_map (remove_keys (remove_values m ps1) pi1) g1) \<Longrightarrow>
  subset (range g1) ps1 \<Longrightarrow>
  subset (range g2) ps2 \<Longrightarrow>
  subset (domain g1) pi1 \<Longrightarrow>
  subset (domain g2) pi2 \<Longrightarrow>
  extends (f2 (f1 m))
    (update_map (remove_keys (remove_values m (union ps1 ps2)) (union pi1 pi2))
       (update_map g1 g2))
"
  nitpick
(* Nitpick found a counterexample for card 'a = 1 and card 'b = 1:

  Free variables:
    f1 = (\<lambda>x. _)(Map.empty := [a\<^sub>1 \<mapsto> b\<^sub>1], [a\<^sub>1 \<mapsto> b\<^sub>1] := Map.empty)
    f2 = (\<lambda>x. _)(Map.empty := [a\<^sub>1 \<mapsto> b\<^sub>1], [a\<^sub>1 \<mapsto> b\<^sub>1] := Map.empty)
    g1 = [a\<^sub>1 \<mapsto> b\<^sub>1]
    g2 = Map.empty
    m = Map.empty
    pi1 = {a\<^sub>1}
    pi2 = {a\<^sub>1}
    ps1 = {b\<^sub>1}
    ps2 = {}
  Skolem constant:
    ??.Ball.x = a\<^sub>1
*)
  oops

lemma test: "
  (subset pi1 empty_set \<Longrightarrow> subset ps1 empty_set) \<Longrightarrow>
  (subset ps1 empty_set \<Longrightarrow> subset pi1 empty_set) \<Longrightarrow>
  (subset pi2 empty_set \<Longrightarrow> subset ps2 empty_set) \<Longrightarrow>
  (subset ps2 empty_set \<Longrightarrow> subset pi2 empty_set) \<Longrightarrow>
  extends (f2 (f1 m)) (update_map (remove_keys (remove_values (f1 m) ps2) pi2) g2) \<Longrightarrow>
  extends (f1 m) (update_map (remove_keys (remove_values m ps1) pi1) g1) \<Longrightarrow>
  subset (range g1) ps1 \<Longrightarrow>
  subset (range g2) ps2 \<Longrightarrow>
  subset (domain g1) pi1 \<Longrightarrow>
  subset (domain g2) pi2 \<Longrightarrow>
  extends (f2 (f1 m))
    (update_map (remove_keys (remove_values m (union ps1 ps2)) (union pi1 pi2))
       (update_map g1 g2))
"
  nitpick
(* Nitpick found a counterexample for card 'a = 1 and card 'b = 1:

  Free variables:
    f1 = (\<lambda>x. _)(Map.empty := [a\<^sub>1 \<mapsto> b\<^sub>1], [a\<^sub>1 \<mapsto> b\<^sub>1] := Map.empty)
    f2 = (\<lambda>x. _)(Map.empty := [a\<^sub>1 \<mapsto> b\<^sub>1], [a\<^sub>1 \<mapsto> b\<^sub>1] := Map.empty)
    g1 = [a\<^sub>1 \<mapsto> b\<^sub>1]
    g2 = Map.empty
    m = Map.empty
    pi1 = {a\<^sub>1}
    pi2 = {a\<^sub>1}
    ps1 = {b\<^sub>1}
    ps2 = {b\<^sub>1}
  Skolem constants:
    ??.Ball.x = a\<^sub>1
    ??.less_eq_fun.x = a\<^sub>1
    ??.less_eq_fun.x = b\<^sub>1
    ??.less_eq_fun.x = a\<^sub>1
    ??.less_eq_fun.x = b\<^sub>1
*)
  oops

lemma test: "
  (\<forall> k . get m k \<noteq> Some a) \<Longrightarrow>
  get (remove_values m (diff (range m) (union (singleton_set a) (diff l (singleton_set x))))) i =
  Some x \<Longrightarrow> False
"
  nitpick
  (* Nitpick found no counterexample *)
  oops

lemma test: "
  (\<forall> k. get m k \<noteq> Some a) \<Longrightarrow>
  (\<forall> k.
   get (remove_values m (diff (range m) (union (singleton_set a) (diff l (singleton_set x)))))
     k \<noteq> Some x) \<Longrightarrow> False
"
(*
Auto Quickcheck found a counterexample:
  m = Map.empty
  a = a\<^sub>1
  l = {}
  x = a\<^sub>1
*)
  oops

lemma test: "
  subset l (union (range m) (singleton_set x)) \<Longrightarrow>
  get (remove_values m (diff (range m) (union (singleton_set a) (diff l (singleton_set x))))) i =
  Some x \<Longrightarrow>
  subset l (range (put (remove_by_value m x) i x))
"
  (* Auto Quickcheck doesn't say anything *)
  (* nitpick [timeout = 500] *) (* Nitpick found no counterexample *)
  oops
