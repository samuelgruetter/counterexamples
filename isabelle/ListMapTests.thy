theory ListMapTests
  imports Main
begin

typedecl K
typedecl V

datatype tuple = pair K V

datatype list = nil | cons tuple list

datatype option = None | Some V

fun get :: "list \<Rightarrow> K \<Rightarrow> option" where
  "get nil k = None" |
  "get (cons (pair ki vi) rest) k = 
    (if (ki = k) then Some vi else get rest k)"

fun filter :: "(tuple \<Rightarrow> bool) \<Rightarrow> list \<Rightarrow> list" where
  "filter f nil = nil" |
  "filter f (cons h t) =
     (if (f h) then (cons h (filter f t)) else (filter f t))"

fun remove :: "list \<Rightarrow> K \<Rightarrow> list" where
  "remove l k = filter (\<lambda> t. case t of pair ki vi \<Rightarrow> ki \<noteq> k) l"

fun put :: "list \<Rightarrow> K \<Rightarrow> V \<Rightarrow> list" where
  "put l k v = cons (pair k v) (remove l k)"

lemma "get (put l k1 v) k2 = get l k2"
  nitpick
(*
Nitpick found a counterexample for card K = 2 and card V = 2:

  Free variables:
    k1 = K\<^sub>1
    k2 = K\<^sub>1
    l = nil
    v = V\<^sub>1
*)
  oops

lemma "k1 \<noteq> k2 \<Longrightarrow> get (put l k1 v) k2 = get l k2"
  nitpick (* so it probably holds ;-) *)