theory Tests imports Main begin

lemma foo: "\<not> (True = False)"
  by auto



lemma foo2: "(\<forall> P. P) \<Longrightarrow> P"



lemma foo2: "\<forall> P . \<forall> Q . ((P \<Longrightarrow> Q \<and> P) \<Longrightarrow> Q)"