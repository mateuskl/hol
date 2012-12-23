theory Session3 imports Main begin

section {* Natural Deduction *}
text {*Isabelle/HOL rules for conjunction.*}
thm conjI conjunct1 conjunct2

text {*An example using the `rule' method.*}
lemma assumes pq: "p \<and> q" and "r" shows "p \<and> (q \<and> r)" (is ?goal)
proof -
  from pq have "q" by (rule conjunct2)
  from pq have "p" by (rule conjunct1)
  moreover
    from `q` and `r` have "q \<and> r" by (rule conjI)
  ultimately
    show ?goal by (rule conjI)
qed

section {* Propositional Logic *}
text {*Natural Deduction Rules.*}
thm conjI
thm conjunct1 conjunct2
thm disjI1 disjI2
thm disjE
thm impI
thm mp
thm notI
thm notE

subsection {*Some derived rules.*}
text {*Double negation introduction.*}
lemma assumes "P" shows "\<not>\<not>P"
proof (rule notI)
  assume "\<not>P"
  from this and `P` show False by (rule notE)
qed

text {*Law of the excluded middle.*}
lemma lem: "P \<or> \<not>P"
proof (cases P)
  case True thus ?thesis by (rule disjI1)
next
  case False thus ?thesis by (rule disjI2)
qed

text {*Double negation elimination.*}
lemma notnotE: assumes "\<not>\<not>P" shows "P"
proof -
  have "P \<or> \<not>P" by (rule lem)
  thus ?thesis
  proof (rule disjE)
    assume "P" thus ?thesis .
  next
    assume "\<not>P" with `\<not>\<not>P` show ?thesis by (rule notE)
  qed
qed

text {*Double negation elimination (using raw proof blocks
and moreover).*}
lemma notnotE': assumes "\<not>\<not>P" shows "P"
proof -
  have "P \<or> \<not>P" by (rule lem)
  moreover {
    assume "P"
    hence "P" .
  }
  moreover {
    assume "\<not>P"
    from `\<not>\<not>P` and this
    have "P" by (rule notE)
  }
  ultimately show ?thesis by (rule disjE)
qed

text {*Proof by contradiction.*}
lemma pbc: assumes "\<not>P \<Longrightarrow> False" shows "P"
proof -
 from assms have "\<not>\<not>P" by (rule notI)
 thus ?thesis by (rule notnotE)
qed

section {* Predicate Logic *}
text {*Meta for all introduction.*}
lemma "\<And>x. x = x"
proof -
  fix x
  show "x = x" by (rule refl)
qed

text {*Obtaining some term that is guaranteed to exist.*}
lemma assumes "\<exists>x. P x" shows "\<exists>y. P y"
proof -
  from assms obtain y where "P y" by (rule exE)
  thus ?thesis by (rule exI)
qed

text {*A proof using quantifiers.*}
lemma
  assumes ex: "\<exists>x. \<forall>y. P x y"
  shows "\<forall>y. \<exists>x. P x y"
proof (* here `allI' is used by default. *)
  fix y
  from ex obtain x where "\<forall>y. P x y" by (rule exE)
  hence "P x y" by (rule spec)
  thus "\<exists>x. P x y" by (rule exI)
qed

end
