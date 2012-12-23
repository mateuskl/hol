theory Session4 imports Main begin

section {* Sets *}
text {*A set is defined by its characteristic function.
Have a look at the type of sets.*}
typ "'a set"

text {*An element `x' is a member of the set `S', if the
characteristic function of `S' returns `True'. *}
thm mem_def

subsection {*Basic Operations*}
subsubsection {*Intersection*}
text {*Notation*}
term "A \<inter> B"
text {*ASCII*}
term "A Int B"
text {* Natural deduction rules. *}
thm IntI IntD1 IntD2 IntE

subsubsection {*Union*}
text {*Notation*}
term "A \<union> B"
text {*ASCII*}
term "A Un B"
text {*Natural deduction rules.*}
thm UnI1 UnI2 UnE

subsection {*Set Notation*}
text {*The empty set.*}
term "{}"
text {*The universal set.*}
term "UNIV"
text {*Singleton sets.*}
term "{x}"
text {*Insertion.*}
term "insert x A"
thm insert_is_Un

text {*An example proof.*}
lemma
  "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  (is "?lhs = ?rhs")
proof (rule equalityI)
  show "?lhs \<subseteq> ?rhs"
  proof (rule subsetI)
    fix x assume "x \<in> ?lhs"
    hence "x \<in> A" by (rule IntD1)
    from `x \<in> ?lhs` have "x \<in> B \<union> C" by (rule IntD2)
    thus "x \<in> ?rhs"
    proof (rule UnE)
      assume "x \<in> B"
      with `x \<in> A` have "x \<in> A \<inter> B" by (rule IntI)
      thus "x \<in> ?rhs" by (rule UnI1)
    next
      assume "x \<in> C"
      with `x \<in> A` have "x \<in> A \<inter> C" by (rule IntI)
      thus "x \<in> ?rhs" by (rule UnI2)
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof (rule subsetI)
    fix x assume "x \<in> ?rhs"
    thus "x \<in> ?lhs"
    proof (rule UnE)
      assume "x \<in> A \<inter> B"
      hence "x \<in> A" by (rule IntD1)
      from `x \<in> A \<inter> B` have "x \<in> B" by (rule IntD2)
      hence "x \<in> B \<union> C" by (rule UnI1)
      with `x \<in> A` show "x \<in> ?lhs" by (rule IntI)
    next
      assume "x \<in> A \<inter> C"
      hence "x \<in> A" by (rule IntD1)
      from `x \<in> A \<inter> C` have "x \<in> C" by (rule IntD2)
      hence "x \<in> B \<union> C" by (rule UnI2)
      with `x \<in> A` show "x \<in> ?lhs" by (rule IntI)
    qed
  qed
qed

text {*And now shorter.*}
lemma "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)" by blast

subsection {*Examples of Set Comprehension*}
text {*The set of all elements satisfying P.*}
term "{x. P x}"
text {*The set of all pairs where the first component comes
from A and the second component form B.*}
term "{(x, y) | x y. x \<in> A \<and> y \<in> B}"

subsection{*Binding Operators for Sets*}
term "\<forall>x\<in>A. P x"
term "\<exists>x\<in>A. P x"
thm ballI bspec bexI bexE

subsection {*Relations*}
text {*A relation is represented by a set of pairs.*}
text {*The identity relation.*}
term "Id"
thm Id_def

text {*Composition of relations.*}
term "r O s"
thm rel_comp_def

text {*Inverse of a relation.*}
term "r^-1"
thm converse_iff

lemma
  "(r O s)^-1 = s^-1 O r^-1" 
  (is "?lhs = ?rhs")
proof (rule equalityI)
  show "?lhs \<subseteq> ?rhs"
  proof (rule subsetI)
    fix xy assume "xy \<in> ?lhs"
    thus "xy \<in> ?rhs"
    proof (rule converseE)
      fix y x assume "xy = (x, y)" and "(y, x) \<in> r O s"
      from `(y, x) \<in> r O s` show "xy \<in> ?rhs" unfolding `xy = (x, y)`
      proof (rule rel_compEpair)
        fix z assume "(y, z) \<in> r" and "(z, x) \<in> s"
        from `(z, x) \<in> s` have "(x, z) \<in> s^-1" by (rule converseI)
        moreover from `(y, z) \<in> r` have "(z, y) \<in> r^-1" by (rule converseI)
        ultimately show "(x, y) \<in> ?rhs" by (rule rel_compI)
      qed
    qed
  qed
next
  show "?rhs \<subseteq> ?lhs"
  proof (rule subsetI)
    fix xy assume "xy \<in> ?rhs"
    thus "xy \<in> ?lhs"
    proof (rule rel_compE)
      fix x z y assume "xy = (x, y)" and "(x, z) \<in> s^-1" and "(z, y) \<in> r^-1"
      from `(z, y) \<in> r^-1` have "(y, z) \<in> r" by (rule converseD)
      moreover from `(x, z) \<in> s^-1` have "(z, x) \<in> s" by (rule converseD)
      ultimately have "(y, x) \<in> r O s" by (rule rel_compI)
      thus "xy \<in> ?lhs" unfolding `xy = (x, y)` by (rule converseI)
    qed
  qed
qed

text {* Reflexive and transitive closure. *}
term "r^*"
term "r^+"
thm rtrancl_refl r_into_rtrancl rtrancl_trans


section {* Inductively Defined Sets *}

inductive_set
  even :: "nat set"
where
  zero[intro!]: "0 \<in> even"
| step[intro!]: "n \<in> even \<Longrightarrow> Suc(Suc n) \<in> even"

text {*Automatically generated lemms.*}
thm even.zero even.step even.cases even.induct

text {*Have a look at the definition of `dvd'.*}
thm dvd_def

text {*Have a look at the induction rule for `even'.*}
thm even.induct

text {*Every even number is divisible by 2.*}
lemma even_imp_2_dvd: "n \<in> even \<Longrightarrow> 2 dvd n"
proof (induct rule: even.induct)
  case zero show ?case by simp
next
  case (step n)
  hence IH: "2 dvd n" by simp
  thus ?case
  proof (rule dvdE)
    fix k assume "n = 2 * k"
    hence "Suc (Suc n) = 2 * (Suc k)" by arith
    thus ?case by (rule dvdI)
  qed
qed

text {*A number that is divisible by 2 is even.*}
lemma two_times_even[intro!]: "2 * k \<in> even"
  by (induct k) auto

lemma dvd_imp_even: "2 dvd n \<Longrightarrow> n \<in> even"
  unfolding dvd_def by auto
  
text {*A number is even iff it is divisible by 2.*}
lemma even_iff_dvd: "(n \<in> even) = (2 dvd n)"
proof
 assume "n \<in> even" thus "2 dvd n" by (rule even_imp_2_dvd)
next
 assume "2 dvd n" thus "n \<in> even" by (rule dvd_imp_even)
qed

subsection {*Advanced Inductive Sets*}
text {*The reflexive and transitive closure.*}
inductive_set
  rtc :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" ("_*" [1000] 999)
  for r :: "('a \<times> 'a) set"
where
  refl: "(x, x) \<in> r*"
| step: "(x, y) \<in> r \<Longrightarrow> (y, z) \<in> r* \<Longrightarrow> (x, z) \<in> r*"

text {*rtc is obviously reflexive (by rule rtc_refl).
Now we show that it is indeed transitive.*}
lemma rtc_trans:
  assumes "(x, y) \<in> r*" and "(y, z) \<in> r*"
  shows "(x, z) \<in> r*"
using assms
proof (induct rule: rtc.induct)
  case (refl x) thus ?case .
next
  case (step w x y)
  hence IH: "(x, z) \<in> r*" by simp
  from `(w, x) \<in> r` and IH show ?case by (rule rtc.step)
qed

end