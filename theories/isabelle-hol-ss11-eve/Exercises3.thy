theory Exercises3
imports Main
begin

section {* Elimination of Connectives *}

lemma eq_elim:
  "A = B \<longleftrightarrow> (A \<longrightarrow> B) \<and> (B \<longrightarrow> A)"
  by blast

lemma disj_elim:
  "A \<or> B \<longleftrightarrow> (A \<longrightarrow> False) \<longrightarrow> B"
  by blast

lemma not_elim:
  "\<not> A \<longleftrightarrow> A \<longrightarrow> False"
  by blast

lemmas elims[simp] = eq_elim disj_elim not_elim

lemma "A \<or> (B \<and> C) = A"
  apply (simp only: elims)
oops


section {* Propositional Logic *}

lemma I: "A \<longrightarrow> A" by (rule impI)

lemma "A \<and> B \<longrightarrow> B \<and> A"
proof (rule impI)
  assume "A \<and> B"
  show "B \<and> A"
  proof (rule conjI)
    from `A \<and> B` show "B" by (rule conjE)
  next
    from `A \<and> B` show "A" by (rule conjE)
  qed
qed

lemma "(A \<and> B) \<longrightarrow> (B \<or> A)"
proof (rule impI)
  assume "A \<and> B"
  hence "A" by (rule conjE)
  thus "B \<or> A" by (rule disjI2)
qed

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
proof (rule impI)
  assume "(A \<or> B) \<or> C"
  thus "A \<or> (B \<or> C)"
  proof (rule disjE)
    assume "A \<or> B"
    thus "A \<or> (B \<or> C)"
    proof (rule disjE)
      assume "A"
      thus "A \<or> (B \<or> C)" by (rule disjI1)
    next
      assume "B"
      hence "B \<or> C" by (rule disjI1)
      thus "A \<or> (B \<or> C)" by (rule disjI2)
    qed
  next
    assume "C"
    hence "B \<or> C" by (rule disjI2)
    thus "A \<or> (B \<or> C)" by (rule disjI2)
  qed
qed

lemma K: "A \<longrightarrow> B \<longrightarrow> A"
proof (rule impI)
  assume "A"
  show "B \<longrightarrow> A"
  proof (rule impI)
    assume "B"
    from I and `A` show A by (rule mp)
  qed
qed

lemma "(A \<or> A) = (A \<and> A)"
proof (rule iffI)
  assume "A \<or> A"
  thus "A \<and> A"
  proof (rule disjE)
    assume A
    from this and this show "A \<and> A" by (rule conjI)
  next
    assume A
    from this and this show "A \<and> A" by (rule conjI)
  qed
next
  assume "A \<and> A"
  hence "A" by (rule conjE)
  thus "A \<or> A" by (rule disjI1)
qed

lemma S: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
proof (rule impI)
  assume "A \<longrightarrow> B \<longrightarrow> C"
  show "(A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  proof (rule impI)
    assume "A \<longrightarrow> B"
    show "A \<longrightarrow> C"
    proof (rule impI)
      assume "A"
      with `A \<longrightarrow> B` have "B" by (rule mp)
      from `A \<longrightarrow> B \<longrightarrow> C` and `A` have "B \<longrightarrow> C" by (rule mp)
      from this and `B` show "C" by (rule mp)
    qed
  qed
qed

lemma "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "(B \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> C"
  proof (rule impI)
    assume "B \<longrightarrow> C"
    show "A \<longrightarrow> C"
    proof (rule impI)
      assume "A"
      with `A \<longrightarrow> B` have "B" by (rule mp)
      with `B \<longrightarrow> C` show "C" by (rule mp)
    qed
  qed
qed

lemma "\<not> \<not> A \<longrightarrow> A"
proof (rule impI)
  assume "\<not> \<not> A"
  show "A"
  proof (rule classical)
    assume "\<not> A"
    with `\<not> \<not> A` show "A" by (rule notE)
  qed
qed

lemma "A \<longrightarrow> \<not> \<not> A"
proof (rule impI)
  assume "A"
  show "\<not> \<not> A"
  proof (rule notI)
    assume "\<not> A"
    from this and `A` show "False" by (rule notE)
  qed
qed

lemma "(\<not> A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> A)"
proof (rule impI)
  assume "\<not> A \<longrightarrow> B"
  show "\<not> B \<longrightarrow> A"
  proof (rule impI)
    assume "\<not> B"
    show "A"
    proof (rule classical)
      assume "\<not> A"
      with `\<not> A \<longrightarrow> B`
      have "B" by (rule mp)
      with `\<not> B` show "A" by (rule notE)
    qed
  qed
qed

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof (rule impI)
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  show "A"
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof (rule impI)
      assume "A"
      with `\<not> A` show "B" by (rule notE)
    qed
    with `(A \<longrightarrow> B) \<longrightarrow> A` show "A" by (rule mp)
  qed
qed

lemma lem: "A \<or> \<not> A"
proof (rule classical)
  assume "\<not> (A \<or> \<not> A)"
  have "\<not> A"
  proof (rule notI)
    assume "A"
    hence "A \<or> \<not> A" by (rule disjI1)
    with `\<not> (A \<or> \<not> A)` show False by (rule notE)
  qed
  thus "A \<or> \<not> A" by (rule disjI2)
qed

lemma "(\<not> (A \<and> B)) = (\<not> A \<or> \<not> B)"
proof (rule iffI)
  assume "\<not> (A \<and> B)"
  have "A \<or> \<not> A" by (rule lem)
  thus "\<not> A \<or> \<not> B"
  proof (rule disjE)
    assume "A"
    have "B \<or> \<not> B" by (rule lem)
    thus "\<not> A \<or> \<not> B"
    proof (rule disjE)
      assume "B"
      with `A` have "A \<and> B" by (rule conjI)
      with `\<not> (A \<and> B)` show "\<not> A \<or> \<not> B" by (rule notE)
    next
      assume "\<not> B"
      thus "\<not> A \<or> \<not> B" by (rule disjI2)
    qed
  next
    assume "\<not> A"
    thus "\<not> A \<or> \<not> B" by (rule disjI1)
  qed
next
  assume "\<not> A \<or> \<not> B"
  thus "\<not> (A \<and> B)"
  proof (rule disjE)
    assume "\<not> A"
    show "\<not> (A \<and> B)"
    proof (rule notI)
      assume "A \<and> B"
      hence "A" by (rule conjE)
      with `\<not> A` show "False" by (rule notE)
    qed
  next
    assume "\<not> B"
    show "\<not> (A \<and> B)"
    proof (rule notI)
      assume "A \<and> B"
      hence "B" by (rule conjE)
      with `\<not> B` show "False" by (rule notE)
    qed
  qed
qed


section {* Predicate Logic *}

lemma "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
proof (rule impI)
  assume "\<exists>x. \<forall>y. P x y"
  thus "\<forall>y. \<exists>x. P x y"
  proof (rule exE)
    fix x
    assume "\<forall>y. P x y"
    show "\<forall>y. \<exists>x. P x y"
    proof (rule allI)
      fix y
      from `\<forall>y. P x y`
        have "P x y" by (rule allE)
      thus "\<exists>x. P x y" by (rule exI)
    qed
  qed
qed

text {*We switch to ASCII syntax, in order to show
the similarity.*}
lemma "(ALL x. P x --> Q) = ((EX x. P x) --> Q)"
proof (rule iffI)
  assume "ALL x. P x --> Q"
  show "((EX x. P x) --> Q)"
  proof (rule impI)
    assume "EX x. P x"
    thus "Q"
    proof (rule exE)
      fix x assume "P x"
      from `ALL x. P x --> Q`
        have "P x --> Q" by (rule allE)
      from this and `P x` show "Q" by (rule mp)
    qed
  qed
next
  assume "(EX x. P x) --> Q"
  show "ALL x. P x --> Q"
  proof (rule allI)
    fix x show "P x --> Q"
    proof (rule impI)
      assume "P x"
      hence "EX x. P x" by (rule exI)
      with `(EX x. P x) --> Q`
        show "Q" by (rule mp)
    qed
  qed
qed

lemma "((ALL x. P x) & (ALL x. Q x)) = (ALL x. (P x & Q x))"
proof (rule iffI)
  assume 1: "(ALL x. P x) & (ALL x. Q x)"
  show "ALL x. (P x & Q x)"
  proof (rule allI)
    fix x show "P x & Q x"
    proof (rule conjI)
      from 1 have "ALL x. P x" by (rule conjE)
      thus "P x" by (rule allE)
    next
      from 1 have "ALL x. Q x" by (rule conjE)
      thus "Q x" by (rule allE)
    qed
  qed
next
  assume 2: "ALL x. P x & Q x"
  show "(ALL x. P x) & (ALL x. Q x)"
  proof (rule conjI)
    show "ALL x. P x"
    proof (rule allI)
      fix x
      from 2 have "P x & Q x" by (rule allE)
      thus "P x" by (rule conjE)
    qed
  next
    show "ALL x. Q x"
    proof (rule allI)
      fix x
      from 2 have "P x & Q x" by (rule allE)
      thus "Q x" by (rule conjE)
    qed
  qed
qed

lemma "((ALL x. P x) | (ALL x. Q x)) = (ALL x. (P x | Q x))"
quickcheck
oops

lemma "((EX x. P x) | (EX x. Q x)) = (EX x. (P x | Q x))"
proof (rule iffI)
  assume "(EX x. P x) | (EX x. Q x)"
  thus "EX x. (P x | Q x)"
  proof (rule disjE)
    assume "EX x. P x"
    thus "EX x. (P x | Q x)"
    proof (rule exE)
      fix x assume "P x"
      hence "P x | Q x" by (rule disjI1)
      thus "EX x. (P x | Q x)" by (rule exI)
    qed
  next
    assume "EX x. Q x"
    thus "EX x. (P x | Q x)"
    proof (rule exE)
      fix x assume "Q x"
      hence "P x | Q x" by (rule disjI2)
      thus "EX x. (P x | Q x)" by (rule exI)
    qed
  qed
next
  assume "EX x. P x | Q x"
  thus "(EX x. P x) | (EX x. Q x)"
  proof (rule exE)
    fix x assume "P x | Q x"
    thus "(EX x. P x) | (EX x. Q x)"
    proof (rule disjE)
      assume "P x"
      hence "EX x. P x" by (rule exI)
      thus "(EX x. P x) | (EX x. Q x)" by (rule disjI1)
    next
      assume "Q x"
      hence "EX x. Q x" by (rule exI)
      thus "(EX x. P x) | (EX x. Q x)" by (rule disjI2)
    qed
  qed
qed

lemma "(ALL x. EX y. P x y) --> (EX y. ALL x. P x y)"
quickcheck
oops

lemma "(~ (ALL x. P x)) = (EX x. ~ P x)"
proof (rule iffI)
  assume "~ (ALL x. P x)"
  show "EX x. ~ P x"
  proof (rule classical)
    assume "~ (EX x. ~ P x)"
    have "ALL x. P x"
    proof (rule allI)
      fix x
      show "P x"
      proof (rule classical)
        assume "~ P x"
        hence "EX x. ~ P x" by (rule exI)
        with `~ (EX x. ~ P x)` show "P x" by (rule notE)
      qed
    qed
    with `~ (ALL x. P x)`
    show "EX x. ~ P x" by (rule notE)
  qed
next
  assume "EX x. ~ P x"
  thus "~ (ALL x. P x)"
  proof (rule exE)
    fix x assume "~ P x"
    show "~ (ALL x. P x)"
    proof (rule notI)
      assume "ALL x. P x"
      hence "P x" by (rule allE)
      with `~ P x` show False by (rule notE)
    qed
  qed
qed
  
end
