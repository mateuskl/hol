header {* Session 2 *}
theory Session2 imports Main begin

section {* Simplification *}

text {*A datatype for natural numbers.*}
datatype num = Zero | Succ num

notation Zero ("0")

text {*'( produces a paranthesis, whereas ( allone would
just tell the parser that an indentation group is
starting (i.e., it just influences pretty printing).*}
notation Succ ("s'(_')")

text {*Immitating the rewrite rules for
addition on natural numbers.*}
(* equality has priority 50 in Isabelle/HOL *)
primrec
  add :: "num => num => num" (infixl "+" 65)
where
  "(0::num) + y = y"
| "s(x)     + y = s(x + y)"

text {*Immitating the rewrite rules for
multiplication on natural numbers.*}
primrec
  mul :: "num => num => num" (infixl "\<times>" 70)
where
  "(0::num) \<times> y = 0"
| "s(x) \<times> y     = y + (x \<times> y)"

text {*Automatic lemmas/simplification rules.*}
thm num.simps add.simps mul.simps

text {*Evaluate some terms to check the implementation.*}
value "(0::num) \<times> 0"
value "s(s(0)) \<times> s(s(0))"
value "s(s(s(s(0)))) \<times> s(s(s(s(0))))"

text {*Simplification rules are automatically applied when using "simp."*}
lemma "s(s(0)) \<times> s(s(0)) = s(s(s(s(0))))" by simp
lemma "s(s(0)) \<times> s(s(0)) = s(s(s(s(0))))" unfolding mul.simps add.simps by (rule refl)

text {*Removing simplification rules from the simpset.*}
(*
declare add.simps[simp del]
lemma "0 + s(0) = s(0)" by simp
*)

text {*A proof by "hand."*}
lemma "s(s(0)) \<times> s(s(0)) = s(s(s(s(0))))"
proof - (*we don't want to apply an initial method, hence "-"*)
  have "s(s(0)) \<times> s(s(0)) = s(s(0)) + s(0) \<times> s(s(0))" unfolding mul.simps by (rule refl)
  from this have "s(s(0)) \<times> s(s(0)) = s(s(0)) + (s(s(0)) + 0 \<times> s(s(0)))"
    unfolding mul.simps . (*abbreviates "by assumption"*)
  from this have "s(s(0)) \<times> s(s(0)) = s(s(0)) + (s(s(0)) + 0)"
    unfolding mul.simps .
  from this show ?thesis unfolding add.simps .
qed

text {*Modifiers for the "simp" method.*}
lemma "s(0) \<times> s(0) = s(0)" by (simp only: add.simps mul.simps)

text {*The general format of stating theorems.*}
lemma some_lemma[simp]: fixes A :: bool assumes AA:"A \<and> A" shows A: "A"
  using AA by simp

text {*By default assumptions are used for simplification.*}
lemma assumes "xs@zs = ys@xs" and "[]@xs = []@[]" shows "ys = zs"
  using assms by simp

text {*Sometimes assumptions cause nontermination.*}
lemma assumes "\<forall>x. f x = g (f (g x))" shows "f [] = f [] @ []"
  using assms by (simp (no_asm))

text {*Activate Tracing via Isabelle \<rightarrow> Settings \<rightarrow> Trasing \<rightarrow> 
Trace Simplifier.*}
lemma "s(s(0)) \<times> s(0) = s(s(0))" by simp

subsection {* Finding Theorems *}
text {*Find all theorems containing "simp" in their names, and having an
addition as subterm, but no multiplication.*}
find_theorems name: simp "op + :: num \<Rightarrow> num \<Rightarrow> num" -"op \<times> :: num \<Rightarrow> num \<Rightarrow> num"


section {* Function Definitions *}
fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = Suc 0"
| "fib (Suc 0) = Suc 0"
| "fib (Suc (Suc n)) = fib n + fib (Suc n)"

value "fib(Suc(Suc(Suc(Suc(Suc(Suc(0)))))))"

lemma fib_gt_0[simp]: "0 < fib n"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  hence IH: "0 < fib n" .
  thus ?case
  proof (cases n)
    case 0 show ?thesis unfolding 0 by simp
  next
    case (Suc m) show ?thesis using IH unfolding Suc by simp
  qed
qed

text {*Two examples of functions that are not proved to be terminating
automatically.*}

function evenodd :: "bool => nat => bool" where
  "evenodd b 0 = (\<not> b)"
| "evenodd False (Suc n) = evenodd True n"
| "evenodd True (Suc n) = (\<not> evenodd False (Suc n))"
  by (pat_completeness) auto
abbreviation bool2nat where "bool2nat b \<equiv> if b then 1 else 0"
termination
  by (relation "measures [size \<circ> snd, bool2nat \<circ> fst]")
     simp+

thm evenodd.simps

function (sequential) f :: "nat => nat" where
  "f 0 = 0"
| "f x = (if x mod 2 = 0 then f (x - 2) else f (x + 1))"
  by (pat_completeness) auto
termination
  by (relation "measure (\<lambda>x. x + (if x mod 2 = 0 then 0 else 1) * 2)") 
     (auto, arith+)

thm f.simps


section {* Calculational Reasoning *}

primrec sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0"
| "sum (Suc n) = Suc n + sum n"

text {* An Example Proof. *}
lemma "sum n = (n * (Suc n)) div (Suc (Suc 0))"
proof (induct n)
 case 0 show ?case by simp
next
 case (Suc n)
 hence IH: "sum n = (n*(Suc n)) div (Suc(Suc 0))" .
 have "sum(Suc n) = Suc n + sum n" by simp
 also have "\<dots> = Suc n + ((n*(Suc n)) div (Suc(Suc 0)))" unfolding IH by simp
 also have "\<dots> = ((Suc(Suc 0) * Suc n) div Suc(Suc 0)) + ((n*(Suc n)) div Suc(Suc 0))" by arith
 also have "\<dots> = (Suc(Suc 0) * Suc n + n*(Suc n)) div Suc(Suc 0)" by arith
 also have "\<dots> = ((Suc(Suc 0) + n) * Suc n) div Suc(Suc 0)" unfolding add_mult_distrib by simp
 also have "\<dots> = (Suc(Suc n) * Suc n) div Suc(Suc 0)" by simp
 finally show ?case by simp
qed

end
