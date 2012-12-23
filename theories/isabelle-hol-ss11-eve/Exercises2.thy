header {* Power, Sum *}
theory Exercises2 imports Main begin

section {* Power *}

text {*Define a primitive recursive function @{text "pow x n"} that computes the
$n$-th power of a natural number $x$.*}

primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pow x 0 = Suc 0"
| "pow x (Suc n) = x * pow x n"

text {*Prove the well-known equation $x^{m \cdot n} = (x^m)^n$.*}

(* Needed in the base case: 1^n = 1 *)
lemma pow_Suc_0[simp]: "pow (Suc 0) n = Suc 0"
  by (induct n) simp_all

(* Needed in the step case: x^(m+n) = x^m * x^n *)
lemma pow_sum[simp]: "pow x (m + n) = pow x m * pow x n"
  by (induct m) simp_all

(* Also needed in the step case:  (x*y)^n = x^n * y^n *)
lemma pow_mult_distrib[simp]: "pow (x * y) n = pow x n * pow y n"
  by (induct n) simp_all

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  by (induct m) simp_all


section {* Summation *}

text {*Define a (primitive recursive) function @{text "sum ns"} that sums a list of natural
numbers: $sum~[n_1, \dots, n_k] = n_1 + \cdots + n_k$.*}

primrec sum :: "nat list \<Rightarrow> nat" where
  "sum [] = 0"
| "sum (n # ns) = n + sum ns"

text {*Show that @{term "sum"} is compatible with @{term "rev"}.
You may need an auxiliary lemma.*}

(* Needed in the step case. *)
lemma sum_append[simp]: "sum (xs @ ys) = sum xs + sum ys"
  by (induct xs) simp_all

theorem sum_rev: "sum (rev ns) = sum ns"
  by (induct ns) simp_all

text {*Define a function @{text "Sum f k"} that sums @{term "f"} from @{term "0::nat"} up
to @{term "(k::nat) - 1"}: $Sum~f~k = f~0 + \cdots + f~(k-1)$.*}

fun Sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "Sum f 0 = 0"
| "Sum f (Suc k) = Sum f k + f k"

text {*Show the following equations for the pointwise summation of functions. Determine
first what the expression @{text "whatever"} should be.*}
theorem "Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k" oops
theorem "Sum f (k + l) = Sum f k + Sum whatever l" oops

theorem "Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k"
  by (induct k) simp_all

theorem "Sum f (k + l) = Sum f k + Sum (\<lambda>i. f (k + i)) l"
  by (induct l) simp_all

text {*What is the relationship between @{term "Sum"} and @{term "sum"}? Prove the following
equation, suitably instantiated.*}
theorem "Sum f k = sum whatever" oops

theorem "Sum f k = sum (map f [0..<k])"
  by (induct k) simp_all

end
