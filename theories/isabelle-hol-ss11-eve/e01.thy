theory AnotherList imports Datatype
begin 

datatype 'a list = Nil
                 | Cons 'a "'a list"

notation Nil ("[]")
notation Cons (infixr "#" 65) -- "a right-associative infix operator of priority 65"

primrec append :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" (infixr "@" 65)
where
  "[] @ ys = ys"
  | "(x # xs) @ ys = x # (xs @ ys)"

primrec rev :: "'a list => 'a list" where
  "rev [] = []"
| "rev (x#xs) = rev xs @ (x#[])"

lemma append_Nil2[simp]: "xs @ [] = xs"
  by (induct xs) simp_all

lemma append_assoc[simp]: "(xs @ ys) @ zs = xs @ ys @ zs"
  by (induct xs) simp_all

lemma rev_append[simp]: "rev (xs @ ys) = rev ys @ rev xs"
  by (induct xs) simp_all

theorem rev_rev_ident[simp]: "rev (rev xs) = xs"
  by (induct xs) simp_all


primrec length :: "'a list \<Rightarrow> nat"
where
  "length [] = 0"
  | "length (x # xs) = length xs + 1"


lemma length_append[simp]: "length (xs @ ys) = length xs + length ys"
  by (induct xs) simp_all


(* Another way to write the same proof *)
lemma length_append_v2[simp]: "length (xs @ ys) = length xs + length ys"
proof -
  show "length (xs @ ys) = length xs + length ys" by (induct xs) simp_all
qed

(* Exercise 3 *)
primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list"
where
  "snoc [] y = y # []"
  | "snoc (x # xs) y = x # snoc xs y"


(* Exercise 4 *)
lemma snoc_append[simp]: "snoc (xs @ ys) z = xs @ snoc ys z"
  by (induct xs) simp_all

lemma snoc_rev[simp]: "snoc (rev xs) x = rev (x # xs)"
  by (induct xs) simp_all


(* Exercise 5 *)
primrec replace :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list "
where
  "replace x y [] = []"
| "replace x y (z#zs) = (if z = x then y else z) # replace x y zs"


(* Some tests *)
value "length ([])"

value "lenght (1 # [])"

value "lenght  (True # [])"

value "(lenght  (True # False # []))"

end
