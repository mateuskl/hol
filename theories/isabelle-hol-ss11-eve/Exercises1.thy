theory Exercises1 imports Datatype begin

section {* Definitions *}

datatype 'a list = Nil ("[]")
                 | Cons 'a "'a list" (infixr "#" 65)

primrec
  append :: "'a list => 'a list => 'a list" (infixr "@" 65)
where
  "[] @ ys = ys"
| "(x#xs) @ ys = x # (xs @ ys)"

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


section {* Exercises *}

primrec length :: "'a list => nat" where
  "length [] = 0"
| "length (x#xs) = length xs + 1"

lemma length_append[simp]: "length (xs@ys) = length xs + length ys"
  by (induct xs) simp_all

primrec snoc :: "'a list => 'a => 'a list" where
  "snoc [] y = y#[]"
| "snoc (x#xs) y = x # snoc xs y"

lemma snoc_append[simp]: "snoc (xs@ys) z = xs @ snoc ys z"
  by (induct xs) simp_all

lemma snoc_rev[simp]: "snoc (rev xs) y = rev (y # xs)"
  by (induct xs) simp_all

primrec replace :: "'a => 'a => 'a list => 'a list" where
  "replace x y [] = []"
| "replace x y (z#zs) = (if z = x then y else z) # replace x y zs"

lemma replace_append[simp]:
  "replace x y (ws@zs) = replace x y ws @ replace x y zs"
  by (induct ws) simp_all

lemma rev_replace[simp]:
  "replace x y (rev zs) = rev (replace x y zs)"
  by (induct zs) simp_all

end
