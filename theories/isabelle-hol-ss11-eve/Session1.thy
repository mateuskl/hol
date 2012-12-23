header {* Session 1 *}
theory Session1 imports Datatype begin

section {* Functional Programming in HOL *}

subsection {*A Datatype for Lists*}
datatype 'a list = Nil
                 | Cons 'a "'a list"

text {*Some example lists.*}
term "Nil"                 -- "the empty list"
term "Cons (0::nat) Nil"   -- "singleton list [0]"
term "Cons 0 (Cons 1 Nil)" -- "2-element list [0, 1]"

subsection {*Syntactic Sugar for Lists*}
notation Nil ("[]")
notation Cons (infixr "#" 65) -- "a right-associative infix operator of priority 65"

(* It would also be possible to use

  datatype 'a list = Nil ("[]")
                   | Cons 'a "'a list" (infixr "#" 65)

and thereby combine special notation for lists with their declaration.
*)

subsection {*Example Lists*}
text {*Notations are applied before printing (check the output of the
statements below).*}
term "Nil"
term "Cons (0::nat) Nil"
term "Cons 0 (Cons 1 Nil)"
text {*Of course, notation may also be used in input.*}
term "[]"
term "0 # []"
term "0 # 1 # []"
text {*Note: space between # and any numeral (e.g.,
0, 1, 2, 3) is important.*}

text {*Many lemmas for lists are proved automatically.*}
find_theorems name:list

subsection {*Example - Concatenating two Lists*}
primrec
  append :: "'a list => 'a list => 'a list" (infixr "@" 65)
where
  "[] @ ys = ys"
| "(x # xs) @ ys = x # (xs @ ys)"

subsection {*Example - Reversing a List*}
primrec rev :: "'a list => 'a list" where
  "rev [] = []"
| "rev (x # xs) = rev xs @ (x # [])"

subsection {*An Introductory Proof*}
lemma append_Nil2[simp]: "xs @ [] = xs" by (induct xs) simp_all

lemma append_assoc[simp]: "(xs @ ys) @ zs = xs @ (ys @ zs)"
  by (induct xs) simp_all

lemma rev_append[simp]: "rev (xs @ ys) = rev ys @ rev xs"
  by (induct xs) simp_all

theorem rev_rev_ident[simp]: "rev (rev xs) = xs" by (induct xs) simp_all

subsection {*Definitions - Type Synonyms*}
type_synonym number    =  nat
type_synonym gate      =  "bool => bool => bool"
type_synonym 'a plist  =  "('a * 'a) list"

typ gate
typ "'a plist"

subsection {*Definitions - Constant Definitions*}
definition nand :: gate
where "nand x y == ~(x & y)"

definition xor  :: gate
where "xor  x y == (x & ~y) | (~x & y)"

text {*Provided lemmas.*}
thm nand_def
thm xor_def

subsection {*The Definitional Approach*}

axiomatization f :: "nat => nat" where
  f_def: "f x = f x + 1"

lemma everything: "P"
proof -
  fix x
  have "f x = f x + 1" by (rule f_def)
  from this show "P" by simp
qed

lemma wrong: "0 = 1" by (rule everything)

end
