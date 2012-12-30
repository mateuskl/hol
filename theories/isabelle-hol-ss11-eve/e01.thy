theory AnotherList imports Datatype
begin 

datatype 'a list = Nil
                 | Cons 'a "'a list"

notation Nil ("[]")
notation Cons (infixr "#" 65) -- "a right-associative infix operator of priority 65"


primrec length :: "'a list \<Rightarrow> nat"
where
  "length [] = 0"
  | "length (x # xs) = (length xs) + 1"



value "length ([])"

value "lenght (1 # [])"

value "lenght  (True # [])"

value "(lenght  (True # False # []))"

end
