(* 
Exercise 2.5.1

Define the datatype of binary trees:
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

Define a function mirror that mirrors a binary tree by swapping subtrees
recursively. 

Prove
lemma mirror_mirror: "mirror(mirror t) = t"

Define a function flatten that flattens a tree into a list by traversing it in
infix order. 
Prove
lemma "flatten(mirror t) = rev(flatten t)"

*)
theory ToyBinaryThree
imports Main

begin
(* Datatype *)
datatype 'a tree = 
  Tip | 
  Node "'a tree" 'a "'a tree"


(* Function definitions *)
primrec mirror :: "'a tree \<Rightarrow> 'a tree"
where
  "mirror Tip = Tip " |
  "mirror (Node left v right) = Node (mirror (right)) v (mirror (left))"


primrec flatten :: "'a tree \<Rightarrow> 'a list"
where
  "flatten Tip = []" |
  "flatten (Node left v right) = flatten(left) @ [v] @ flatten(right)"

(* Some random tests *)
(* value "Node (Node (Node Tip 2 Tip) 1 (Node Tip 3 Tip)) 0 (Node (Node Tip 5 Tip) 4 (Node Tip 6 Tip)" *)
value "Tip"
value "Node Tip 2 Tip"
value "Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip)"
value "flatten(Node (Node Tip 0 Tip) 1 (Node Tip 2 Tip))"


(* Proofs *)
lemma mirror_mirror [simp]: "mirror(mirror t) = t"
apply (induct_tac t)
apply (auto)
done


lemma "flatten(mirror t) = rev(flatten t)"
apply(induct_tac t)
apply(auto) 
done

end

