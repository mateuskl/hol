theory PointTheory
imports Main
begin

record point = 
  Xcoord :: int
  Ycoord :: int

fun distance :: "point \<Rightarrow> point \<Rightarrow> int" where
"distance p1 p2 = Xcoord p1 + Xcoord p2" 


(* Some tests *)

definition aPoint :: point where
"aPoint \<equiv> \<lparr> Xcoord = 1, Ycoord = -2 \<rparr>"

definition otherPoint :: point where
"otherPoint \<equiv> \<lparr> Xcoord = 3, Ycoord = -2 \<rparr>"

value "aPoint"

value "distance aPoint otherPoint" 

lemma "distance aPoint otherPoint = 4"
by simp

end
