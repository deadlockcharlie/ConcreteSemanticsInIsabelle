theory simplification
  imports Main
begin

datatype tree0 = Tip | Node " tree0"  "tree0"

definition test_tree :: "tree0" where
  "test_tree = Tip"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) =  1+ (nodes l) + (nodes r)"

value "nodes test_tree"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
 "explode 0 t = t" |
 "explode (Suc n) t = explode n (Node t t )"


(* When we do an induction on n, we say "if the lemma holds for n, assuming everything else remains fixed". Sometimes this is too weak a hypothesis
When do you need arbitrary: t?

Use arbitrary: t when:

    You're doing induction on a variable (n)\<dots>

    But another variable (t) is used in the recursive calls, or may need to vary in the induction step\<dots>

    And you want to apply the induction hypothesis to different t values (not just the one fixed when you started the proof).

In such cases, arbitrary: t tells Isabelle:

    “Please generalize the lemma to: for all t, it holds.”

This gives you an induction hypothesis that's universally quantified over t, so you can instantiate it however needed in the inductive case.


*)
lemma "(nodes (explode n t)) = ((2^n)-1)+ ((2^n)* (nodes t))"
  apply(induction n  arbitrary:t)
  apply(simp)
   apply (simp add: algebra_simps)
  done


end