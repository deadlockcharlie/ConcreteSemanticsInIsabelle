theory TypesAndFunctions
  imports Main
begin

value "1 + (2::nat)"
value "1 + (2::int )"
value "1 - (2::nat )" 
value "1 - (2::int )"

fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x [] = 0"|
"count x ( y # xs) = (if x=y then 1+(count x xs) else count x xs)"

theorem countSmallerThanLength [simp] :"count x xs \<le> length xs"
  apply(induction xs)
   apply(simp)
   apply(auto)
  done


datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: " 'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip"|
"mirror (Node l a r) = Node (mirror r) a (mirror l)"



fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []"|
"contents (Node l a r) = [a] @ (contents l) @ (contents r)"

fun sum_tree ::  "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0"|
"sum_tree (Node l a r) = a + sum_tree l + sum_tree r"

definition test_tree :: "nat tree" where
  "test_tree = Node (Node Tip 2 Tip) 1 (Node Tip 3 Tip)"

value "contents test_tree" 
value "sum_tree test_tree"

theorem sum2ways : "sum_tree t = sum_list(contents t)"
  apply(induction t)
   apply (simp)
  apply(auto)
  done


fun preorder :: "'a tree \<Rightarrow> 'a list" where
"preorder Tip = []"|
"preorder (Node l a r) =  [a ]@ (preorder l)@ (preorder r)"


fun postorder :: "'a tree \<Rightarrow> 'a list" where
"postorder Tip = []"|
"postorder (Node l a r) = (postorder l)@ (postorder r) @ [a]"


theorem preorderIsReversePostorder: "preorder (mirror x) = rev (postorder x)"
  apply(induction x)
   apply(auto)
  done


fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"itrev [] ys = ys "|
"itrev (x#xs) ys = itrev xs (x#ys)"

lemma "itrev xs ys = rev xs@ys"
(*With just the induction on xs, the induction hypothesis is too weak. The induction hypothesis is on itrev xs ys while the induction occurs on itrev xs (a#ys)
  So, we need to generalise ys to assume this. It can be done using arbitrary:ys. This quantifies the induction step universally over ys. Finally, the proof with auto succeeds.
*)
  apply (induction xs arbitrary:ys)
   apply (auto)
  done
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0  n =  n" |
"add (Suc m) n = Suc (add m n)"

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n"|
"itadd (Suc x) y = Suc (itadd x y)"

value "itadd 6 6"
value "add 6 6"

lemma "itadd m n = add m n"
  apply(induction m)
  apply(auto)
  done

end
