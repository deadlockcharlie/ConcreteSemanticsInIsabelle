theory ProgrammingAndProving
  imports Main
begin
datatype bool = True | False

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"



datatype nat = zero | Succ nat
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add zero  n =  n" |
"add (Succ m) n = Succ (add m n)"

lemma add_02: "add m zero = m"
  apply (induction m)
  apply (auto)
  done

thm add_02

datatype 'a list = Nil | Cons 'a "'a list"

fun app:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys"|
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev:: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil"|
"rev (Cons x xs) = app (rev xs) ( Cons x Nil)"



value "rev (Cons True (Cons False Nil))"

value "app (Cons x (Cons y Nil)) (Cons z (Cons a Nil))"




lemma app_assoc [simp]: "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs) 
  apply (auto)
  done

lemma app_nil [simp]: "app xs Nil = xs"
  apply( induction xs)
   apply auto
  done

lemma rev_app [simp]: "rev (app xs ys) = app (rev ys) (rev xs)"
  apply(induction xs)
   apply(auto)
  done

theorem rev_rev [simp] : "rev (rev xs) = xs"
  apply (induction xs)
   apply(auto)
  done

theorem add_assoc [simp]: "add a (add b c) =  add (add a b) c"
  apply(induction a)
   apply (auto)
  done


fun double:: " nat \<Rightarrow> nat" where
"double zero = zero"|
"double (Succ n) = Succ (Succ (double n))"

lemma add_Successor [simp] : "Succ (add n m) = add n (Succ m)"
  apply(induction n)
   apply(auto)
  done


theorem doubleIsAddTwice [simp] : "double n = add n n"
  apply (induction n)
   apply (auto)
  done


fun count:: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count x Nil = zero"|
"count x (Cons y xs) = (if x=y then Succ(count x xs) else count x xs)"

end
