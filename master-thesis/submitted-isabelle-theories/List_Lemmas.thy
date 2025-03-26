section \<open>Appendix\<close>
subsection \<open>List Lemmas\<close>

theory List_Lemmas
  imports Main
begin

text\<open>In this theory some simple equalities about lists are established.\<close>

lemma len_those:
  assumes "those l \<noteq> None"
  shows "length (the (those l)) = length l" 
using assms proof(induct l)
  case Nil
  then show ?case by simp 
next
  case (Cons a l)
  hence "\<exists>x. a = Some x" using those.simps
    using option.collapse by fastforce 
  then obtain x where "a=Some x" by auto
  hence AL: "those (a#l) = map_option (Cons x) (those l)" using those.simps by auto
  hence "those l \<noteq> None" using assms Cons.prems by auto 
  hence "length (the (those l)) = length l" using Cons by simp
  then show ?case using AL \<open>those l \<noteq> None\<close> by (simp add: option.map_sel)
qed

lemma the_those_n:
  assumes "those (l:: 'a option list) \<noteq> None" and "(n::nat) < length l"
  shows "(the (those l)) ! n = the (l ! n)" 
  using assms proof (induct l arbitrary: n)
  case Nil
  then show ?case by simp 
next
  case (Cons a l)
  from assms(1) have l_notNone: "those l \<noteq> None" using those.simps(2)
    by (metis (no_types, lifting) Cons.prems(1) option.collapse option.map_disc_iff option.simps(4) option.simps(5)) 
  from assms(1) have "\<exists>b. a=Some b" using those.simps
    using Cons.prems(1) not_None_eq by fastforce
  from this obtain b where "a=Some b" by auto 
  hence those_al: "those (a#l) = (Some (b# (the (those l))))" using those.simps l_notNone by simp
  then show ?case proof(cases "n=0")
    case True    
    have "the (those (a # l)) ! n = the (Some (b# (the (those l)))) ! n" using those_al nth_def by simp
    also have "... = b" using True by simp
    also have "... = the ((a # l) ! n)" using \<open>a=Some b\<close> True by simp 
    finally show ?thesis .
  next
    case False
    hence "\<exists>m. n= Suc m" using old.nat.exhaust by auto 
    from this obtain m where "n = Suc m" by auto
    hence "m < length l" using assms(2) Cons.prems(2) by auto
    hence "the (those l) ! m = the (l ! m)" using Cons l_notNone by simp
    hence A: "the (those l) ! m = the ((a#l) ! n)" using \<open>n = Suc m\<close> by auto 
    have "the (those l) ! m = the (those (a # l)) ! n" using \<open>n = Suc m\<close> those.simps(2) those_al nth_def
      by simp
    then show ?thesis using A by simp
  qed
qed 

lemma those_all_Some:
  assumes "those l \<noteq> None" and "n < length l"
  shows "(l ! n)\<noteq>None" 
  using assms proof(induct l arbitrary:n)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  from assms(1) have l_notNone: "those l \<noteq> None" using those.simps(2)
    by (metis (no_types, lifting) Cons.prems(1) option.collapse option.map_disc_iff option.simps(4) option.simps(5))
  from assms(1) have "\<exists>b. a=Some b" using those.simps
    using Cons.prems(1) not_None_eq by fastforce
  from this obtain b where "a=Some b" by auto 
   then show ?case proof(cases "n=0")
     case True
     then show ?thesis using \<open>a=Some b\<close> by fastforce 
   next
     case False
     hence "\<exists>m. n= Suc m" using old.nat.exhaust by auto 
     from this obtain m where "n = Suc m" by auto
     hence "m < length l" using assms(2) Cons.prems(2) by auto
     hence "l ! m \<noteq> None" using Cons l_notNone by simp
     then show ?thesis using \<open>n = Suc m\<close> by simp
   qed
qed

lemma nth_map_enumerate: 
  shows "n < length xs \<Longrightarrow> (map f (List.enumerate 0 xs))!n = f((List.enumerate 0 xs)!n)"
proof (induct xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case using less_Suc_eq_0_disj
    by (metis length_enumerate nth_map) 
qed

lemma those_map_not_None: 
  assumes "\<forall>n< length xs. f (xs ! n) \<noteq> None" 
  shows "those (map f xs) \<noteq> None"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  hence " f ((a # xs) ! 0) \<noteq> None" using Cons(2) by auto 
  hence "\<exists>b. f a = Some b" by auto
  from this obtain b where "f a = Some b" by auto
  have "those (map f xs) \<noteq> None" using Cons(1) assms those.simps
    by (smt (verit) Cons.prems Ex_less_Suc length_Cons less_trans_Suc nth_Cons_Suc)  
  then show ?case using those.simps \<open>f a = Some b\<close>
    by (simp add: option.simps(5))
qed

lemma last_len:
  assumes "length xs = Suc n"
  shows "last xs = xs ! n"
  using assms proof(induct xs arbitrary: n)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  show ?case proof(cases "xs = Nil")
    case True
    then show ?thesis
      using Cons.prems by auto
  next
    case False
    hence "\<exists>m. n = Suc m" using Cons
      using not0_implies_Suc by auto 
    from this obtain m where "n = Suc m" by auto
    hence "length xs = Suc m" using Cons by simp
    have "last (a#xs) = last xs"
      using False by simp
    also have "... = xs ! m" using Cons \<open>length xs = Suc m\<close> by simp
    also have "... = (a#xs) ! (Suc m)" by simp
    finally show ?thesis using \<open>n = Suc m\<close> by simp
  qed
qed

end