section \<open>Bisping's Updates\<close>

theory Update
  imports Energy_Order "HOL-Algebra.Galois_Connection"
begin

text \<open>
In this theory we define Bisping's updates and their application. Further, we introduce Bisping's ``inversion''
of updates and relate the two. 
\<close>

subsection \<open>Bisping's Updates\<close>

text \<open>
Bisping allows three ways of updating a component of an energy: \<open>zero\<close> does not change the respective entry, 
\<open>minus_one\<close> subtracts one and \<open>min_set\<close> $A$ for some set $A$ replaces the entry by the 
minimum of entries whose index is contained in $A$. 
Updates are vectors where each entry contains the information, how the update changes the respective 
component of energies. We now introduce a datatype such that updates can be represented as lists of \<open>update_component\<close>s.
\<close>

datatype update_component = zero | minus_one | min_set "nat set"
type_synonym update = "update_component list" 

abbreviation "valid_update u \<equiv> (\<forall>i D. u ! i = min_set D 
                                    \<longrightarrow> i \<in> D \<and> D \<subseteq> {x. x < length u})"

text \<open>Now the application of updates \<open>apply_update\<close> will be defined.\<close>

fun apply_component::"nat \<Rightarrow> update_component \<Rightarrow> energy \<Rightarrow> enat option" where
  "apply_component i zero e = Some (e ! i)" |
  "apply_component i minus_one e = (if ((e ! i) > 0) then Some ((e ! i) - 1) 
                                    else None)" |
  "apply_component i (min_set A) e = Some (min_list (nths e A))"

fun apply_update:: "update \<Rightarrow> energy \<Rightarrow> energy option"  where 
  "apply_update u e = (if (length u = length e) 
          then (those (map (\<lambda>i. apply_component i (u ! i) e) [0..<length e])) 
          else  None)"

abbreviation "upd u e \<equiv> the (apply_update u e)"

text \<open>We now observe some properties of updates and their application. 
In particular, the application of an update preserves the dimension and the domain of an update is upward closed.
\<close>

lemma len_appl: 
  assumes "apply_update u e \<noteq> None"
  shows "length (upd u e) = length e"
proof -  
  from assms have "apply_update u e = those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])" by auto
  thus ?thesis using assms len_those
    using length_map length_upt by force 
qed

lemma apply_to_comp_n:
  assumes "apply_update u e \<noteq> None" and "i < length e"
  shows  "(upd u e) ! i = the (apply_component i (u ! i) e)" 
proof- 
  have "(the (apply_update u e)) ! i =(the (those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])))!i" using apply_update.simps
    using assms by auto 
  also have "... = the ((map (\<lambda>n. apply_component n (u ! n) e) [0..<length e])! i)" using the_those_n
    by (metis (no_types, lifting) apply_update.simps assms(1) assms(2) calculation length_map map_nth)
  also have "... = the ( apply_component i (u ! i) e)" using nth_map
    by (simp add: assms(2) calculation linordered_semidom_class.add_diff_inverse not_less_zero nth_map_upt)
  finally show ?thesis.
qed

lemma upd_domain_upward_closed:
  assumes "apply_update u e \<noteq> None" and "e e\<le> e'" 
  shows "apply_update u e' \<noteq> None"
proof
  assume "apply_update u e' = None"
  from assms have "length u = length e'" unfolding apply_update.simps energy_leq_def by metis 
  hence A: "apply_update u e' = those (map (\<lambda>n. apply_component n (u ! n) e') [0..<length e'])" using apply_update.simps by simp
  hence "those (map (\<lambda>n. apply_component n (u ! n) e') [0..<length e']) = None" using \<open>apply_update u e' = None\<close> by simp
  hence "\<not> (\<forall>n < length e'. (\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) \<noteq> None)" using those_map_not_None
    by (metis (no_types, lifting) length_map map_nth)
  hence "\<exists>n< length e'. (\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) = None" by auto
  from this obtain n where "n< length e'" and "(\<lambda>n. apply_component n (u ! n) e') ([0..<length e'] ! n) = None" by auto
  hence "apply_component n (u ! n) e' = None" by simp
  hence "u ! n = minus_one" using apply_component.elims by blast
  hence  " e' ! n = 0" using \<open>apply_component n (u ! n) e' = None\<close> apply_component.elims
    by (metis not_gr_zero option.distinct(1)) 
  hence "e ! n = 0" using assms(2) energy_leq_def \<open>n < length e'\<close> by auto 
  hence "(\<lambda>n. apply_component n (u ! n) e) ([0..<length e] ! n) = None" using \<open>u ! n = minus_one\<close> apply_component.simps(2)
    using \<open>n < length e'\<close> assms(2) energy_leq_def by auto
  hence "those (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) = None" using those.simps option.map_sel  \<open>n < length e'\<close>
    by (smt (verit, ccfv_SIG) \<open>length u = length e'\<close> apply_update.simps assms(1) length_map map_nth nth_map those_all_Some)
  hence "apply_update u e = None" by simp 
  thus "False" using assms(1) by simp
qed

text \<open>Now we show that all valid updates are declining and monotonic. The proofs follow directly 
from the definition of \<open>apply_update\<close> and \<open>valid_update\<close>.\<close> 

lemma updates_declining: 
  assumes "(apply_update u e) \<noteq> None" and  "valid_update u" 
  shows "(upd u e) e\<le> e"
  unfolding energy_leq_def proof
  show "length (the (apply_update u e)) = length e" using assms(1) len_appl by simp
  show "\<forall>n<length (the (apply_update u e)). the (apply_update u e) ! n \<le> e ! n "
  proof 
    fix n 
    show "n < length (the (apply_update u e)) \<longrightarrow> the (apply_update u e) ! n \<le> e ! n" 
    proof 
      assume "n<length (the (apply_update u e))"
      hence A: "the (apply_update u e) ! n =  the (apply_component n (u ! n) e)" using apply_to_comp_n assms(1) len_appl by auto
      consider (zero) "u ! n = zero" | (minus_one) "u ! n = minus_one" | (min) "\<exists>A. u !n = min_set A" 
        using update_component.exhaust by auto 
      hence "the (apply_component n (u ! n) e) \<le> e! n" 
        proof(cases)
          case zero
          then show ?thesis using apply_component.simps
            by (simp add: A linorder_le_less_linear option.sel) 
        next
          case minus_one
          have "(e ! n) - 1 \<le> e ! n"
            by (metis eSuc_minus_1 i0_lb idiff_0 ile_eSuc iless_eSuc0 less_eqE one_eSuc plus_1_eSuc(1) verit_comp_simplify1(3)) 
          from minus_one have "the (apply_component n (u ! n) e) = (e ! n) - 1" using apply_component.simps assms(1) those_all_Some apply_update.simps
            by (smt (z3) \<open>length (the (apply_update u e)) = length e\<close> \<open>n < length (the (apply_update u e))\<close> length_map map_nth nth_map option.sel) 
          then show ?thesis using \<open>(e ! n) - 1 \<le> e ! n\<close> by simp
        next
          case min
          from this obtain A where "u ! n = min_set A " by auto
          hence "n\<in> A \<and> A \<subseteq> {x. x < length e}" using assms(2)
            by (metis apply_update.elims assms(1))
          hence "e!n \<in> set (nths e A)" using set_nths
            using mem_Collect_eq subsetD by fastforce 
          hence "Min (set (nths e A)) \<le> e !n" using Min_le
            by (simp add: List.finite_set)
          hence "min_list (nths e A) \<le> e ! n"
            by (metis \<open>e ! n \<in> set (nths e A)\<close> in_set_member member_rec(2) min_list_Min) 
          then show ?thesis using apply_component.simps by (simp add: \<open>u ! n = min_set A\<close>)
        qed    
      thus "the (apply_update u e) ! n \<le> e ! n" using A by simp
    qed
  qed
qed

lemma updates_monotonic:
  assumes "apply_update u e \<noteq> None" and "e e\<le> e'" and "valid_update u"
  shows "(upd u e) e\<le> (upd u e')" 
  unfolding energy_leq_def proof
  have "apply_update u e' \<noteq> None" using assms upd_domain_upward_closed by auto
  thus "length (the (apply_update u e)) = length (the (apply_update u e'))" using assms len_appl
    by (metis energy_leq_def)
  show "\<forall>n<length (the (apply_update u e)). the (apply_update u e) ! n \<le> the (apply_update u e') ! n " 
  proof 
    fix n 
    show "n < length (the (apply_update u e)) \<longrightarrow> the (apply_update u e) ! n \<le> the (apply_update u e') ! n"
    proof 
      assume "n < length (the (apply_update u e))"
      hence "n < length e" using len_appl assms(1)
        by simp
      hence " e ! n \<le> e' !n " using assms energy_leq_def
        by simp
      consider (zero) "(u ! n) = zero" | (minus_one) "(u ! n) = minus_one" | (min_set) "(\<exists>A. (u ! n) = min_set A)"
        using update_component.exhaust by auto 
      thus "the (apply_update u e) ! n \<le> the (apply_update u e') ! n" 
      proof (cases)
        case zero
        then show ?thesis using apply_update.simps apply_component.simps assms \<open>e ! n \<le> e' !n\<close> \<open>apply_update u e' \<noteq> None\<close>
          by (metis \<open>n < length (the (apply_update u e))\<close> apply_to_comp_n len_appl option.sel)
      next
        case minus_one
        hence "the (apply_update u e) ! n = the (apply_component n (u ! n) e)" using apply_to_comp_n assms(1)
          by (simp add: \<open>n < length e\<close>)

        from assms(1) have A: "(map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) ! n \<noteq> None" using  \<open>n < length e\<close> those_all_Some apply_update.simps
          by (metis (no_types, lifting) length_map map_nth) 
        hence "(apply_component n (u ! n) e) = (map (\<lambda>n. apply_component n (u ! n) e) [0..<length e]) ! n " using \<open>n < length e\<close>
          by simp
        hence "(apply_component n (u ! n) e) \<noteq> None" using A by simp
        hence "e ! n >0 " using minus_one apply_component.elims by auto 
        hence  "(e ! n) -1 \<le> (e' ! n) -1" using \<open>e ! n \<le> e' ! n\<close> by (metis eSuc_minus_1 iadd_Suc ileI1 le_iff_add)

        from \<open>e ! n >0\<close> have "e' ! n > 0" using assms(2) energy_leq_def
          using \<open>e ! n \<le> e' ! n\<close> by auto 
        have A: "the (apply_update u e') ! n = the (apply_component n (u ! n) e')" using apply_to_comp_n \<open>apply_update u e' \<noteq> None\<close>
          using \<open>n < length e\<close> assms(2) energy_leq_def by auto 
        have "the (apply_component n (u ! n) e' )= (e' ! n) -1" using minus_one \<open>e' ! n >0\<close>
          by simp
        hence "the (apply_update u e') ! n  = (e' ! n) -1" using A by simp
        then show ?thesis using \<open>(e ! n) -1 \<le> (e' ! n) -1\<close>
          using \<open>0 < e ! n\<close> \<open>the (apply_update u e) ! n = the (apply_component n (u ! n) e)\<close> minus_one by auto
      next
        case min_set
        from this obtain A where "u ! n = min_set A" by auto
        hence " A \<subseteq> {x. x < length e}" using assms(3)  by (metis apply_update.elims assms(1))
        hence "\<forall>a \<in> A. e!a \<le> e'!a" using assms(2) energy_leq_def
          by blast
        have "\<forall>a\<in> A. (Min (set (nths e A))) \<le> e! a" proof
          fix a
          assume "a \<in> A"
          hence "e!a \<in> set (nths e A)" using set_nths nths_def
            using \<open>A \<subseteq> {x. x < length e}\<close> in_mono by fastforce
          thus "Min (set (nths e A)) \<le> e ! a " using Min_le by simp
        qed
        hence "\<forall>a\<in> A. (Min (set (nths e A))) \<le> e'! a" using \<open>\<forall>a \<in> A. e!a \<le> e'!a\<close>
          using dual_order.trans by blast 
        hence "\<forall>x \<in> (set (nths e' A)). (Min (set (nths e A))) \<le> x" using set_nths
          by (smt (verit) mem_Collect_eq)        

        from assms(2) have "A\<noteq>{}"
          using \<open>u ! n = min_set A\<close> assms(3) by auto 
        hence "set (nths e' A) \<noteq> {}" using set_nths \<open>A \<subseteq> {x. x < length e}\<close>
          using Collect_empty_eq \<open>n < length e\<close> \<open>u ! n = min_set A\<close> assms(2) assms(3) energy_leq_def by fastforce
        hence "(nths e' A) \<noteq> []" by simp
        from \<open>A\<noteq>{}\<close> have"set (nths e A) \<noteq> {}" using set_nths \<open>A \<subseteq> {x. x < length e}\<close> Collect_empty_eq \<open>n < length e\<close> \<open>u ! n = min_set A\<close>
          by (smt (verit) assms(3)) 
        hence "(nths e A) \<noteq> []" by simp
        hence "(min_list (nths e A)) = Min (set (nths e A))" using min_list_Min by auto
        also have "... \<le> Min (set (nths e' A))"        
          using \<open>\<forall>x \<in> (set (nths e' A)). (Min (set (nths e A))) \<le> x\<close>
          by (simp add: \<open>nths e' A \<noteq> []\<close>) 
        finally have "(min_list (nths e A)) \<le> min_list (nths e' A)" using min_list_Min \<open>(nths e' A) \<noteq> []\<close> by metis
        then show ?thesis using apply_to_comp_n assms(1) \<open>apply_update u e' \<noteq> None\<close> apply_component.simps(3) \<open>u ! n = min_set A\<close>
          by (metis \<open>length (the (apply_update u e)) = length (the (apply_update u e'))\<close> \<open>n < length e\<close> len_appl option.sel)
      qed
    qed
  qed
qed

subsection \<open>Bisping's Inversion\<close>

text\<open>The ``inverse'' of an update $u$ is a function mapping energies $e$ to $\min \lbrace e' \ | \ e \leq u(e') \rbrace$ 
w.r.t\ the component-wise order.
We start by giving a calculation and later show that we indeed calculate such minima.  
For an energy $e = (e_0, ..., e_{n-1})$ we calculate this component-wise such that the $i$-th 
component is the maximum of $e_i$ (plus one if applicable) 
and each entry $e_j$ where $i \in u_j \subseteq \lbrace 0, ..., n-1 \rbrace $.
\<close>

fun apply_inv_component::"nat \<Rightarrow> update \<Rightarrow> energy \<Rightarrow> enat" where
  "apply_inv_component i u e = Max (set (map (\<lambda>(j,up). 
          (case up of zero \<Rightarrow> e ! i | 
                minus_one \<Rightarrow> (if i=j then (e ! i)+1 else e ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! j) else 0))) 
          (List.enumerate 0 u)))" 

fun apply_inv_update:: "update \<Rightarrow> energy \<Rightarrow> energy option" where 
  "apply_inv_update u e = (if (length u = length e) 
                    then Some (map (\<lambda>i. apply_inv_component i u e) [0..<length e])
                    else None)" 

abbreviation "inv_upd u e \<equiv> the (apply_inv_update u e)"

text \<open>We now observe the following properties, if an update $u$ and an energy $e$ have the same dimension:
\begin{itemize}
  \item \<open>apply_inv_update\<close> preserves dimension.
  \item The domain of \<open>apply_inv_update u\<close> is $\lbrace \<open>e\<close> \ | \ |\<open>e\<close>| = |\<open>u\<close>| \rbrace$.
  \item \<open>apply_inv_update u e\<close>  is in the domain of the update \<open>u\<close>.
\end{itemize}
The first two proofs follow directly from the definition of \<open>apply_inv_update\<close>, while the proof
of \<open>inv_not_none_then\<close> is done by a case analysis of the possible \<open>update_component\<close>s. \<close>

lemma len_inv_appl: 
  assumes "length u = length e"
  shows "length (inv_upd u e) = length e"
  using assms apply_inv_update.simps length_map option.sel by auto

lemma inv_not_none: 
  assumes "length u = length e"
  shows "apply_inv_update u e \<noteq> None" 
  using assms apply_inv_update.simps by simp  

lemma inv_not_none_then:
  assumes "apply_inv_update u e \<noteq> None"
  shows "(apply_update u (inv_upd u e)) \<noteq> None"
proof - 
  have len: "length u = length (the (apply_inv_update u e))" using assms apply_inv_update.simps len_those
    by auto 
  have "\<forall>n<length u. (apply_component n (u ! n) (the (apply_inv_update u e)))\<noteq>None" 
  proof
    fix n
    show "n < length u \<longrightarrow> apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None " 
    proof 
      assume "n<length u"
      consider (zero) "(u ! n) = zero" | (minus_one) "(u ! n) = minus_one" | (min_set) "(\<exists>A. (u ! n) = min_set A)"
        using update_component.exhaust by auto 
      then show "apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None" 
      proof(cases)
        case zero
        then show ?thesis by simp 
      next
        case minus_one
        have nth: "(the (apply_inv_update u e)) ! n = apply_inv_component n u e" using apply_inv_update.simps
          by (metis (no_types, lifting) \<open>n < length u\<close> add_0 assms len length_map nth_map nth_upt option.sel)

        have n_minus_one: "List.enumerate 0 u ! n = (n,minus_one) " using minus_one
          by (simp add: \<open>n < length u\<close> nth_enumerate_eq) 
        have "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)))(n,minus_one) = (e ! n) +1"
          by simp
        hence "(e ! n) +1 \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0)))(List.enumerate 0 u))" using n_minus_one
          by (metis (no_types, lifting) \<open>n < length u\<close> in_set_conv_nth length_enumerate length_map nth_map)
        hence "(nth e n)+1 \<le> apply_inv_component n u e" using minus_one nth apply_inv_component.simps Max_ge
          by simp
        hence "(nth (the (apply_inv_update u e)) n >0)" using nth by fastforce
        then show ?thesis by (simp add: minus_one) 
      next
        case min_set
        then show ?thesis by auto 
      qed
    qed
  qed
  hence "\<forall>n<length (the (apply_inv_update u e)). apply_component n (u ! n) (the (apply_inv_update u e)) \<noteq> None" 
    using len by presburger 
  hence "those (map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) \<noteq> None" 
    using those_map_not_None
    by (smt (verit) add_less_cancel_left gen_length_def length_code length_map map_nth nth_upt) 
  thus ?thesis using apply_update.simps len by presburger
qed

text \<open>Now we show that \<open>apply_inv_update u\<close> is monotonic for all updates \<open>u\<close>. The proof follows directly 
from the definition of \<open>apply_inv_update\<close> and a case analysis of the possible update components.\<close>

lemma inverse_monotonic:
  assumes "e e\<le> e'" and "length u = length e'"
  shows "(inv_upd u e) e\<le> (inv_upd u e')"
  unfolding energy_leq_def proof
  show "length (the (apply_inv_update u e)) = length (the (apply_inv_update u e'))" using assms len_inv_appl energy_leq_def
    by simp 
  show "\<forall>i<length (the (apply_inv_update u e)). the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i " 
  proof
    fix i
    show "i < length (the (apply_inv_update u e)) \<longrightarrow> the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i "
    proof 
      assume "i < length (the (apply_inv_update u e))"
      have "the (apply_inv_update u e) ! i = (map (\<lambda>i. apply_inv_component i u e) [0..<length e]) ! i" 
        using apply_inv_update.simps assms
        using energy_leq_def by auto
      also have "... =  (\<lambda>i. apply_inv_component i u e) ([0..<length e] ! i)" using nth_map
        by (metis (full_types) \<open>i < length (the (apply_inv_update u e))\<close> add_less_mono assms(1) assms(2) energy_leq_def diff_add_inverse gen_length_def len_inv_appl length_code less_add_same_cancel2 not_less_less_Suc_eq nth_map_upt nth_upt plus_1_eq_Suc)
      also have "... = apply_inv_component i u e"
        using \<open>i < length (the (apply_inv_update u e))\<close> assms(1) assms(2) energy_leq_def by auto 
      finally have E: "the (apply_inv_update u e) ! i =
                Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e ! i | 
                minus_one \<Rightarrow> (if i=m then (e ! i)+1 else e ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
        by presburger 


      have "the (apply_inv_update u e') ! i = (map (\<lambda>i. apply_inv_component i u e') [0..<length e']) ! i" 
        using apply_inv_update.simps assms
        using energy_leq_def by auto
      also have "... =  (\<lambda>i. apply_inv_component i u e') ([0..<length e'] ! i)" using nth_map
        by (metis (full_types) \<open>i < length (the (apply_inv_update u e))\<close> add_less_mono assms(1) assms(2) energy_leq_def diff_add_inverse gen_length_def len_inv_appl length_code less_add_same_cancel2 not_less_less_Suc_eq nth_map_upt nth_upt plus_1_eq_Suc)
      also have "... = apply_inv_component i u e'"
        using \<open>i < length (the (apply_inv_update u e))\<close> assms(1) assms(2) energy_leq_def by auto 
      finally have E': "the (apply_inv_update u e') ! i =
                Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
        by presburger 

      have fin': "finite (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u)))" by simp
      have fin: "finite (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u)))" by simp

      have "\<And>x. x \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e ! i | 
                minus_one \<Rightarrow> (if i=m then (e ! i)+1 else e ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e ! m) else 0))) (List.enumerate 0 u))) \<Longrightarrow> (\<exists>y. x\<le> y \<and> y\<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u))))"
      proof-
        fix x
        assume "x \<in> set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u))" 
        hence "\<exists>j < length u. x = (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u)) ! j" using in_set_conv_nth
          by (metis (no_types, lifting) length_enumerate length_map)
        from this obtain j where "j < length u" and X: "x = (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u)) ! j" by auto
        hence "(List.enumerate 0 u) ! j = (j, (u !j))"
          by (simp add: nth_enumerate_eq) 
        hence X: "x=(case (u !j) of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = j then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! j else 0)" using X
          by (simp add: \<open>j < length u\<close>) 

        consider (zero) "(u !j) = zero" | (minus_one) "(u !j) = minus_one" | (min_set) "\<exists> A. (u !j) = min_set A"
          by (meson update_component.exhaust)

        thus "(\<exists>y. x\<le> y \<and> y\<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u))))" 
        proof(cases)
          case zero
          hence "x= e!i" using X by simp
          also have "...\<le> e'!i" using assms
            using \<open>i < length (the (apply_inv_update u e))\<close> energy_leq_def by auto 
          also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)(j, (u ! j))"
            by (simp add: zero)
          finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto 
        next
          case minus_one
          hence X: "x = (if i=j then (e ! i)+1 else e ! i)" using X by simp
          then show ?thesis proof(cases "i=j")
            case True
            hence "x = (e ! i) +1" using X by simp
            also have "...\<le> (e' ! i) +1" using assms
              using True \<open>j < length u\<close> energy_leq_def by auto
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)(j, (u ! j))"
            by (simp add: minus_one True)
             finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto
          next
            case False
            hence "x = (e ! i) " using X by simp
            also have "...\<le> (e' ! i)" using assms
              using False \<open>j < length u\<close> energy_leq_def
              by (metis \<open>i < length (the (apply_inv_update u e))\<close> len_inv_appl) 
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)(j, (u ! j))"
            by (simp add: minus_one False)
             finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)
                     (List.enumerate 0 u))!j"
            by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
          then show ?thesis
            using \<open>j < length u\<close> by auto
          qed
        next
          case min_set
          from this obtain A where A: "u ! j = min_set A " by auto
          hence X: "x = (if i \<in> A then e ! j else 0)" using X by auto
          then show ?thesis proof(cases "i \<in> A")
            case True
            hence "x=e ! j" using X by simp
            also have "...\<le> e'!j" using assms
              using \<open>j < length u\<close> energy_leq_def by auto
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)(j, (u ! j))"
              by (simp add: A True)
            finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)
                     (List.enumerate 0 u))!j"
              by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
            then show ?thesis
              using \<open>j < length u\<close> by auto
          next
            case False
            hence "x=0" using X by simp
            also have "... = (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)(j, (u ! j))"
              by (simp add: A False)
            finally have "x \<le> (map (\<lambda>(m, up).
                            case up of zero \<Rightarrow> e' ! i | minus_one \<Rightarrow> if i = m then e' ! i + 1 else e' ! i
                            | min_set A \<Rightarrow> if i \<in> A then e' ! m else 0)
                     (List.enumerate 0 u))!j"
              by (simp add: \<open>List.enumerate 0 u ! j = (j, u ! j)\<close> \<open>j < length u\<close>)
            then show ?thesis
              using \<open>j < length u\<close> by auto
          qed
        qed
      qed

      hence "\<forall>x\<in> (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u))). 
            x\<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u)))"
        using fin'
        by (meson Max.coboundedI dual_order.trans) 
      hence "Max (set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> e ! i | minus_one \<Rightarrow> if i = m then e ! i + 1 else e ! i
                          | min_set A \<Rightarrow> if i \<in> A then e ! m else 0)
                   (List.enumerate 0 u)))
            \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> e' ! i | 
                minus_one \<Rightarrow> (if i=m then (e' ! i)+1 else e' ! i) |
                min_set A \<Rightarrow> (if i\<in>A then (e' ! m) else 0))) (List.enumerate 0 u)))"
        using fin assms Max_less_iff
        by (metis (no_types, lifting) Max_in \<open>i < length (the (apply_inv_update u e))\<close> \<open>length (the (apply_inv_update u e)) = length (the (apply_inv_update u e'))\<close> ex_in_conv len_inv_appl length_enumerate length_map nth_mem)

      thus "the (apply_inv_update u e) ! i \<le> the (apply_inv_update u e') ! i " using E E'
        by presburger 
    qed
  qed
qed

subsection \<open>Relating Updates and ``Inverse'' Updates\<close>

text \<open>
Since the minimum is not an injective function, for many updates there does not exist an inverse. The 
following $2$-dimensional examples show, that the function \<open>apply_inv_update\<close> does not map an update to its inverse.
\<close>

lemma not_right_inverse_example:
  shows "apply_update [minus_one, (min_set {0,1})] [1,2] = Some [0,1]"
        "apply_inv_update [minus_one, (min_set {0,1})] [0,1] = Some [1,1]"  
  by (auto simp add: nths_def)

lemma not_right_inverse:
  shows "\<exists>u. \<exists>e. apply_inv_update u (upd u e) \<noteq> Some e" 
  using not_right_inverse_example by force

lemma not_left_inverse_example:
  shows "apply_inv_update [zero, (min_set {0,1})] [0,1] = Some [1,1]"  
        "apply_update [zero, (min_set {0,1})] [1,1] = Some [1,1]"
  by (auto simp add: nths_def)

lemma not_left_inverse: 
  shows "\<exists>u. \<exists>e. apply_update u (inv_upd u e) \<noteq> Some e" 
  by (metis option.sel apply_update.simps length_0_conv not_Cons_self2 option.distinct(1))

text \<open>
We now show that the given calculation \<open>apply_inv_update\<close> indeed calculates $e \mapsto  \min \lbrace e' \ | \ e \leq u(e') \rbrace$
for all valid updates $u$.
For this we first name this set \<open>possible_inv u e\<close>. Then we show that \<open>inv_upd u e\<close> is an element 
of that set before showing that it is minimal. 
Considering one component at a time, the proofs follow by a case analysis of the possible 
update components from the definition of \<open>apply_inv_update\<close>
\<close>

abbreviation "possible_inv u e \<equiv> {e'. apply_update u e' \<noteq> None 
                                        \<and> (e e\<le> (upd u e'))}"

lemma leq_up_inv:
  assumes "length u = length e" and "valid_update u"
  shows "e e\<le> (upd u (inv_upd u e))"
  unfolding energy_leq_def proof
  from assms have notNone: "apply_update u (the (apply_inv_update u e)) \<noteq> None" using inv_not_none_then inv_not_none by blast
  thus len1: "length e = length (the (apply_update u (the (apply_inv_update u e))))" using assms len_appl len_inv_appl
    by presburger

  show "\<forall>n<length e. e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n " 
  proof
    fix n 
    show "n < length e \<longrightarrow> e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n " 
    proof
      assume "n < length e"

      have notNone_n: "(map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) ! n \<noteq> None" using notNone apply_update.simps
        by (smt (verit) \<open>n < length e\<close> assms(1) length_map map_nth nth_map option.distinct(1) those_all_Some)

      have "the (apply_update u (the (apply_inv_update u e))) ! n = the (those (map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))])) ! n" 
        using apply_update.simps assms(1) len1 notNone by presburger 
      also have " ... = the ((map (\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) [0..<length (the (apply_inv_update u e))]) ! n)" using the_those_n notNone
        by (smt (verit) \<open>n < length e\<close> apply_update.elims calculation assms(1) length_map map_nth nth_map) 
      also have "... = the ((\<lambda>n. apply_component n (u ! n) (the (apply_inv_update u e))) ([0..<length (the (apply_inv_update u e))] ! n))" using nth_map
        using \<open>n < length e\<close> assms len_inv_appl minus_nat.diff_0 nth_upt by auto
      also have " ... = the (apply_component n (u ! n) (the (apply_inv_update u e)))" using \<open>n < length e\<close> assms len_inv_appl
        by (simp add: plus_nat.add_0) 
      finally have unfolded_apply_update: "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n (u ! n) (the (apply_inv_update u e)))" .

      have "(the (apply_inv_update u e)) ! n = (the (Some (map (\<lambda>n. apply_inv_component n u e) [0..<length e])))!n " using apply_inv_update.simps assms(1) by auto
      also have "... = (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) ! n" by auto
      also have "... =  apply_inv_component n u e" using nth_map map_nth
        by (smt (verit) Suc_diff_Suc \<open>n < length e\<close> add_diff_inverse_nat diff_add_0 length_map less_diff_conv less_one nat_1 nat_one_as_int nth_upt plus_1_eq_Suc) 
      finally have unfolded_apply_inv: "(the (apply_inv_update u e)) ! n = apply_inv_component n u e". 

      consider (zero) "u ! n = zero" |(minus_one) "u ! n = minus_one" |(min_set) "\<exists>A. min_set A = u ! n"
        by (metis update_component.exhaust) 
      thus "e ! n \<le> the (apply_update u (the (apply_inv_update u e))) ! n" 
      proof (cases)
        case zero
        hence "(List.enumerate 0 u) ! n = (n, zero)"
          by (simp add: \<open>n < length e\<close> assms(1) nth_enumerate_eq) 
        hence nth_in_set: "e ! n \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))" using nth_map
          by (metis (no_types, lifting) \<open>n < length e\<close> assms(1) case_prod_conv in_set_conv_nth length_enumerate length_map update_component.simps(8)) 

        from zero have "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n zero (the (apply_inv_update u e)))" using unfolded_apply_update by auto
        also have "... = ((the (apply_inv_update u e)) ! n)" using apply_component.simps(1) by simp
        also have "... = apply_inv_component n u e" using unfolded_apply_inv by auto
        also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps by auto
        also have "... \<ge> e ! n " using nth_in_set by simp
        finally show ?thesis .
      next
        case minus_one

        hence A: "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (n,(u!n)) = (e!n) +1"
          by simp 
        have "(List.enumerate 0 u)!n = (n,(u!n))"
          using \<open>n < length e\<close> assms(1) nth_enumerate_eq
          by (metis add_0)
        hence "(e!n) +1 \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using A nth_map_enumerate
          by (metis (no_types, lifting) \<open>n < length e\<close> assms(1) length_enumerate length_map nth_mem) 
        hence leq: "(e!n) +1 \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using Max_ge by simp

        have notNone_comp: "apply_component n minus_one (the (apply_inv_update u e)) \<noteq> None" using notNone
          by (smt (z3) \<open>n < length e\<close> add_0 len1 len_appl length_map length_upt map_nth minus_one notNone_n nth_map_upt)

        from minus_one have "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n minus_one (the (apply_inv_update u e)))" using unfolded_apply_update by auto
        also have "... = ((the (apply_inv_update u e)) ! n) -1" using apply_component.simps(2) notNone_comp
          using calculation option.sel by auto 
        also have "... = apply_inv_component n u e -1" using unfolded_apply_inv by auto
        also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) -1" using apply_inv_component.simps by auto
        also have "... \<ge> e ! n" using leq 
          by (smt (verit) add.assoc add_diff_assoc_enat le_iff_add) 
        finally show ?thesis .
      next
        case min_set
        from this obtain A where "min_set A = u ! n" by auto
        hence n_in_A: "n \<in> A" using assms(2) by simp
        from \<open>min_set A = u ! n\<close> have A_in_len: "\<And>a. a \<in> A \<Longrightarrow> a < length e" using assms(2) 
          by (metis assms(1) in_mono mem_Collect_eq)

        have leq_all_A: "\<forall>a \<in> A. (map (\<lambda>n. apply_inv_component n u e) [0..<length e])! a \<ge>  e ! n" 
        proof
          fix a
          assume "a\<in> A"

          hence X: "(\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e a | 
                minus_one \<Rightarrow> (if a=m then (nth e a)+1 else nth e a) |
                min_set A \<Rightarrow> (if a\<in>A then (nth e m) else 0)))(n, (min_set A)) = e!n" by auto
          have "(List.enumerate 0 u) ! n = (n, (min_set A))" using \<open>min_set A = u ! n\<close> \<open>n < length e\<close> assms(1) nth_enumerate_eq
            by (metis add_0)
          hence "e!n \<in> (set (map (\<lambda>(m,up). (case up of
                zero \<Rightarrow> nth e a | 
                minus_one \<Rightarrow> (if a=m then (nth e a)+1 else nth e a) |
                min_set A \<Rightarrow> (if a\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using X nth_map_enumerate
            by (metis (no_types, lifting) \<open>n < length e\<close> in_set_conv_nth assms(1) length_enumerate length_map)
          hence leq: "e!n \<le> Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e a | 
                minus_one \<Rightarrow> (if a=m then (nth e a)+1 else nth e a) |
                min_set A \<Rightarrow> (if a\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using Max_ge
            by (simp add: List.finite_set finite.emptyI finite.insertI finite_UnI) 

          from \<open>a\<in> A\<close> have "map (\<lambda>n. apply_inv_component n u e) [0..<length e] ! a = apply_inv_component a u e" using nth_map A_in_len
            by (smt (z3) add_0 length_upt minus_nat.diff_0 nth_upt) 
          also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e a | 
                minus_one \<Rightarrow> (if a=m then (nth e a)+1 else nth e a) |
                min_set A \<Rightarrow> (if a\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps by simp
          finally show "e ! n \<le> map (\<lambda>n. apply_inv_component n u e) [0..<length e] ! a " using leq by presburger
        qed
        have leq: "\<forall>x \<in> (set (nths (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) A)). x \<ge> e!n" 
        proof
          fix x 
          assume "x \<in> set (nths (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) A)"
          hence "\<exists>a. (x = map (\<lambda>n. apply_inv_component n u e) [0..<length e]!a) \<and> (a < size (map (\<lambda>n. apply_inv_component n u e) [0..<length e])) \<and> (a \<in> A)" using set_nths
            by (smt (verit) mem_Collect_eq) 
          from this obtain a where " (x = map (\<lambda>n. apply_inv_component n u e) [0..<length e]!a) \<and> (a < size (map (\<lambda>n. apply_inv_component n u e) [0..<length e])) \<and> (a \<in> A)" by auto
          thus "e ! n \<le> x" using leq_all_A
            by blast 
        qed

        have len_inv_comp: "length (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) = length e"
          by (simp add: length_upt minus_nat.diff_0) 
        hence not_empty: "(map (\<lambda>n. apply_inv_component n u e) [0..<length e])! n \<in> set((nths (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) A) ) " 
          using set_nths n_in_A by (smt (verit) \<open>n < length e\<close> mem_Collect_eq)
 
        from \<open>min_set A = u ! n\<close> have "the (apply_update u (the (apply_inv_update u e))) ! n = the (apply_component n (min_set A) (the (apply_inv_update u e)))" using unfolded_apply_update by auto
        also have "... = (min_list (nths (the (apply_inv_update u e)) A))" using apply_component.simps by auto
        also have "... = (min_list (nths (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) A))" using apply_inv_update.simps assms(1) by auto
        also have "... =  Min (set (nths (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) A))" using min_list_Min not_empty
          by (metis length_pos_if_in_set less_numeral_extra(3) list.size(3))
        also have "... \<ge> e ! n " using leq Min_ge_iff not_empty
          by (metis List.finite_set empty_iff)
        finally show ?thesis .
      qed
    qed
  qed 
qed

lemma apply_inv_is_min:
  assumes "length u = length e" and "valid_update u"
  shows "energy_Min (possible_inv u e) = {inv_upd u e}"
proof
  have apply_inv_leq_possible_inv: "\<forall>e'\<in>(possible_inv u e). (inv_upd u e) e\<le> e'"
  proof 
    fix e'
    assume "e' \<in> possible_inv u e"
    hence "energy_leq e (the (apply_update u e'))" by auto
    hence B: "\<forall>n < length e. e! n \<le> (the (apply_update u e')) ! n" unfolding energy_leq_def by auto

    show "energy_leq (the (apply_inv_update u e)) e'" unfolding energy_leq_def 
    proof
      show "length (the (apply_inv_update u e)) = length e'" using assms
        by (metis (mono_tags, lifting) \<open>e' \<in> possible_inv u e\<close> energy_leq_def len_appl len_inv_appl mem_Collect_eq) 
      show "\<forall>n<length (the (apply_inv_update u e)). the (apply_inv_update u e) ! n \<le> e' ! n" 
      proof
        fix n 
        show " n < length (the (apply_inv_update u e)) \<longrightarrow> the (apply_inv_update u e) ! n \<le> e' ! n" 
        proof
          assume "n < length (the (apply_inv_update u e))"
          have "the (apply_inv_update u e) ! n = (map (\<lambda>n. apply_inv_component n u e) [0..<length e]) ! n" using apply_inv_update.simps
            by (metis assms(1) option.sel)
          also have "... = apply_inv_component n u e"
            by (metis \<open>n < length (the (apply_inv_update u e))\<close> assms(1) len_inv_appl minus_nat.diff_0 nth_map_upt plus_nat.add_0)
          also have "... =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps by auto
          finally have inv_max: "the (apply_inv_update u e) ! n = Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))".

          from B have "e ! n \<le> (the (apply_update u e')) ! n" using \<open>n < length (the (apply_inv_update u e))\<close>
            using assms(1) len_inv_appl by auto 
          hence upd_v: "e ! n \<le> the ( apply_component n (u ! n) e')" using apply_to_comp_n
            using \<open>length (the (apply_inv_update u e)) = length e'\<close> \<open>n < length (the (apply_inv_update u e))\<close> \<open>e' \<in> possible_inv u e\<close> by auto 

          have min_does_min_stuff: "\<And>m A. (u ! m) = min_set A \<Longrightarrow> n \<in> A \<Longrightarrow> (e ! m) \<le> (e' ! n) " 
          proof-
            fix m A
            assume "(u ! m) = min_set A" and "n \<in> A" 
            hence "e' ! n \<in> set (nths e' A)" using nths_def set_nths
            by (smt (verit) \<open>length (the (apply_inv_update u e)) = length e'\<close> \<open>n < length (the (apply_inv_update u e))\<close> mem_Collect_eq)
            have "(e ! m) > (e' ! n) \<Longrightarrow> False " 
            proof-
              assume "(e ! m) > (e' ! n)"
              hence "(the (apply_update u e')) ! m = the (apply_component m (u ! m) e')" using apply_to_comp_n \<open>e' \<in> possible_inv u e\<close>
                by (smt (verit) \<open>length (the (apply_inv_update u e)) = length e'\<close> \<open>u ! m = min_set A\<close> assms(1) assms(2) len_inv_appl mem_Collect_eq subsetD)
              also have "... = (min_list (nths e' A))" using \<open>(u ! m) = min_set A\<close> apply_component.simps(3)
                by simp
              also have "... = Min (set (nths e' A))" using min_list_Min \<open>e' ! n \<in> set (nths e' A)\<close>
                by (metis in_set_member member_rec(2))
              also have "... \<le>  e' ! n" using \<open>e' ! n \<in> set (nths e' A)\<close> Min_le by simp
              finally have  "(the (apply_update u e')) ! m \<le> e' ! n" .
              hence "(the (apply_update u e')) ! m < (e ! m)" using \<open>(e ! m) > (e' ! n)\<close> by auto
              thus "False" using B
                by (metis Collect_mem_eq Collect_mono_iff \<open>u ! m = min_set A\<close> assms leD) 
            qed
            thus "(e ! m) \<le> (e' ! n)"
              using verit_comp_simplify1(3) by blast
          qed

          consider (zero) "u ! n = zero" |(minus_one) "u ! n = minus_one" |(min_set) "\<exists>A. min_set A = u ! n"
            by (metis update_component.exhaust) 
          thus "the (apply_inv_update u e) ! n \<le> e' ! n " 
          proof(cases)
            case zero
            hence "the (apply_component n (u ! n) e') = e'! n" using apply_component.simps(1) by simp
            hence "e ! n \<le> e' ! n" using \<open>e ! n \<le> (the (apply_update u e')) ! n\<close> upd_v by simp
            have "0 \<le> e'!n" by simp
            have set: "(set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
            proof
              show "(set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                \<subseteq> {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
              proof 
                fix x 
                assume "x \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
                from this consider (n) "x \<in> {nth e n}" |(map) "x\<in>set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))"
                  by blast
                then show "x\<in> {nth e n} \<union> {(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
                proof(cases)
                  case n
                  then show ?thesis by simp
                next
                  case map
                  hence "\<exists>m < length (List.enumerate 0 u). x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m"
                    by (metis (no_types, lifting) in_set_conv_nth length_map) 
                  from this obtain m where M: "m < length (List.enumerate 0 u)" and "x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m" by auto
                  hence X: "x = (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (m, u !m)" using nth_map M
                    by (simp add: nth_enumerate_eq)

                  consider (zero0) "u ! m = zero" |(minus_one) "u ! m = minus_one" |(min_set) "\<exists>A. min_set A = u ! m"
                    by (metis update_component.exhaust)
                  then show ?thesis 
                  proof(cases)
                    case zero0
                    then show ?thesis using X by auto
                  next
                    case minus_one
                    then show ?thesis using X zero by auto
                  next
                    case min_set
                    from this obtain A where "min_set A = u ! m" by auto
                    then show ?thesis 
                    proof(cases "n \<in> A")
                      case True
                      hence "x= e!m" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> True by auto 
                    next
                      case False
                      hence "x= 0" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> False by auto 
                    qed
                  qed
                qed
              qed
              show "{nth e n} \<union> {(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}
                \<subseteq> set (map (\<lambda>(m, up). case up of 
                zero \<Rightarrow> e ! n | 
                minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n | 
                min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (List.enumerate 0 u))" 
              proof
                fix x 
                assume "x \<in> {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                from this consider (n) "x \<in> {nth e n}" |(min_set) "x\<in>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))}" |(zero) "x\<in> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                  by blast
                then show "x \<in> set (map (\<lambda>(m, up).
                           case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                           | min_set A \<Rightarrow> if n \<in> A then e ! m else 0)
                    (List.enumerate 0 u))" 
                proof(cases)
                  case n
                  from zero have "(List.enumerate 0 u) ! n = (n, zero)"
                    by (metis \<open>n < length (the (apply_inv_update u e))\<close> add_cancel_left_left assms(1) len_inv_appl nth_enumerate_eq)
                  hence nth_in_set: "e ! n \<in> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))" using nth_map
                    by (metis (no_types, lifting) \<open>n < length (the (apply_inv_update u e))\<close> assms(1) case_prod_conv len_inv_appl length_enumerate length_map nth_mem update_component.simps(8))
                  then show ?thesis using n by auto 
                next
                  case min_set
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<in> A \<and> x=e ! m" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= e ! m" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                next
                  case zero
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin>A)\<and> x=0)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A)\<and> x=0)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<notin> A \<and> x=0" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= 0" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                qed
              qed
            qed

            have all_leq: "\<forall>x\<in>({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}). x \<le> e'!n" 
              using min_does_min_stuff \<open>e ! n \<le> e' ! n\<close> \<open>0 \<le> e'!n\<close>
              by blast
            have "finite (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
              by auto 
            hence fin: "finite ({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})" using set
              by metis 

            from set have "Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = Max ({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})"
              by presburger
            also have "... \<le> (e' ! n)" using all_leq fin Max_ge
              by (simp add: Un_empty insert_not_empty)
            finally have "the (apply_inv_update u e) ! n \<le> (e' ! n)" using inv_max by metis 
            then show ?thesis using upd_v by presburger 
          next
            case minus_one
            hence "(apply_component n (u ! n) e') \<noteq> None" using \<open>e' \<in> possible_inv u e\<close> those_all_Some
              by (smt (verit) \<open>length (the (apply_inv_update u e)) = length e'\<close> \<open>n < length (the (apply_inv_update u e))\<close> apply_update.simps length_map map_nth mem_Collect_eq nth_map nth_upt plus_nat.add_0)
            hence "the (apply_component n (u ! n) e') = (e'! n) -1" using apply_component.simps(2) minus_one
              by (metis option.sel)
            hence "e ! n \<le>( e' ! n) -1" using \<open>e ! n \<le> (the (apply_update u e')) ! n\<close> upd_v by simp
            have "0 \<le> (e'!n)-1" by simp
            have set: "({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = {nth e n} \<union>{(nth e n)+1}\<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
            proof
             show "({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                \<subseteq> {nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
              proof 
                fix x 
                assume "x \<in> ({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
                from this consider (n) "x \<in> {nth e n}"|(map) "x\<in>set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))"
                  by blast
                then show "x\<in> {nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
                proof(cases)
                  case n
                  then show ?thesis by simp
                next
                  case map
                  hence "\<exists>m < length (List.enumerate 0 u). x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m"
                    by (metis (no_types, lifting) in_set_conv_nth length_map) 
                  from this obtain m where M: "m < length (List.enumerate 0 u)" and "x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m" by auto
                  hence X: "x = (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (m, u !m)" using nth_map M
                    by (simp add: nth_enumerate_eq)

                  consider (zero) "u ! m = zero" |(minus_one1) "u ! m = minus_one" |(min_set) "\<exists>A. min_set A = u ! m"
                    by (metis update_component.exhaust)
                  then show ?thesis 
                  proof(cases)
                    case zero
                    then show ?thesis using X by auto
                  next
                    case minus_one1
                    then show ?thesis 
                    proof(cases "n=m")
                      case True
                      then show ?thesis using X minus_one1 by simp 
                    next
                      case False
                      then show ?thesis  using X  minus_one1 by simp 
                    qed
                  next
                    case min_set
                    from this obtain A where "min_set A = u ! m" by auto
                    then show ?thesis 
                    proof(cases "n \<in> A")
                      case True
                      hence "x= e!m" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> True by auto 
                    next
                      case False
                      hence "x= 0" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> False by auto 
                    qed
                  qed
                qed
              qed
              show "{nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}
                \<subseteq> {e ! n} \<union> set (map (\<lambda>(m, up). case up of 
                zero \<Rightarrow> e ! n | 
                minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n | 
                min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (List.enumerate 0 u))" 
              proof
                fix x 
                assume "x \<in> {nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                from this consider (n) "x \<in> {nth e n}" | (plus_one) "x\<in> {(nth e n)+1}" | (min_set) "x\<in>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))}" |(zero) "x\<in> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                  by blast
                then show " x \<in> {e ! n} \<union>
              set (map (\<lambda>(m, up).
                           case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                           | min_set A \<Rightarrow> if n \<in> A then e ! m else 0)
                    (List.enumerate 0 u))" 
                proof(cases)
                  case n
                  then show ?thesis by blast
                next
                  case plus_one              
                  have "(List.enumerate 0 u)!n = (n, minus_one)" using minus_one nth_enumerate_eq \<open>n < length (the (apply_inv_update u e))\<close>
                    by (metis add_0 apply_inv_update.elims assms(1) len_inv_appl)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0)(n, minus_one) = (e!n)+1"
                    by simp
                  hence " (e!n)+1 \<in> set (map (\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0)
               (List.enumerate 0 u))" using \<open>(List.enumerate 0 u)!n = (n, minus_one)\<close> length_enumerate length_map nth_map nth_mem
                    by (metis (no_types, lifting) \<open>n < length (the (apply_inv_update u e))\<close> apply_inv_update.simps assms(1) len_inv_appl)
                  then show ?thesis using plus_one by blast 
                next
                  case min_set
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<in> A \<and> x=e ! m" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= e ! m" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                next
                  case zero
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin>A)\<and> x=0)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A)\<and> x=0)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<notin> A \<and> x=0" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= 0" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                qed
              qed   
            qed

            have "0 < (e'!n)" using upd_v \<open>e'\<in>possible_inv u e\<close> apply_component.simps(2) minus_one
              using \<open>apply_component n (u ! n) e' \<noteq> None\<close> by auto
            from \<open>e ! n \<le> (e' ! n)-1\<close> have "((e ! n) +1) \<le> (e'!n)" 
            proof(cases "e'!n = \<infinity>")
              case True
              then show ?thesis using enat_ord_code(4) by simp
            next
              case False
              hence "\<exists>b. (e' ! n) = enat b" by simp
              from this obtain b where "(e' ! n) = enat b" by auto
              hence "\<exists>b'. (e' ! n) = enat (Suc b')" using \<open>0 < (e'!n)\<close>
                by (simp add: not0_implies_Suc zero_enat_def)
              from this obtain b' where "(e' ! n) = enat (Suc b')" by auto
              hence \<open>e ! n \<le> enat b'\<close> using \<open>e ! n \<le> (e' ! n)-1\<close>
                by (simp add: one_enat_def)
              hence \<open>(e ! n)+1 \<le> enat (Suc b')\<close>
                by (metis add.commute add_left_mono of_nat_Suc of_nat_eq_enat)
              thus ?thesis using \<open>(e' ! n) = enat (Suc b')\<close>
                by auto
            qed

            hence "(e ! n) \<le> (e'!n)"
              by (metis add.commute add_0 add_mono_thms_linordered_semiring(3) dual_order.trans i0_lb)
            from \<open>0 \<le> (e'!n)-1\<close> have "0 \<le> (e'!n)"by simp

            have all_leq: "\<forall>x\<in>({nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}). x \<le> (e'!n)" 
              using min_does_min_stuff \<open>(e ! n) \<le> (e'!n)\<close> \<open>((e ! n) +1) \<le> (e'!n)\<close> \<open>0 \<le> (e'!n)\<close> by blast
            have finite: "finite ({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
              by auto 
            hence fin: "finite ({nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})" using set
              by metis 

            from minus_one have "(List.enumerate 0 u) ! n = (n, minus_one)"
              by (metis \<open>n < length (the (apply_inv_update u e))\<close> add_0 assms(1) len_inv_appl nth_enumerate_eq) 
            hence "(e ! n) +1 \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using nth_map set_map
              by (smt (verit, best) \<open>n < length (the (apply_inv_update u e))\<close> assms(1) case_prod_conv len_inv_appl length_enumerate length_map nth_mem update_component.simps(9)) 
            hence "Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                \<le> Max ({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using Max_mono finite
              by (metis (no_types, lifting) Un_upper2 empty_iff) 
            also have "... = Max ({nth e n} \<union> {(nth e n)+1}\<union>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})"
              using set by presburger
            also have "... \<le> (e' ! n)" using all_leq fin Max_ge
              by (simp add: Un_empty insert_not_empty)
            finally have "the (apply_inv_update u e) ! n \<le> (e' ! n)" using inv_max by metis 
            then show ?thesis using upd_v by presburger 
          next
            case min_set
            from this obtain A where "min_set A = u ! n" by auto
            hence "n \<in> A \<and> A \<subseteq> {x. x < length e}" using assms by simp
            hence "the (apply_component n (u ! n) e') = (min_list (nths e' A))" using apply_component.simps(3) \<open>min_set A = u ! n\<close>
              by (metis option.sel) 
            hence "e ! n \<le> (min_list (nths e' A))"  using \<open>e ! n \<le> (the (apply_update u e')) ! n\<close> upd_v by simp
            hence "e ! n \<le> e' ! n" using \<open>n \<in> A \<and> A \<subseteq> {x. x < length e}\<close>
              by (metis \<open>min_set A = u ! n\<close> min_does_min_stuff) 
            have "0 \<le> e'!n" by simp
            have set: "({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
            proof
              show "({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                \<subseteq> {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
              proof 
                fix x 
                assume "x \<in> ({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
                from this consider (n) "x \<in> {nth e n}" |(map) "x\<in>set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))"
                  by blast
                then show "x\<in> {nth e n} \<union> {(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}" 
                proof(cases)
                  case n
                  then show ?thesis by simp
                next
                  case map
                  hence "\<exists>m < length (List.enumerate 0 u). x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m"
                    by (metis (no_types, lifting) in_set_conv_nth length_map) 
                  from this obtain m where M: "m < length (List.enumerate 0 u)" and "x = (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))!m" by auto
                  hence X: "x = (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (m, u!m)" using nth_map M
                    by (simp add: nth_enumerate_eq)

                  consider (zero) "u ! m = zero" |(minus_one) "u ! m = minus_one" |(min_set1) "\<exists>A. min_set A = u ! m"
                    by (metis update_component.exhaust)
                  then show ?thesis 
                  proof(cases)
                    case zero
                    then show ?thesis using X by auto
                  next
                    case minus_one
                    then show ?thesis using X \<open>min_set A = u ! n\<close> by auto
                  next
                    case min_set1
                    from this obtain A where "min_set A = u ! m" by auto
                    then show ?thesis 
                    proof(cases "n \<in> A")
                      case True
                      hence "x= e!m" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> True by auto 
                    next
                      case False
                      hence "x= 0" using X \<open>min_set A = u ! m\<close>
                        by (smt (verit) case_prod_conv update_component.simps(10))
                      then show ?thesis using M \<open>min_set A = u ! m\<close> False by auto 
                    qed
                  qed
                qed
              qed
              show "{nth e n} \<union> {(e ! m)|m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}
                \<subseteq> {e ! n} \<union> set (map (\<lambda>(m, up). case up of 
                zero \<Rightarrow> e ! n | 
                minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n | 
                min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (List.enumerate 0 u))" 
              proof
                fix x 
                assume "x \<in> {nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                from this consider (n) "x \<in> {nth e n}" |(min_set) "x\<in>{(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))}" |(zero) "x\<in> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}"
                  by blast
                then show " x \<in> {e ! n} \<union>
              set (map (\<lambda>(m, up).
                           case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                           | min_set A \<Rightarrow> if n \<in> A then e ! m else 0)
                    (List.enumerate 0 u))" 
                proof(cases)
                  case n
                  then show ?thesis by blast
                next
                  case min_set
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A)\<and> x=e ! m)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<in> A \<and> x=e ! m" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= e ! m" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                next
                  case zero
                  hence "\<exists>m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin>A)\<and> x=0)"
                    by auto
                  from this obtain m where M: "(m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A)\<and> x=0)" by auto
                  from this obtain A where A: "u ! m = min_set A \<and> n \<notin> A \<and> x=0" by auto
                  hence "(List.enumerate 0 u) ! m = (m,  min_set A )" using M nth_enumerate_eq
                    by (metis add_0)
                  have "(\<lambda>(m, up).
                      case up of zero \<Rightarrow> e ! n | minus_one \<Rightarrow> if n = m then e ! n + 1 else e ! n
                      | min_set A \<Rightarrow> if n \<in> A then e ! m else 0) (m,  min_set A )= 0" using M A
                    by simp 
                  then show ?thesis using M A \<open>List.enumerate 0 u ! m = (m, min_set A)\<close>
                    by (metis (no_types, lifting) UnCI length_enumerate length_map nth_map nth_mem)
                qed
              qed   
            qed
            have all_leq: "\<forall>x\<in>({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))}). x \<le> e'!n" 
              using min_does_min_stuff \<open>e ! n \<le> e' ! n\<close> \<open>0 \<le> e'!n\<close>
              by blast
            have "finite ({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))"
              by auto 
            hence fin: "finite ({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})" using set
              by metis 

            from \<open>min_set A = u ! n\<close> have "(List.enumerate 0 u) ! n = (n, min_set A)"
              by (metis \<open>n < length (the (apply_inv_update u e))\<close> add_0 assms(1) len_inv_appl nth_enumerate_eq) 
            hence "(e ! n) \<in> (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" using nth_map set_map
              by (smt (verit, best) \<open>n < length (the (apply_inv_update u e))\<close> \<open>n \<in> A \<and> A \<subseteq> {x. x < length e}\<close> assms(1) case_prod_conv in_set_conv_nth len_inv_appl length_enumerate length_map update_component.simps(10))
            hence set1: "({nth e n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u)))" by blast

            from set set1 have "Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth e n | 
                minus_one \<Rightarrow> (if n=m then (nth e n)+1 else nth e n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth e m) else 0))) (List.enumerate 0 u))) 
                = Max ({nth e n} \<union> {(e ! m)| m.( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<in> A))} \<union> {0| m. ( m < length u \<and> (\<exists> A. (u ! m) = min_set A \<and> n \<notin> A))})"
              by presburger
            also have "... \<le> (e' ! n)" using all_leq fin Max_ge
              by (simp add: Un_empty insert_not_empty)
            finally have "the (apply_inv_update u e) ! n \<le> (e' ! n)" using inv_max by metis 
            then show ?thesis using upd_v by presburger 
          qed
        qed
      qed
    qed
  qed


  have apply_inv_is_possible_inv: "\<And>u v. length u = length v \<Longrightarrow> valid_update u \<Longrightarrow> inv_upd u v \<in> possible_inv u v"
  using leq_up_inv inv_not_none_then inv_not_none by blast

  show "energy_Min (possible_inv u e) \<subseteq> {the (apply_inv_update u e)}" 
    using apply_inv_leq_possible_inv apply_inv_is_possible_inv energy_Min_def assms
    by (smt (verit, del_insts) Collect_cong insert_iff mem_Collect_eq subsetI) 
  show "{the (apply_inv_update u e)} \<subseteq> energy_Min (possible_inv u e)"
    using apply_inv_leq_possible_inv apply_inv_is_possible_inv energy_Min_def
    by (smt (verit, ccfv_SIG) \<open>energy_Min (possible_inv u e) \<subseteq> {the (apply_inv_update u e)}\<close> assms(1) assms(2) energy_leq.strict_trans1 insert_absorb mem_Collect_eq subset_iff subset_singletonD) 
qed

text\<open>
We now show that\<open>apply_inv_update u\<close> is decreasing. 
\<close>

lemma inv_up_leq: 
  assumes "apply_update u e \<noteq> None" and "valid_update u" 
  shows "(inv_upd u (upd u e)) e\<le> e"
  unfolding energy_leq_def proof
  from assms(1) have "length e = length u"
    by (metis apply_update.simps)
  hence "length (the (apply_update u e)) = length u" using len_appl assms(1)
    by presburger
  hence "(apply_inv_update u (the (apply_update u e))) \<noteq> None"
    using inv_not_none by presburger 
  thus "length (the (apply_inv_update u (the (apply_update u e)))) = length e" using len_inv_appl \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close>
    by presburger
  show "\<forall>n<length (the (apply_inv_update u (the (apply_update u e)))).
       the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n "
  proof
    fix n 
    show "n < length (the (apply_inv_update u (the (apply_update u e)))) \<longrightarrow>
         the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n"
    proof 
      assume "n < length (the (apply_inv_update u (the (apply_update u e))))"
      hence "n < length e"
        using \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> by auto 
      show "the (apply_inv_update u (the (apply_update u e))) ! n \<le> e ! n"
      proof-
        have "the (apply_inv_update u (the (apply_update u e))) !n = (map (\<lambda>n. apply_inv_component n u (the (apply_update u e))) [0..<length (the (apply_update u e))]) ! n " using apply_inv_update.simps
          using \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close> option.sel by auto 
        hence A: "the (apply_inv_update u (the (apply_update u e))) !n = apply_inv_component n u (the (apply_update u e))"
          by (metis \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> \<open>length (the (apply_update u e)) = length u\<close> \<open>length e = length u\<close> \<open>n < length (the (apply_inv_update u (the (apply_update u e))))\<close> diff_diff_left length_upt nth_map nth_upt plus_nat.add_0 zero_less_diff)
        have "apply_inv_component n u (the (apply_update u e)) \<le> e ! n" proof-

          have "\<forall>x \<in>({nth (the (apply_update u e)) n} \<union> set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth (the (apply_update u e)) n | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else nth (the (apply_update u e)) n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0))) (List.enumerate 0 u))). x \<le> e ! n" 
          proof
            fix x 
            assume X: "x \<in> {the (apply_update u e) ! n} \<union>
             set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   (List.enumerate 0 u))"
            show "x \<le> e ! n" proof(cases "x=the (apply_update u e) ! n")
              case True
              then show ?thesis using updates_declining energy_leq_def
                using Collect_cong \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> \<open>n < length (the (apply_inv_update u (the (apply_update u e))))\<close> assms(1) assms(2) by auto
            next
              case False
              hence "x \<in> set (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   (List.enumerate 0 u))" using X by auto
              hence "\<exists>m < length (List.enumerate 0 u). x =  (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   (List.enumerate 0 u)) ! m" using in_set_conv_nth
                by (metis (no_types, lifting) length_map) 
              from this obtain m where "m < length (List.enumerate 0 u)" and "x =  (map (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   (List.enumerate 0 u)) ! m" by auto
              hence "x = (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   ((List.enumerate 0 u) ! m)" using nth_map \<open>m < length (List.enumerate 0 u)\<close>
                by simp 
              hence X: "x= (\<lambda>(m, up).
                          case up of zero \<Rightarrow> the (apply_update u e) ! n
                          | minus_one \<Rightarrow> if n = m then the (apply_update u e) ! n + 1 else the (apply_update u e) ! n
                          | min_set A \<Rightarrow> if n \<in> A then the (apply_update u e) ! m else 0)
                   (m, (u ! m))"
                by (metis (no_types, lifting) \<open>m < length (List.enumerate 0 u)\<close> add_cancel_left_left length_enumerate nth_enumerate_eq)

              consider (zero) "u ! m = zero" | (minus_one) "u ! m = minus_one" | (min) "\<exists>A. u !m = min_set A" 
                using update_component.exhaust by auto 
              thus "x \<le> e ! n" proof(cases)
                case zero
                hence "x = the (apply_update u e) ! n" using X by simp
                then show ?thesis using False by blast
              next
                case minus_one
                then show ?thesis proof(cases "m=n")
                  case True
                  hence "u ! n = minus_one" using minus_one by simp
                  have "(apply_component n (u ! n) e) \<noteq> None"  using assms(1) those_all_Some apply_update.simps apply_component.simps \<open>n < length e\<close>
                    by (smt (verit) add_cancel_right_left length_map map_nth nth_map nth_upt)
                  hence "e ! n > 0" using \<open>u ! n = minus_one\<close> by auto
                  hence "((e!n) -1 )+1 = e!n" proof(cases "e ! n = \<infinity>")
                    case True
                    then show ?thesis by simp
                  next
                    case False
                    hence "\<exists>b. e ! n = enat b" by simp
                    from this obtain b where "e ! n = enat b" by auto
                    hence "\<exists>b'. b = Suc b'" using \<open>e ! n > 0\<close>
                      by (simp add: not0_implies_Suc zero_enat_def)
                    from this obtain b' where "b = Suc b'" by auto
                    hence "e ! n = enat (Suc b')" using \<open>e ! n = enat b\<close> by simp
                    hence "(e!n)-1 = enat b'"
                      by (metis eSuc_enat eSuc_minus_1) 
                    hence "((e!n) -1 )+1 = enat (Suc b')"
                      using eSuc_enat plus_1_eSuc(2) by auto 
                    then show ?thesis using \<open>e ! n = enat (Suc b')\<close> by simp  
                  qed

                  from True have "x = (the (apply_update u e) ! n) +1" using X minus_one by simp
                  also have "... = (the (apply_component n (u ! n) e)) +1" using apply_to_comp_n assms
                    using \<open>length (the (apply_inv_update u (the (apply_update u e)))) = length e\<close> \<open>n < length (the (apply_inv_update u (the (apply_update u e))))\<close> by presburger
                  also have "... = ((e !n) -1 ) +1" using \<open>u ! n = minus_one\<close> assms those_all_Some apply_update.simps apply_component.simps
                    using \<open>0 < e ! n\<close> by auto 
                  finally have "x = e ! n" using \<open>((e!n) -1 )+1 = e!n\<close> by simp
                  then show ?thesis by simp
                next
                  case False
                  hence "x = the (apply_update u e) ! n" using X minus_one by simp
                  then show ?thesis using \<open>x \<noteq> the (apply_update u e) ! n\<close> by blast
                qed
              next
                case min
                from this obtain A where "u ! m = min_set A" by auto
                hence "m\<in> A \<and> A \<subseteq> {x. x < length e}" using assms
                  by (simp add: \<open>length e = length u\<close>) 
                then show ?thesis proof(cases "n \<in> A")
                  case True
                  hence "x = the (apply_update u e) ! m" using X \<open>u ! m = min_set A\<close> by simp
                  also have "... = (the (apply_component n (u ! m) e))" using apply_to_comp_n
                    by (metis \<open>length e = length u\<close> \<open>m < length (List.enumerate 0 u)\<close> \<open>u ! m = min_set A\<close> apply_component.simps(3) assms(1) length_enumerate) 
                  also have "... = (min_list (nths e A))" using \<open>u ! m = min_set A\<close> apply_component.simps by simp
                  also have "... = Min (set (nths e A))" using \<open>m\<in> A \<and> A \<subseteq> {x. x < length e}\<close> min_list_Min
                    by (smt (z3) True \<open>n < length e\<close> less_zeroE list.size(3) mem_Collect_eq set_conv_nth set_nths)
                  also have "... \<le> e!n" using True Min_le \<open>m\<in> A \<and> A \<subseteq> {x. x < length e}\<close>
                    using List.finite_set \<open>n < length e\<close> set_nths by fastforce
                  finally show ?thesis .
                next
                  case False
                  hence "x = 0" using X \<open>u ! m = min_set A\<close> by simp
                  then show ?thesis by simp
                qed
              qed
            qed
          qed
          hence leq: "\<forall>x \<in>(set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth (the (apply_update u e)) n | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else nth (the (apply_update u e)) n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0))) (List.enumerate 0 u))). x \<le> e ! n" by blast

          have "apply_inv_component n u (the (apply_update u e)) =  Max (set (map (\<lambda>(m,up). (case up of 
                zero \<Rightarrow> nth (the (apply_update u e)) n | 
                minus_one \<Rightarrow> (if n=m then (nth (the (apply_update u e)) n)+1 else nth (the (apply_update u e)) n) |
                min_set A \<Rightarrow> (if n\<in>A then (nth (the (apply_update u e)) m) else 0))) (List.enumerate 0 u)))" using apply_inv_component.simps
            by blast 
          also have "... \<le> e! n" using leq Max_le_iff
            by (smt (verit) List.finite_set \<open>length e = length u\<close> \<open>n < length e\<close> empty_iff length_enumerate length_map nth_mem)
          finally show ?thesis .
        qed
        thus ?thesis using A by presburger 
      qed
    qed
  qed
qed

text\<open>We now conclude that for any valid update the functions $e \mapsto  \min \lbrace e' \ | \ e \leq u(e') \rbrace$ and $u$ form a 
Galois connection between the domain of $u$ and the set of energies of the same length as $u$ w.r.t 
to the component-wise order.\<close>

lemma galois_connection:
  assumes "apply_update u e' \<noteq> None" and "length e = length e'" and 
          "valid_update u"
  shows "(inv_upd u e) e\<le> e' = e e\<le> (upd u e')"
proof
  show "energy_leq (the (apply_inv_update u e)) e' \<Longrightarrow> energy_leq e (upd u e')" 
  proof- 
    assume A: "energy_leq (the (apply_inv_update u e)) e'" 
    from assms(1) have "length u = length e" using apply_update.simps assms(2) by metis
    hence leq: "energy_leq e (the (apply_update u (the (apply_inv_update u e))))" using leq_up_inv assms(3) inv_not_none
      by presburger
    have "(apply_update u (the (apply_inv_update u e))) \<noteq> None" using \<open>length u = length e\<close>
      using inv_not_none inv_not_none_then by blast
    hence "energy_leq (the (apply_update u (the (apply_inv_update u e)))) (the (apply_update u e'))" using A updates_monotonic
      using \<open>length u = length e\<close> assms(3) inv_not_none len_inv_appl by presburger  
    thus "energy_leq e (the (apply_update u e'))" using leq
      using energy_leq.trans by blast 
  qed
  show "energy_leq e (the (apply_update u e')) \<Longrightarrow> energy_leq (the (apply_inv_update u e)) e' " 
  proof-
    assume A: "energy_leq e (the (apply_update u e'))"
    have "apply_inv_update u e \<noteq> None" using assms
      by (metis apply_update.simps inv_not_none) 
    have "length u = length e" using assms
      by (metis apply_update.elims) 
    from A have "e' \<in> possible_inv u e"
      using assms(1) mem_Collect_eq by auto
    thus "energy_leq (the (apply_inv_update u e)) e'" using apply_inv_is_min assms \<open>length u = length e\<close> energy_Min_def
      by (smt (verit) A Collect_cong energy_leq.strict_trans1 inv_up_leq inverse_monotonic len_appl) 
  qed
qed

end