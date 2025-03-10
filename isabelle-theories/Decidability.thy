section \<open>Decidability of Bisping's Declining Energy Games\<close>

theory Decidability
  imports Galois_Energy_Game Complete_Non_Orders.Kleene_Fixed_Point
begin

text\<open>In this theory we give a proof of decidability for Galois energy games (over vectors of naturals). 
We do this by providing a proof of correctness of the simplifyed version of
Bisping's Algorithm to calculate minimal attacker winning budgets. 
We further formalise the key argument for its termination.
\<close>

locale galois_energy_game_assms = galois_energy_game attacker weight application inverse_application dimension
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> 'label option" and
      application :: "'label \<Rightarrow> energy \<Rightarrow> energy option" and
      inverse_application :: "'label \<Rightarrow> energy \<Rightarrow> energy option" and
      dimension :: "nat"
+
assumes nonpos_eq_pos: "nonpos_winning_budget = winning_budget" and
        finite_positions: "finite positions"
begin

subsection\<open>Minimal Attacker Winning Budgets as Pareto Fronts\<close>

text\<open>We now prepare the proof of decidability by introducing minimal winning budgets.\<close>

abbreviation minimal_winning_budget:: "energy \<Rightarrow> 'position \<Rightarrow> bool" where
"minimal_winning_budget e g \<equiv> e \<in> energy_Min {e. winning_budget_len e g}"
abbreviation "a_win g \<equiv> {e. winning_budget_len e g}"
abbreviation "a_win_min g \<equiv> energy_Min (a_win g)"

text\<open>Since the component-wise order on energies is well-founded, we can conclude that minimal winning budgets are finite.\<close>

lemma minimal_winning_budget_finite:
  shows "\<And>g. finite (a_win_min g)"
  using energy_Min_finite
  by (metis mem_Collect_eq winning_budget_len.cases) 

text\<open>We now introduce the set of mappings from positions to possible Pareto fronts, i.e.\ incomparable sets of energies.\<close>

definition possible_pareto:: "('position \<Rightarrow> energy set) set" where 
  "possible_pareto \<equiv> {F. \<forall>g. F g \<subseteq> {e. length e = dimension} 
                          \<and> (\<forall>e e'. (e \<in> F g \<and> e' \<in> F g \<and> e \<noteq> e') 
                             \<longrightarrow> (\<not> e e\<le> e' \<and> \<not> e' e\<le> e))}"

text\<open>By definition minimal winning budgets are possible Pareto fronts.\<close>

lemma a_win_min_in_pareto:
  shows "a_win_min \<in> possible_pareto" 
  unfolding energy_Min_def possible_pareto_def proof
  show "\<forall>g. {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<subseteq> {e. length e = dimension} \<and>
        (\<forall>e e'.
            e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
            e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e' \<longrightarrow>
            incomparable (e\<le>) e e') "
  proof
    fix g 
    show "{e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<subseteq> {e. length e = dimension} \<and>
         (\<forall>e e'.
             e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
             e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e' \<longrightarrow>
             incomparable (e\<le>) e e')"
    proof
      show "{e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<subseteq> {e. length e = dimension}"
        using winning_budget_len.simps
        by blast
      show " \<forall>e e'.
       e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
       e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e' \<longrightarrow>
       incomparable (e\<le>) e e' "
      proof
        fix e
        show "\<forall>e'. e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
              e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e' \<longrightarrow>
              incomparable (e\<le>) e e'"
        proof
          fix e'
          show "e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
          e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e' \<longrightarrow>
          incomparable (e\<le>) e e'"
          proof
            assume " e \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and>
    e' \<in> {e \<in> a_win g. \<forall>e'\<in>a_win g. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e} \<and> e \<noteq> e'"
            thus "incomparable (e\<le>) e e'" 
              by auto
          qed
        qed
      qed
    qed
  qed
qed

text\<open>We define a partial order on possible Pareto fronts.\<close>

definition pareto_order:: "('position \<Rightarrow> energy set) \<Rightarrow> ('position \<Rightarrow> energy set) \<Rightarrow> bool"  (infix "\<preceq>" 80) where
  "pareto_order F F' \<equiv> (\<forall>g e. e \<in> F(g) \<longrightarrow> (\<exists>e'. e' \<in> F'(g) \<and>  e' e\<le> e))"

lemma pareto_partial_order_vanilla:
  shows reflexivity: "\<And>F. F \<in> possible_pareto \<Longrightarrow> F \<preceq> F" and 
transitivity: "\<And>F F' F''. F \<in> possible_pareto \<Longrightarrow> F' \<in> possible_pareto 
               \<Longrightarrow> F'' \<in> possible_pareto \<Longrightarrow>  F \<preceq> F' \<Longrightarrow> F' \<preceq> F'' 
               \<Longrightarrow> F \<preceq> F'' " and
antisymmetry: "\<And>F F'.  F \<in> possible_pareto \<Longrightarrow> F' \<in> possible_pareto 
               \<Longrightarrow> F \<preceq> F' \<Longrightarrow> F' \<preceq> F \<Longrightarrow> F = F'"
proof-
  fix F F' F''
  assume "F \<in> possible_pareto" and "F' \<in> possible_pareto" and "F'' \<in> possible_pareto"
  show "F \<preceq> F"
    unfolding pareto_order_def
    using energy_leq.refl by auto 
  show "F \<preceq> F' \<Longrightarrow> F' \<preceq> F'' \<Longrightarrow> F \<preceq> F'' "
  proof-
    assume "F \<preceq> F'" and "F' \<preceq> F''" 
    show " F \<preceq> F'' "
      unfolding pareto_order_def proof
      show "\<And>g. \<forall>e. e \<in> F g \<longrightarrow> (\<exists>e'. e' \<in> F'' g \<and> e' e\<le> e)"
      proof
        fix g e
        show "e \<in> F g \<longrightarrow> (\<exists>e'. e' \<in> F'' g \<and> e' e\<le> e)"
        proof
          assume "e \<in> F g"
          hence "(\<exists>e'. e' \<in> F' g \<and> e' e\<le> e)" using \<open>F \<preceq> F'\<close> unfolding pareto_order_def by simp
          from this obtain e' where "e' \<in> F' g \<and> e' e\<le> e" by auto
          hence "(\<exists>e''. e'' \<in> F'' g \<and> e'' e\<le> e')" using \<open>F' \<preceq> F''\<close> unfolding pareto_order_def by simp
          from this obtain e'' where "e'' \<in> F'' g \<and> e'' e\<le> e'" by auto
          hence "e'' \<in> F'' g \<and> e'' e\<le> e" using \<open>e' \<in> F' g \<and> e' e\<le> e\<close> energy_leq.trans by auto
          thus "\<exists>e'. e' \<in> F'' g \<and> e' e\<le> e" by auto
        qed
      qed
    qed
  qed
  show "F \<preceq> F' \<Longrightarrow> F' \<preceq> F \<Longrightarrow> F = F'"
  proof-
    assume "F \<preceq> F'" and "F' \<preceq> F"
    show "F = F'"
    proof
      fix g 
      show "F g = F' g"
      proof
        show "F g \<subseteq> F' g"
        proof
          fix e
          assume "e \<in> F g"
          hence "\<exists>e'. e' \<in> F' g \<and> e' e\<le> e" using \<open>F \<preceq> F'\<close> unfolding pareto_order_def by auto
          from this obtain e' where "e' \<in> F' g \<and> e' e\<le> e" by auto
          hence "\<exists>e''. e'' \<in> F g \<and> e'' e\<le> e'" using \<open>F' \<preceq> F\<close> unfolding pareto_order_def by auto
          from this obtain e'' where "e'' \<in> F g \<and> e'' e\<le> e'" by auto
          hence "e'' = e \<and> e' = e" using possible_pareto_def \<open>F \<in> possible_pareto\<close>
            by (smt (verit) \<open>e \<in> F g\<close> \<open>e' \<in> F' g \<and> e' e\<le> e\<close> energy_leq.strict_trans1 mem_Collect_eq)
          thus "e \<in> F' g" using \<open>e' \<in> F' g \<and> e' e\<le> e\<close> by auto
        qed
        show "F' g \<subseteq> F g" 
        proof
          fix e
          assume "e \<in> F' g"
          hence "\<exists>e'. e' \<in> F g \<and> e' e\<le> e" using \<open>F' \<preceq> F\<close> unfolding pareto_order_def by auto
          from this obtain e' where "e' \<in> F g \<and> e' e\<le> e" by auto
          hence "\<exists>e''. e'' \<in> F' g \<and> e'' e\<le> e'" using \<open>F \<preceq> F'\<close> unfolding pareto_order_def by auto
          from this obtain e'' where "e'' \<in> F' g \<and> e'' e\<le> e'" by auto
          hence "e'' = e \<and> e' = e" using possible_pareto_def \<open>F' \<in> possible_pareto\<close>
            by (smt (verit) \<open>e \<in> F' g\<close> \<open>e' \<in> F g \<and> e' e\<le> e\<close> energy_leq.strict_trans1 mem_Collect_eq)
          thus "e \<in> F g" using \<open>e' \<in> F g \<and> e' e\<le> e\<close> by auto
        qed
      qed
    qed
  qed
qed

lemma pareto_partial_order:
  shows "reflp_on possible_pareto (\<preceq>)" and 
        "transp_on possible_pareto (\<preceq>)" and 
        "antisymp_on possible_pareto (\<preceq>)"
proof-
  show "reflp_on possible_pareto (\<preceq>)"
    using reflexivity
    by (simp add: reflp_onI)
  show "transp_on possible_pareto (\<preceq>)"
    using transitivity
    using transp_onI by blast
  show "antisymp_on possible_pareto (\<preceq>)"
    using antisymmetry
    using antisymp_onI by auto
qed

text\<open>By defining a supremum, we show that the order is directed-complete bounded join-semilattice.\<close>

definition pareto_sup:: "('position \<Rightarrow> energy set) set \<Rightarrow> ('position \<Rightarrow> energy set)" where 
  "pareto_sup P g = energy_Min {e. \<exists>F. F\<in> P \<and> e \<in> F g}"

lemma pareto_sup_is_sup:
  assumes "P \<subseteq> possible_pareto"
  shows "pareto_sup P \<in> possible_pareto" and 
        "\<And>F. F \<in> P \<Longrightarrow> F \<preceq> pareto_sup P" and 
        "\<And>Fs. Fs \<in> possible_pareto \<Longrightarrow> (\<And>F. F \<in> P \<Longrightarrow> F \<preceq> Fs) 
         \<Longrightarrow> pareto_sup P \<preceq> Fs"
proof-
  show "pareto_sup P \<in> possible_pareto" unfolding pareto_sup_def possible_pareto_def energy_Min_def
    by (smt (verit, ccfv_threshold) Ball_Collect assms mem_Collect_eq possible_pareto_def) 
  show "\<And>F. F \<in> P \<Longrightarrow> F \<preceq> pareto_sup P"
  proof-
    fix F
    assume "F \<in> P"
    show "F \<preceq> pareto_sup P"
      unfolding pareto_order_def proof
      show "\<And>g. \<forall>e. e \<in> F g \<longrightarrow> (\<exists>e'. e' \<in> pareto_sup P g \<and> e' e\<le> e)"
      proof
        fix g e
        show "e \<in> F g \<longrightarrow> (\<exists>e'. e' \<in> pareto_sup P g \<and> e' e\<le> e)"
        proof
          assume "e \<in> F g"
          hence "e\<in>{(e::energy). (\<exists>F. F\<in> P \<and>  e\<in> (F g))}" using \<open>F \<in> P\<close> by auto
          hence "\<exists>e'. e' \<in> energy_Min {(e::energy). (\<exists>F. F\<in> P \<and>  e\<in> (F g))} \<and> e' e\<le> e" 
            using energy_Min_contains_smaller
            by (smt (verit) Collect_mono_iff mem_Collect_eq)
          thus "\<exists>e'. e' \<in> pareto_sup P g \<and> e' e\<le> e" unfolding pareto_sup_def by simp
        qed
      qed
    qed
  qed
  show "\<And>Fs. Fs \<in> possible_pareto \<Longrightarrow> (\<And>F. F \<in> P \<Longrightarrow> F \<preceq> Fs) \<Longrightarrow> pareto_sup P \<preceq> Fs"
  proof-
    fix Fs
    assume "Fs \<in> possible_pareto" and "(\<And>F. F \<in> P \<Longrightarrow> F \<preceq> Fs)"
    show "pareto_sup P \<preceq> Fs"
      unfolding pareto_order_def proof
      show "\<And>g. \<forall>e. e \<in> pareto_sup P g \<longrightarrow> (\<exists>e'. e' \<in> Fs g \<and> e' e\<le> e) "
      proof
        fix g e 
        show "e \<in> pareto_sup P g \<longrightarrow> (\<exists>e'. e' \<in> Fs g \<and> e' e\<le> e)"
        proof
          assume "e \<in> pareto_sup P g"
          hence "e\<in> {e. \<exists>F. F \<in> P \<and> e \<in> F g}" unfolding pareto_sup_def using energy_Min_def by simp
          from this obtain F where "F \<in> P \<and> e \<in> F g" by auto
          thus "\<exists>e'. e' \<in> Fs g \<and> e' e\<le> e" using \<open>(\<And>F. F \<in> P \<Longrightarrow> F \<preceq> Fs)\<close> pareto_order_def by auto 
        qed
      qed
    qed
  qed
qed

lemma pareto_directed_complete:
  shows "directed_complete possible_pareto (\<preceq>)"
  unfolding directed_complete_def 
proof-
  show "(\<lambda>X r. directed X r \<and> X \<noteq> {})-complete possible_pareto (\<preceq>)"
    unfolding complete_def 
  proof
    fix P
    show "P \<subseteq> possible_pareto \<longrightarrow>
         directed P (\<preceq>) \<and> P \<noteq> {} \<longrightarrow> (\<exists>s. extreme_bound possible_pareto (\<preceq>) P s)"
    proof
      assume "P \<subseteq> possible_pareto"
      show "directed P (\<preceq>) \<and> P \<noteq> {} \<longrightarrow> (\<exists>s. extreme_bound possible_pareto (\<preceq>) P s)"
      proof
        assume "directed P (\<preceq>) \<and> P \<noteq> {}"
        show "\<exists>s. extreme_bound possible_pareto (\<preceq>) P s"
        proof
          show "extreme_bound possible_pareto (\<preceq>) P (pareto_sup P)"
            unfolding extreme_bound_def 
          proof
            show "pareto_sup P \<in> {b \<in> possible_pareto. bound P (\<preceq>) b}" 
              using pareto_sup_is_sup \<open>P \<subseteq> possible_pareto\<close> \<open>directed P (\<preceq>) \<and> P \<noteq> {}\<close>
              by blast
            show "\<And>x. x \<in> {b \<in> possible_pareto. bound P (\<preceq>) b} \<Longrightarrow> pareto_sup P \<preceq> x"
            proof-
              fix x 
              assume "x \<in> {b \<in> possible_pareto. bound P (\<preceq>) b}"
              thus "pareto_sup P \<preceq> x"
                using pareto_sup_is_sup \<open>P \<subseteq> possible_pareto\<close> \<open>directed P (\<preceq>) \<and> P \<noteq> {}\<close>
                by auto
            qed
          qed
        qed
      qed
    qed
  qed              
qed

lemma pareto_minimal_element:
  shows "(\<lambda>g. {}) \<preceq> F"
  unfolding pareto_order_def by simp

subsection\<open>Proof of Decidability\<close>

text\<open>Using Kleene's fixed point theorem we now show, that the minimal attacker winning budgets are the least fixed point of the algorithm.
For this we first formalise one iteration of the algorithm.  
\<close>

definition iteration:: "('position \<Rightarrow> energy set) \<Rightarrow> ('position \<Rightarrow> energy set)" where 
  "iteration F g \<equiv> (if g \<in> attacker 
                    then energy_Min {inv_upd (the (weight g g')) e' | e' g'. 
                        length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'}
                    else energy_Min {energy_sup dimension 
                         {inv_upd (the (weight g g')) (e_index g') | g'. 
                         weight g g' \<noteq> None} | e_index. \<forall>g'. weight g g' \<noteq> None
                         \<longrightarrow> length (e_index g')= dimension \<and> e_index g' \<in> F g'})"

text\<open>We now show that \<open>iteration\<close> is a Scott-continuous functor of possible Pareto fronts.\<close>

lemma iteration_pareto_functor:
  assumes "F \<in> possible_pareto"
  shows "iteration F \<in> possible_pareto"
  unfolding possible_pareto_def
proof
  show "\<forall>g. iteration F g \<subseteq> {e. length e = dimension} \<and>
        (\<forall>e e'. e \<in> iteration F g \<and> e' \<in> iteration F g \<and> e \<noteq> e' \<longrightarrow> incomparable (e\<le>) e e')"
  proof
    fix g
    show "iteration F g \<subseteq> {e. length e = dimension} \<and>
        (\<forall>e e'. e \<in> iteration F g \<and> e' \<in> iteration F g \<and> e \<noteq> e' \<longrightarrow> incomparable (e\<le>) e e')"
    proof
      show "iteration F g \<subseteq> {e. length e = dimension}"
      proof
        fix e 
        assume "e \<in> iteration F g"
        show "e \<in> {e. length e = dimension}"
        proof
          show "length e = dimension"
          proof(cases "g \<in> attacker")
            case True
            hence "e \<in> energy_Min {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'}"
              using \<open>e \<in> iteration F g\<close> iteration_def by auto 
            then show ?thesis using assms energy_Min_def len_inv_appl
              by force
          next
            case False
            hence "e \<in> energy_Min {energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}| e_index. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> F g'))}"
              using \<open>e \<in> iteration F g\<close> iteration_def by auto
            then show ?thesis unfolding energy_sup_def using energy_Min_def
              using Ex_list_of_length by force  
          qed  
        qed
      qed
      show "(\<forall>e e'. e \<in> iteration F g \<and> e' \<in> iteration F g \<and> e \<noteq> e' \<longrightarrow> incomparable (e\<le>) e e')"
        using possible_pareto_def iteration_def energy_Min_def
        by (smt (verit) mem_Collect_eq)
    qed
  qed
qed

lemma iteration_monotonic:
  assumes "F \<in> possible_pareto" and "F' \<in> possible_pareto" and "F \<preceq> F'"
  shows "iteration F \<preceq> iteration F'"
  unfolding pareto_order_def 
proof
  fix g 
  show "\<forall>e. e \<in> iteration F g \<longrightarrow> (\<exists>e'. e' \<in> iteration F' g \<and> e' e\<le> e)"
  proof
    fix e
    show "e \<in> iteration F g \<longrightarrow> (\<exists>e'. e' \<in> iteration F' g \<and> e' e\<le> e)"
    proof
      assume "e \<in> iteration F g"
      show "(\<exists>e'. e' \<in> iteration F' g \<and> e' e\<le> e)"
      proof(cases"g\<in> attacker")
        case True
        hence "e \<in> energy_Min {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'}"
          using iteration_def \<open>e \<in> iteration F g\<close> by simp
        from this obtain e' g' where E: "e = inv_upd (the (weight g g')) e' \<and> length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'" 
          using energy_Min_def by auto 
        hence "\<exists>e''. e'' \<in> F' g' \<and> e'' e\<le> e'" using pareto_order_def assms by simp
        from this obtain e'' where "e'' \<in> F' g' \<and> e'' e\<le> e'" by auto
        hence uE: "inv_upd (the (weight g g')) e'' e\<le>  inv_upd (the (weight g g')) e'" 
          using E inverse_monotonic domain_inv
          using energy_leq_def by blast 
        hence "inv_upd (the (weight g g')) e'' \<in> {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F' g'}"
          using E iteration_def True \<open>e'' \<in> F' g' \<and> e'' e\<le> e'\<close>
          using energy_leq_def by blast
        hence "\<exists>e'''. e'''\<in> energy_Min {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F' g'} \<and> e''' e\<le> inv_upd (the (weight g g')) e''"
          using energy_Min_contains_smaller
          by meson 
        hence "\<exists>e'''. e''' \<in> iteration F' g \<and> e''' e\<le> inv_upd (the (weight g g')) e''" 
          unfolding iteration_def using True by simp
        from this obtain e''' where E''': "e''' \<in> iteration F' g \<and> e''' e\<le> inv_upd (the (weight g g')) e''" by auto
        hence "e''' e\<le> e" using E uE
          using energy_leq.trans by blast        
        then show ?thesis using E''' by auto
      next
        case False
        hence "e\<in> (energy_Min {energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}| e_index. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> F g'))})"
          using iteration_def \<open>e \<in> iteration F g\<close> by simp
        from this obtain e_index where E: "e= energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}" and "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> F g'))" 
          using energy_Min_def by auto
        hence "\<And>g'.  weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> F' g' \<and> e' e\<le> e_index g'"
          using assms(3) pareto_order_def by force
        define e_index' where "e_index' \<equiv> (\<lambda>g'. (SOME e'. (e' \<in> F' g' \<and> e' e\<le> e_index g')))"
        hence E': "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g' \<in> F' g' \<and> e_index' g' e\<le> e_index g'"
          using \<open>\<And>g'.  weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> F' g' \<and> e' e\<le> e_index g'\<close> some_eq_ex
          by (metis (mono_tags, lifting))
        hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> inv_upd (the (weight g g')) (e_index' g') e\<le> inv_upd (the (weight g g')) (e_index g')"
          using inverse_monotonic 
          using \<open>\<forall>g'. weight g g' \<noteq> None \<longrightarrow> length (e_index g') = dimension \<and> e_index g' \<in> F g'\<close>
          by (simp add: domain_inv energy_leq_def)
        hence leq: "\<And>a. a\<in> {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} \<Longrightarrow> \<exists>b. b \<in> {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None} \<and> a e\<le> b"
          by blast
        have len: "\<And>a. a\<in> {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} \<Longrightarrow> length a = dimension"
          using  E' E len_inv_appl
          using \<open>\<forall>g'. weight g g' \<noteq> None \<longrightarrow> length (e_index g') = dimension \<and> e_index g' \<in> F g'\<close> energy_leq_def by force
        hence leq: "energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}"
        proof(cases "{g'. weight g g' \<noteq> None} = {}")
          case True
          hence "{inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} = {} \<and> {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None} = {}"
            by simp
          then show ?thesis using empty_Sup_is_zero
            using energy_leq.refl by fastforce 
        next
          case False
          hence "{inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} \<noteq> {}" by simp
          then show ?thesis using energy_sup_leq_energy_sup len leq
            by meson
        qed

        have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> length (e_index' g') = dimension" using E' \<open>\<forall>g'. weight g g' \<noteq> None \<longrightarrow> length (e_index g') = dimension \<and> e_index g' \<in> F g'\<close>
          by (simp add: energy_leq_def)
        hence "energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} \<in> {energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}| e_index. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> F' g'))}"
          using E'
          by blast 
        hence "\<exists>e'. e' \<in> energy_Min {energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}| e_index. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> F' g'))}
              \<and> e' e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None}"
          using energy_Min_contains_smaller
          by meson
        hence "\<exists>e'. e' \<in> iteration F' g \<and> e' e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} "
          unfolding iteration_def using False by auto
        then show ?thesis using leq E
          using energy_leq.trans by blast 
      qed
    qed
  qed
qed

lemma finite_directed_set_upper_bound:
  assumes "\<And>F F'. F \<in> P \<Longrightarrow> F' \<in> P \<Longrightarrow> \<exists>F''. F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" 
          and "P \<noteq> {}" and "P' \<subseteq> P" and "finite P'" and "P \<subseteq> possible_pareto"
  shows "\<exists>F'. F' \<in> P \<and> (\<forall>F. F \<in> P' \<longrightarrow> F \<preceq> F')"
  using assms proof(induct "card P'" arbitrary: P')
  case 0
  then show ?case
    by auto
next
  case (Suc x)
  hence "\<exists>F. F \<in> P'"
    by auto 
  from this obtain F where "F \<in> P'" by auto
  define P'' where "P'' = P' - {F}"
  hence "card P'' = x" using Suc card_Suc_Diff1 \<open>F \<in> P'\<close> by simp
  hence "\<exists>F'. F' \<in> P \<and> (\<forall>F. F \<in> P'' \<longrightarrow> F \<preceq> F')" using Suc
    using P''_def by blast 
  from this obtain F' where "F' \<in> P \<and> (\<forall>F. F \<in> P'' \<longrightarrow> F \<preceq> F')" by auto
  hence "\<exists>F''. F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" using Suc
    by (metis (no_types, lifting) \<open>F \<in> P'\<close> in_mono)
  from this obtain F'' where "F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" by auto
  show ?case 
  proof
    show "F'' \<in> P \<and> (\<forall>F. F \<in> P' \<longrightarrow> F \<preceq> F'')" 
    proof
      show "F'' \<in> P" using \<open>F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''\<close> by simp
      show "\<forall>F. F \<in> P' \<longrightarrow> F \<preceq> F''"
      proof
        fix F0
        show "F0 \<in> P' \<longrightarrow> F0 \<preceq> F''"
        proof
          assume "F0 \<in> P'"
          show "F0 \<preceq> F''"
          proof(cases "F0 = F")
            case True
            then show ?thesis using \<open>F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''\<close> by simp
          next
            case False
            hence "F0 \<in> P''" using P''_def \<open>F0 \<in> P'\<close> by auto 
            hence "F0 \<preceq> F'" using \<open>F' \<in> P \<and> (\<forall>F. F \<in> P'' \<longrightarrow> F \<preceq> F')\<close> by simp
            then show ?thesis using \<open>F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''\<close> transitivity Suc
              by (smt (z3) \<open>F' \<in> P \<and> (\<forall>F. F \<in> P'' \<longrightarrow> F \<preceq> F')\<close> \<open>F0 \<in> P'\<close> subsetD) 
          qed
        qed
      qed
    qed
  qed
qed

lemma iteration_scott_continuous_vanilla:
  assumes "P \<subseteq> possible_pareto" and 
          "\<And>F F'. F \<in> P \<Longrightarrow> F' \<in> P \<Longrightarrow> \<exists>F''. F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" and "P \<noteq> {}"
  shows "iteration (pareto_sup P) = pareto_sup {iteration F | F. F \<in> P}"
proof(rule antisymmetry)
  from assms have "(pareto_sup P) \<in> possible_pareto" using assms pareto_sup_is_sup by simp
  thus A: "iteration (pareto_sup P) \<in> possible_pareto" using iteration_pareto_functor by simp

  have B: "{iteration F |F. F \<in> P} \<subseteq> possible_pareto"
  proof
    fix F
    assume "F \<in> {iteration F |F. F \<in> P}"
    from this obtain F' where "F = iteration F'" and "F' \<in> P" by auto
    thus "F \<in> possible_pareto" using iteration_pareto_functor
      using assms by auto 
  qed
  thus "pareto_sup {iteration F |F. F \<in> P} \<in> possible_pareto" using pareto_sup_is_sup by simp

  show "iteration (pareto_sup P) \<preceq> pareto_sup {iteration F |F. F \<in> P}"
    unfolding pareto_order_def proof
    fix g 
    show " \<forall>e. e \<in> iteration (pareto_sup P) g \<longrightarrow>
             (\<exists>e'. e' \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> e' e\<le> e)"
    proof
      fix e
      show "e \<in> iteration (pareto_sup P) g \<longrightarrow>
             (\<exists>e'. e' \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> e' e\<le> e)"
      proof
        assume "e \<in> iteration (pareto_sup P) g"
        show "\<exists>e'. e' \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> e' e\<le> e"
        proof(cases "g \<in> attacker")
          case True
          hence "e \<in> energy_Min {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> (pareto_sup P) g'}"
            using iteration_def \<open>e \<in> iteration (pareto_sup P) g\<close> by auto 
          from this obtain e' g' where "e = inv_upd (the (weight g g')) e'" and "length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> (pareto_sup P) g'" 
            using energy_Min_def by auto
          hence "\<exists>F. F\<in> P \<and> e' \<in> F g'" using pareto_sup_def energy_Min_def by simp
          from this obtain F where "F\<in> P \<and> e' \<in> F g'" by auto
          hence E:  "e \<in> {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'}" using \<open>e = inv_upd (the (weight g g')) e'\<close>
            using \<open>length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> pareto_sup P g'\<close> by blast  

          hence "\<exists>e''. e'' \<in> energy_Min {inv_upd (the (weight g g')) e' | e' g'. length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> F g'} \<and> e'' e\<le> e"
            using energy_Min_contains_smaller
            by meson 
          hence "\<exists>e''. e'' \<in> iteration F g \<and> e'' e\<le> e" using True iteration_def by simp
          from this obtain e'' where "e'' \<in> iteration F g \<and> e'' e\<le> e" by auto
          hence "\<exists>e'''. e''' \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> e''' e\<le> e''" 
            unfolding pareto_sup_def energy_Min_contains_smaller
            by (metis (mono_tags, lifting) \<open>F \<in> P \<and> e' \<in> F g'\<close> energy_Min_contains_smaller mem_Collect_eq)
          then show ?thesis
            using \<open>e'' \<in> iteration F g \<and> e'' e\<le> e\<close> energy_leq.trans by blast
        next
          case False
          hence "e \<in> energy_Min {energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}| e_index. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> (pareto_sup P) g'))}"
            using iteration_def \<open>e \<in> iteration (pareto_sup P) g\<close> by auto
          from this obtain e_index where "e= energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}" and "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g')= dimension \<and> e_index g' \<in> (pareto_sup P) g'))"
            using energy_Min_def by auto
          hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> (pareto_sup P) g'" by auto
          hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>F'. F' \<in> P \<and> e_index g' \<in> F' g'" using pareto_sup_def energy_Min_def
            by (simp add: mem_Collect_eq) 
          define F_index where "F_index \<equiv> \<lambda>g'. SOME F'. F' \<in> P \<and> e_index g' \<in> F' g'"
          hence Fg: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> F_index g' \<in> P \<and> e_index g' \<in> F_index g' g'" 
            using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>F'. F' \<in> P \<and> e_index g' \<in> F' g'\<close> some_eq_ex
            by (smt (verit)) 

          have "\<exists>F'. F' \<in> P \<and> (\<forall>F. F \<in> {F_index g' | g'. weight g g' \<noteq> None} \<longrightarrow> F \<preceq> F')"
          proof(rule finite_directed_set_upper_bound)
            show "\<And>F F'. F \<in> P \<Longrightarrow> F' \<in> P \<Longrightarrow> \<exists>F''. F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" using assms by simp
            show "P \<noteq> {}" using assms by simp
            show "{F_index g' |g'. weight g g' \<noteq> None} \<subseteq> P"
              using Fg
              using subsetI by auto 
            have "finite {g'. weight g g' \<noteq> None}" using finite_positions
              by (metis Collect_mono finite_subset)
            thus "finite {F_index g' | g'. weight g g' \<noteq> None}" by auto
            show "P \<subseteq> possible_pareto" using assms by simp
          qed
          from this obtain F where F: "F \<in> P \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>  F_index g' \<preceq> F)" by auto
          hence "F \<in> possible_pareto" using assms by auto
          have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> F g' \<and> e' e\<le> e_index g'"
          proof-
            fix g'
            assume "weight g g' \<noteq> None"
            hence "e_index g' \<in> F_index g' g'" using Fg by auto
            have "F_index g' \<preceq> F" using F \<open>weight g g' \<noteq> None\<close>  by auto
            thus "\<exists>e'. e' \<in> F g' \<and> e' e\<le> e_index g'" unfolding pareto_order_def
              using \<open>e_index g' \<in> F_index g' g'\<close> by fastforce
          qed

          define e_index' where "e_index' \<equiv> \<lambda>g'. SOME e'. e' \<in> F g' \<and> e' e\<le> e_index g'"
          hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g' \<and> e_index' g' e\<le> e_index g'"
            using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> F g' \<and> e' e\<le> e_index g'\<close> some_eq_ex by (smt (verit))
          hence "energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}"
          proof(cases "{g'. weight g g' \<noteq> None} = {}")
            case True
            hence "{inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} = {}" by simp
            have "{inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None} = {}" using True by simp
            then show ?thesis unfolding energy_leq_def using empty_Sup_is_zero \<open>{inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} = {}\<close>
              by (simp add: order_refl)
          next
            case False            
            show ?thesis 
            proof(rule energy_sup_leq_energy_sup)
              show "{inv_upd (the (weight g g')) (e_index' g') |g'. weight g g' \<noteq> None} \<noteq> {}" 
                using False by simp
              show "\<And>a. a \<in> {inv_upd (the (weight g g')) (e_index' g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
                    \<exists>b\<in>{inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None}. a e\<le> b"
              proof-
                fix a 
                assume "a \<in> {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None}"
                from this obtain g' where "a=inv_upd (the (weight g g')) (e_index' g')" and "weight g g' \<noteq> None" by auto
                have "(e_index' g') e\<le>  (e_index' g')" 
                  using \<open>weight g g' \<noteq> None\<close> \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g' \<and> e_index' g' e\<le> e_index g'\<close>
                  by (simp add: energy_leq.refl) 
                have "length (e_index' g') = dimension" 
                  using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g' \<and> e_index' g' e\<le> e_index g'\<close> possible_pareto_def \<open>weight g g' \<noteq> None\<close> F assms
                  by blast 
                hence "a e\<le> inv_upd (the (weight g g')) (e_index' g')"
                  using \<open>a=inv_upd (the (weight g g')) (e_index' g')\<close> \<open>(e_index' g') e\<le> (e_index' g')\<close> inverse_monotonic  \<open>weight g g' \<noteq> None\<close>
                  using energy_leq.refl by blast
                thus "\<exists>b\<in>{inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None}. a e\<le> b"
                  by (smt (verit, best) F \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> pareto_sup P g'\<close> \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g' \<in> F g' \<and> e_index' g' e\<le> e_index g'\<close> \<open>pareto_sup P \<in> possible_pareto\<close> \<open>weight g g' \<noteq> None\<close> assms energy_leq.strict_trans1 mem_Collect_eq pareto_order_def pareto_sup_is_sup(2) possible_pareto_def)                
              qed
              show "\<And>a. a \<in> {inv_upd (the (weight g g')) (e_index' g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
                    length a = dimension"
              proof-
                fix a 
                assume "a \<in> {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None}"
                from this obtain g' where "a=inv_upd (the (weight g g')) (e_index' g')" and "weight g g' \<noteq> None" by auto
                hence "e_index' g'\<in> F g'" using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g' \<and> e_index' g' e\<le> e_index g'\<close>
                  by simp
                hence "length (e_index' g') = dimension" using \<open>F \<in> possible_pareto\<close> possible_pareto_def
                  by blast 
                thus "length a = dimension" using \<open>a=inv_upd (the (weight g g')) (e_index' g')\<close>  len_inv_appl \<open>weight g g' \<noteq> None\<close> by blast
              qed
            qed
          qed
          hence leq: "energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None} e\<le> e"
            using \<open>e= energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}\<close> by simp

          have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g'" using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g'\<in> F g' \<and> e_index' g' e\<le> e_index g'\<close>
            by simp
          hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> length (e_index' g') = dimension" using \<open>F \<in> possible_pareto\<close> possible_pareto_def
            by blast 
          hence "(energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None}) \<in> {energy_sup dimension
            {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} |
           e_index.
           \<forall>g'. weight g g' \<noteq> None \<longrightarrow> length (e_index g') = dimension \<and> e_index g' \<in> F g'}"
            using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index' g' \<in> F g' \<and> e_index' g' e\<le> e_index g'\<close> by auto
          hence "\<exists>e'. e' \<in> iteration F g \<and> e' e\<le> (energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None})"
            unfolding iteration_def using energy_Min_contains_smaller False
            by meson 
          from this obtain e' where E': "e' \<in> iteration F g \<and> e' e\<le> (energy_sup dimension {inv_upd (the (weight g g')) (e_index' g')| g'. weight g g' \<noteq> None})"
            by auto
          hence "e' \<in> {(e::energy). (\<exists>F. F\<in> {iteration F |F. F \<in> P} \<and>  e\<in> (F g))}" using F by auto 

          hence "\<exists>a. a \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> a e\<le> e'"
            unfolding pareto_sup_def using energy_Min_contains_smaller by meson
          from this obtain a where "a \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> a e\<le> e'" by auto
          hence "a e\<le> e" using E' leq
            using energy_leq.trans by blast 
          then show ?thesis using \<open>a \<in> pareto_sup {iteration F |F. F \<in> P} g \<and> a e\<le> e'\<close> by auto
        qed
      qed
    qed
  qed
  
  show "pareto_sup {iteration F |F. F \<in> P} \<preceq> iteration (pareto_sup P)"
  proof(rule pareto_sup_is_sup(3))
    show "{iteration F |F. F \<in> P} \<subseteq> possible_pareto" using B by simp
    show "iteration (pareto_sup P) \<in> possible_pareto" using A by simp
    show "\<And>F. F \<in> {iteration F |F. F \<in> P} \<Longrightarrow> F \<preceq> iteration (pareto_sup P)"
    proof-
      fix F
      assume "F \<in> {iteration F |F. F \<in> P}"
      from this obtain F' where "F = iteration F'" and "F' \<in> P" by auto
      hence "F' \<preceq> pareto_sup P" using pareto_sup_is_sup
        by (simp add: assms)
      thus "F \<preceq> iteration (pareto_sup P)" using \<open>F = iteration F'\<close> iteration_monotonic assms
        by (simp add: \<open>F' \<in> P\<close> \<open>pareto_sup P \<in> possible_pareto\<close> subsetD) 
    qed
  qed
qed

lemma iteration_scott_continuous: 
  shows "scott_continuous possible_pareto (\<preceq>) possible_pareto (\<preceq>) iteration"
proof
  show "iteration ` possible_pareto \<subseteq> possible_pareto"
    using iteration_pareto_functor
    by blast 
  show "\<And>X s. directed_set X (\<preceq>) \<Longrightarrow>
           X \<noteq> {} \<Longrightarrow>
           X \<subseteq> possible_pareto \<Longrightarrow>
           extreme_bound possible_pareto (\<preceq>) X s \<Longrightarrow>
           extreme_bound possible_pareto (\<preceq>) (iteration ` X) (iteration s)"
  proof-
    fix P s
    assume A1: "directed_set P (\<preceq>)" and A2: "P \<noteq> {}" and A3: "P \<subseteq> possible_pareto" and
           A4: "extreme_bound possible_pareto (\<preceq>) P s"
    hence A4: "s = pareto_sup P" unfolding extreme_bound_def using pareto_sup_is_sup
      by (metis (no_types, lifting) A4 antisymmetry extreme_bound_iff)

    from A1 have A1: "\<And>F F'. F \<in> P \<Longrightarrow> F' \<in> P \<Longrightarrow> \<exists>F''. F'' \<in> P \<and> F \<preceq> F'' \<and> F' \<preceq> F''" 
      unfolding directed_set_def
      by (metis A1 directedD2) 

    hence "iteration s = pareto_sup {iteration F |F. F \<in> P}" 
      using iteration_scott_continuous_vanilla A2 A3 A4 finite_positions
      by blast 

    show "extreme_bound possible_pareto (\<preceq>) (iteration ` P) (iteration s)"
      unfolding \<open>iteration s = pareto_sup {iteration F |F. F \<in> P}\<close> extreme_bound_def
    proof
      have A3: "{iteration F |F. F \<in> P} \<subseteq> possible_pareto" 
        using iteration_pareto_functor A3
        by auto 

      thus "pareto_sup {iteration F |F. F \<in> P} \<in> {b \<in> possible_pareto. bound (iteration ` P) (\<preceq>) b}"
      using pareto_sup_is_sup
      by (simp add: Setcompr_eq_image bound_def)

      show "\<And>x. x \<in> {b \<in> possible_pareto. bound (iteration ` P) (\<preceq>) b} \<Longrightarrow>
         pareto_sup {iteration F |F. F \<in> P} \<preceq> x"
        using A3 pareto_sup_is_sup
        by (smt (verit, del_insts) bound_def image_eqI mem_Collect_eq)
    qed
  qed
qed

text\<open>We now show that \<open>a_win_min\<close> is a fixed point of \<open>iteration\<close>.\<close>

lemma a_win_min_is_fp:
  shows "iteration a_win_min = a_win_min"
proof
  
  have  minimal_winning_budget_attacker: "\<And>g e. g \<in> attacker \<Longrightarrow> minimal_winning_budget e g = (e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))})"
  proof-
    fix g e 
    assume "g \<in> attacker" \<open>g \<in> attacker\<close>
    have attacker_inv_in_winning_budget: "\<And>g g' e'. g \<in> attacker \<Longrightarrow> weight g g' \<noteq> None \<Longrightarrow> winning_budget_len e' g' \<Longrightarrow> winning_budget_len (inv_upd (the (weight g g')) e') g"
    proof-
      fix g g' e' 
      assume A1: "g \<in> attacker" and A2: " weight g g' \<noteq> None" and A3: "winning_budget_len e' g'"
      show "winning_budget_len (inv_upd (the (weight g g')) e') g"
      proof
        from A3 have "length e' = dimension" using winning_budget_len.simps
          by blast
        show "length (the (inverse_application (the (weight g g')) e')) = dimension \<and> g \<in> attacker \<and>
           (\<exists>g'a. weight g g'a \<noteq> None \<and>
           application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')) \<noteq> None \<and>
           winning_budget_len (the (application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')))) g'a) "
        proof
          show "length (the (inverse_application (the (weight g g')) e')) = dimension" using \<open>length e' = dimension\<close> A2
            by (simp add: len_inv_appl)
          show "g \<in> attacker \<and>
           (\<exists>g'a. weight g g'a \<noteq> None \<and>
           application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')) \<noteq> None \<and>
           winning_budget_len (the (application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')))) g'a) "
          proof
            show "g \<in> attacker" using A1 .
            show "\<exists>g'a. weight g g'a \<noteq> None \<and>
          application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')) \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g'a)) (the (inverse_application (the (weight g g')) e')))) g'a"
            proof
              show "weight g g' \<noteq> None \<and>
                application (the (weight g g')) (the (inverse_application (the (weight g g')) e')) \<noteq> None \<and>
                winning_budget_len (the (application (the (weight g g')) (the (inverse_application (the (weight g g')) e')))) g'"
              proof
                show "weight g g' \<noteq> None" using A2 .
                show "application (the (weight g g')) (the (inverse_application (the (weight g g')) e')) \<noteq> None \<and>
                    winning_budget_len (the (application (the (weight g g')) (the (inverse_application (the (weight g g')) e')))) g'"
                proof 
                  from A1 A2 show "application (the (weight g g')) (the (inverse_application (the (weight g g')) e')) \<noteq> None" using domain_inv
                    by (simp add: \<open>length e' = dimension\<close>) 
                  have "energy_leq e' (the (application (the (weight g g')) (the (inverse_application (the (weight g g')) e'))))" using leq_up_inv
                    using A2 \<open>length e' = dimension\<close> by blast 
                  thus "winning_budget_len (the (application (the (weight g g')) (the (inverse_application (the (weight g g')) e')))) g'" using  upwards_closure_wb_len
                    using A3 by auto 
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    have min_winning_budget_is_inv_a: "\<And>e g. g \<in> attacker \<Longrightarrow> minimal_winning_budget e g \<Longrightarrow> \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e = (inv_upd (the (weight g g')) e')"
    proof-
      fix e g
      assume A1: "g \<in> attacker" and A2: " minimal_winning_budget e g"
      show "\<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e = (inv_upd (the (weight g g')) e')"
      proof-
        from A1 A2 have "winning_budget_len e g" using energy_Min_def by simp
        hence \<open>length e = dimension\<close> using winning_budget_len.simps by blast
        from A1 A2 \<open>winning_budget_len e g\<close> have " (\<exists>g'. (weight g g' \<noteq> None) \<and> (application (the (weight g g')) e)\<noteq> None \<and> (winning_budget_len (the (application (the (weight g g')) e)) g') )" 
          using winning_budget_len.simps
          by blast 
        from this obtain g' where G: "(weight g g' \<noteq> None) \<and> (application (the (weight g g')) e)\<noteq> None \<and> (winning_budget_len (the (application (the (weight g g')) e)) g')" by auto
        hence "length (the (application (the (weight g g')) e)) = dimension"
          using \<open>length e = dimension\<close> len_appl by blast 
        hence W: "winning_budget_len (the (inverse_application (the (weight g g')) (the (application (the (weight g g')) e)))) g" using G attacker_inv_in_winning_budget
          by (meson A1)
        have "energy_leq (the (inverse_application (the (weight g g')) (the (application (the (weight g g')) e)))) e" using inv_up_leq
          using G
          using \<open>length e = dimension\<close> by blast
        hence E: "e = (the (inverse_application (the (weight g g')) (the (application (the (weight g g')) e))))" using W A1 A2 energy_Min_def
          by auto 
        show ?thesis 
        proof
          show "\<exists>e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e = the (inverse_application (the (weight g g')) e') "
          proof
            show "weight g g' \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) e)) g' \<and> e = the (inverse_application (the (weight g g')) (the (application (the (weight g g')) e)))" 
              using G E by simp 
          qed
        qed
      qed
    qed

    have min_winning_budget_a_iff_energy_Min: "minimal_winning_budget e g
    \<longleftrightarrow> e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e=(inv_upd (the (weight g g')) e')}"
    proof-
      have len: "\<And>e. e\<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))} \<Longrightarrow> length e = dimension"
      proof-
        fix e
        assume "e\<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}"
        hence "\<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))" by auto
        from this obtain g' e' where eg: "weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))" by auto
        hence "weight g g' \<noteq> None" by auto
        from eg have "length e' = dimension" using winning_budget_len.simps by blast 
        thus "length e = dimension" using eg \<open>length e' = dimension\<close>
          using len_inv_appl by blast
      qed

      show ?thesis 
      proof
        assume "minimal_winning_budget e g"
        hence A: "winning_budget_len e g \<and> (\<forall>e'. e' \<noteq> e \<longrightarrow> e' e\<le> e \<longrightarrow> \<not> winning_budget_len e' g)" using energy_Min_def by auto
        hence E: "e\<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}" 
          using min_winning_budget_is_inv_a \<open>g \<in> attacker\<close>
          by (simp add: \<open>minimal_winning_budget e g\<close>) 

        have "\<And>x. x \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))} \<and> energy_leq x e \<Longrightarrow> e=x"
        proof-
          fix x 
          assume X: "x \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))} \<and> energy_leq x e"
          have "winning_budget_len x g" 
          proof
            show "length x = dimension \<and>
              g \<in> attacker \<and>
              (\<exists>g'. weight g g' \<noteq> None \<and>
            application (the (weight g g')) x \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) x)) g')"
            proof
              show "length x = dimension" using len X by blast
              show "g \<in> attacker \<and>
                (\<exists>g'. weight g g' \<noteq> None \<and>
                application (the (weight g g')) x \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) x)) g')"                         
              proof
                show "g \<in> attacker" using \<open>g \<in> attacker\<close>.

                from X have "\<exists>g' e'.
              weight g g' \<noteq> None \<and>
              winning_budget_len e' g' \<and> x = inv_upd (the (weight g g')) e'"
                  by blast
                from this obtain g' e' where X: "weight g g' \<noteq> None \<and>
              winning_budget_len e' g' \<and> x = inv_upd (the (weight g g')) e'" by auto

                show "\<exists>g'. weight g g' \<noteq> None \<and>
         apply_w g g' x \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) x) g'"
                proof
                  show "weight g g' \<noteq> None \<and>
         apply_w g g' x \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) x) g'"
                  proof
                    show "weight g g' \<noteq> None" using X by simp
                    show "apply_w g g' x \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) x) g'"
                    proof

                      have "e' e\<le> (upd (the (weight g g')) x)" 
                        using X leq_up_inv 
                        by (metis winning_budget_len.simps)
                      have "winning_budget_len (inv_upd (the (weight g g')) e') g"
                        using X attacker_inv_in_winning_budget \<open>weight g g' \<noteq> None\<close> \<open>g \<in> attacker\<close>
                        by blast
                      thus "winning_budget_len (upd (the (weight g g')) x) g'"
                        using \<open>e' e\<le> (upd (the (weight g g')) x)\<close> upwards_closure_wb_len X by blast

                      have "inverse_application (the (weight g g')) e' \<noteq> None" 
                        using domain_inv  \<open>weight g g' \<noteq> None\<close>
                        by (metis X winning_budget_len.simps)
                      thus "apply_w g g' x \<noteq> None"
                        using X domain_inv
                        using nonpos_eq_pos winning_bugget_len_is_wb by blast 
                    qed
                  qed
                qed
              qed
            qed
          qed
          thus "e=x" using X A 
            by metis 
        qed
        thus "e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}"
          using E energy_Min_def
          by (smt (verit, del_insts) mem_Collect_eq) 
      next
        assume "e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}"
        hence E: "e \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}"
          using energy_Min_def by auto
        have "winning_budget_len e g \<and> (\<forall>e'. e' \<noteq> e \<longrightarrow> energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g)"
        proof
          show W: "winning_budget_len e g" using len E \<open>g \<in> attacker\<close> winning_budget_len.intros
            by (smt (verit, ccfv_SIG) attacker_inv_in_winning_budget mem_Collect_eq)

          from W have "e\<in> {e''. energy_leq e'' e \<and> winning_budget_len e'' g}" using energy_leq.refl by simp
          hence notempty: "{} \<noteq> {e''. energy_leq e'' e \<and> winning_budget_len e'' g}" by auto
          have "\<And>e''. e'' \<in> {e''. energy_leq e'' e \<and> winning_budget_len e'' g} \<Longrightarrow> length e'' = dimension" 
            using winning_budget_len.simps by blast
          hence "{} \<noteq> energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g}" using energy_Min_not_empty notempty 
            by (smt (verit, ccfv_threshold) emptyE mem_Collect_eq)
          hence "\<exists>e''. e'' \<in> energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g}" by auto
          from this obtain e'' where "e'' \<in> energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g}" by auto
          hence X: "energy_leq e'' e \<and> winning_budget_len e'' g \<and> (\<forall>e'. e'\<in> {e''. energy_leq e'' e \<and> winning_budget_len e'' g} \<longrightarrow> e'' \<noteq> e' \<longrightarrow> \<not> energy_leq e' e'')"
            using energy_Min_def by simp

          have "(\<forall>e' \<noteq> e''. energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g)" 
          proof
            fix e'
            show " e' \<noteq> e'' \<longrightarrow> energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g"
            proof
              assume " e' \<noteq> e''"
              show "energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g"
              proof
                assume " energy_leq e' e''"
                hence "length e' = dimension " using energy_leq_def X
                  using \<open>\<And>e''. e'' \<in> {e''. energy_leq e'' e \<and> winning_budget_len e'' g} \<Longrightarrow> length e'' = dimension\<close> by blast
                from \<open>energy_leq e' e''\<close> have "energy_leq e' e" using X energy_leq.trans by blast
                show "\<not> winning_budget_len e' g"
                proof
                  assume "winning_budget_len e' g"
                  hence "e'\<in>{e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension}" using \<open>length e' = dimension\<close> \<open>energy_leq e' e\<close> by auto
                  hence "\<not> energy_leq e' e''" using X \<open>e' \<noteq> e''\<close> by simp
                  thus "False" using \<open>energy_leq e' e''\<close> by simp
                qed
              qed
            qed
          qed
          hence E: "energy_leq e'' e \<and> winning_budget_len e'' g \<and> (\<forall>e' \<noteq> e''. energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g)" using X
            by meson 
          hence "energy_leq e'' e \<and> minimal_winning_budget e'' g" using energy_Min_def by auto
          hence "\<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e''=(the (inverse_application (the (weight g g')) e'))" 
            using min_winning_budget_is_inv_a X \<open>g \<in> attacker\<close> by simp
          hence "e'' \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}" by auto
          hence "e=e''" using \<open>g \<in> attacker\<close> X energy_Min_def E
            by (smt (verit, best) \<open>e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e = the (inverse_application (the (weight g g')) e')}\<close> mem_Collect_eq)
          thus "(\<forall>e'. e' \<noteq> e \<longrightarrow> energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g)" using E by auto
        qed
        thus "minimal_winning_budget e g" using energy_Min_def by auto
      qed
    qed

    have min_winning_budget_is_minimal_inv_a: "\<And>e g. g \<in> attacker \<Longrightarrow> minimal_winning_budget e g \<Longrightarrow> \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(inv_upd (the (weight g g')) e')"
    proof-
      fix e g 
      assume A1: "g \<in> attacker" and A2: "minimal_winning_budget e g"
      show "\<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(inv_upd (the (weight g g')) e')"
      proof-
        from A1 A2 have "winning_budget_len e g" using energy_Min_def by simp
        from A1 A2 have "\<forall>e' \<noteq> e. energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g" using energy_Min_def
          using mem_Collect_eq by auto 
        hence "\<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))"
          using min_winning_budget_is_inv_a A1 A2 \<open>winning_budget_len e g\<close> by auto
        from this obtain g' e' where G: "weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))" by auto
        hence "e' \<in> {e. winning_budget_len e g' \<and> energy_leq e e'}" using energy_leq.refl by auto
        have "\<And>e'. e' \<in> {e. winning_budget_len e g' \<and> energy_leq e e'} \<Longrightarrow> length e' = dimension" using winning_budget_len.simps by blast
        hence "energy_Min {e. winning_budget_len e g' \<and> energy_leq e e'} \<noteq> {}" using \<open>e' \<in> {e. winning_budget_len e g' \<and> energy_leq e e'}\<close> energy_Min_not_empty
          by (metis (no_types, lifting) empty_iff mem_Collect_eq winning_budget_len.cases)
        hence "\<exists>e''. e'' \<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e e'}" by auto
        from this obtain e'' where "e'' \<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e e'}" by auto
        hence "minimal_winning_budget e'' g'" using energy_Min_def
          by (smt (verit, del_insts) energy_leq.strict_trans1 mem_Collect_eq) 

        have "energy_leq e'' e'" using \<open>e'' \<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e e'}\<close> energy_Min_def by auto
        hence "energy_leq (the (inverse_application (the (weight g g')) e'')) (the (inverse_application (the (weight g g')) e'))" 
          using inverse_monotonic
          using G domain_inv energy_leq_def nonpos_eq_pos winning_bugget_len_is_wb by auto
        hence "energy_leq (the (inverse_application (the (weight g g')) e'')) e" using G by auto
        hence "e=(the (inverse_application (the (weight g g')) e''))" using \<open>minimal_winning_budget e'' g'\<close> \<open>\<forall>e' \<noteq> e. energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g\<close>
          by (metis (no_types, lifting) G A1 attacker_inv_in_winning_budget energy_Min_def mem_Collect_eq)
        thus ?thesis using G \<open>minimal_winning_budget e'' g'\<close> by auto
      qed
    qed

    show "minimal_winning_budget e g = (e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))})"
    proof
      assume "minimal_winning_budget e g"
      show "(e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))})"
      proof-
        from \<open>g \<in> attacker\<close> have exist: "\<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e = inv_upd (the (weight g g')) e'"
          using \<open>minimal_winning_budget e g\<close> min_winning_budget_is_minimal_inv_a by simp
        have "\<And>e''. e'' e\<le> e \<and> e \<noteq> e'' \<Longrightarrow> e'' \<notin> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))}"
        proof-
          fix e''
          show "e'' e\<le> e \<and> e \<noteq> e'' \<Longrightarrow> e'' \<notin> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))}"
          proof-
            assume "e'' e\<le> e \<and> e \<noteq> e'' "
            show "e'' \<notin> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))}"
            proof
              assume "e'' \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))}"
              hence "\<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e''=(the (inverse_application (the (weight g g')) e'))"
                by auto
              from this obtain g' e' where EG: "weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e''=(the (inverse_application (the (weight g g')) e'))" by auto
              hence "winning_budget_len e' g'" using energy_Min_def by simp
              hence "winning_budget_len e'' g" using EG winning_budget_len.simps
                by (metis \<open>g \<in> attacker\<close> attacker_inv_in_winning_budget) 
              then show "False" using \<open>e'' e\<le> e \<and> e \<noteq> e''\<close> \<open>minimal_winning_budget e g\<close> energy_Min_def by auto
            qed
          qed
        qed
        thus "(e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))})" 
          using exist energy_Min_def
          by (smt (verit) mem_Collect_eq) 
      qed
    next
      assume emin: "(e \<in> energy_Min {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g' \<and> e=(the (inverse_application (the (weight g g')) e'))})"
      show "minimal_winning_budget e g"
      proof-
        from emin have "\<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))" using energy_Min_def by auto
        hence  "\<exists>g' e'. weight g g' \<noteq> None \<and> winning_budget_len e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))" using energy_Min_def
          by (metis (no_types, lifting) mem_Collect_eq)
        hence element_of: "e\<in>{e. \<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e = inv_upd (the (weight g g')) e'}" by auto

        have "\<And>e''. e'' e< e \<Longrightarrow> e'' \<notin> {e. \<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e = inv_upd (the (weight g g')) e'}"
        proof
          fix e''
          assume "e'' e< e"
          assume "e'' \<in> {e. \<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e = inv_upd (the (weight g g')) e'}"
          hence "\<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e'' = inv_upd (the (weight g g')) e'" by auto
          from this obtain g' e' where E'G': "weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e'' = inv_upd (the (weight g g')) e'" by auto
          hence "e' \<in> {e. winning_budget_len e g'}" by simp
          hence "\<exists>e_min. minimal_winning_budget e_min g' \<and> e_min e\<le> e'" 
            using energy_Min_contains_smaller by meson
          from this obtain e_min where "minimal_winning_budget e_min g' \<and> e_min e\<le> e'" by auto
          have "inv_upd (the (weight g g')) e_min e\<le> inv_upd (the (weight g g')) e'" 
          proof(rule inverse_monotonic)
            show "weight g g' \<noteq> None"           
              using \<open>weight g g' \<noteq> None \<and> winning_budget_len e' g' \<and> e'' = inv_upd (the (weight g g')) e'\<close> by simp
            show "e_min e\<le> e'" using \<open>minimal_winning_budget e_min g' \<and> e_min e\<le> e'\<close>
              by auto
            hence "length e_min = dimension" using winning_budget_len.simps
              by (metis E'G' energy_leq_def)
            thus " inverse_application (the (weight g g')) e_min \<noteq> None"
              using domain_inv \<open>weight g g' \<noteq> None\<close> by auto
            show "length e_min = dimension"
              by (simp add: \<open>length e_min = dimension\<close>) 
          qed
          hence "inv_upd (the (weight g g')) e_min e< e" using \<open>e'' e< e\<close> E'G'
            using energy_leq.trans
            by (metis energy_leq.asym)

          have "inv_upd (the (weight g g')) e_min \<in> {e. \<exists>g' e'. weight g g' \<noteq> None \<and> minimal_winning_budget e' g'  \<and> e=(the (inverse_application (the (weight g g')) e'))}" 
            using \<open>minimal_winning_budget e_min g' \<and> e_min e\<le> e'\<close> E'G'
            by blast
          thus "False" using \<open>inv_upd (the (weight g g')) e_min e< e\<close> energy_Min_def emin
            by (smt (verit) mem_Collect_eq)    
        qed

        hence "e \<in> energy_Min
            {e. \<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   winning_budget_len e' g' \<and> e = inv_upd (the (weight g g')) e'}" 
          using energy_Min_def element_of 
          by (smt (verit, ccfv_threshold) mem_Collect_eq)
        then show ?thesis using min_winning_budget_a_iff_energy_Min \<open>g \<in> attacker\<close> by simp
      qed
    qed
  qed


  have minimal_winning_budget_defender: "\<And>g e. g \<notin> attacker \<Longrightarrow> minimal_winning_budget e g = (e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})})"
  proof-
    fix g e
    assume "g \<notin> attacker"
    have sup_inv_in_winning_budget: "\<And>(strat:: 'position \<Rightarrow> energy) g. g\<notin>attacker \<Longrightarrow> \<forall>g'.  weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g' } \<Longrightarrow> winning_budget_len (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None}) g"
    proof-
      fix strat g 
      assume A1: "g\<notin>attacker" and "\<forall>g'.  weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g' }"
      hence A2: " \<And>g'.  weight g g' \<noteq> None \<Longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g' }"
        by simp
      show "winning_budget_len (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None}) g"
      proof (rule winning_budget_len.intros(1))
        have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}))) g') " 
        proof
          fix g'
          show "weight g g' \<noteq> None \<longrightarrow>
          application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}))) g'"
          proof
            assume "weight g g' \<noteq> None"
            hence "strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g' }" using A2 by simp
            hence "\<exists>e. strat g' = the (inverse_application (the (weight g g')) e) \<and> winning_budget_len e g'" by blast
            from this obtain e where E: "strat g' = the (inverse_application (the (weight g g')) e) \<and> winning_budget_len e g'" by auto

            hence "length e = dimension" using winning_budget_len.simps by blast
            hence "inverse_application (the (weight g g')) e \<noteq> None" using domain_inv  \<open>weight g g' \<noteq> None\<close> by simp

            have leq: "energy_leq (strat g') (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None})" using energy_sup_in \<open>weight g g' \<noteq> None\<close>
              by (metis (mono_tags, lifting) E \<open>length e = dimension\<close> len_inv_appl mem_Collect_eq ) 

            show "application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) \<noteq> None \<and>
            winning_budget_len (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}))) g'"
            proof
              have "application (the (weight g g')) (strat g') = application (the (weight g g')) (the (inverse_application (the (weight g g')) e))" using E
                by simp
              also have "... \<noteq> None" using \<open>inverse_application (the (weight g g')) e \<noteq> None\<close> domain_inv
                using \<open>length e = dimension\<close> \<open>weight g g' \<noteq> None\<close> by presburger
              finally have "application (the (weight g g')) (strat g') \<noteq> None" .
              thus "application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) \<noteq> None" 
                using leq domain_upw_closed
                using \<open>weight g g' \<noteq> None\<close> by blast  

              have "energy_leq e (the (application (the (weight g g')) (strat g')))" using leq_up_inv 
                by (metis \<open>application (the (weight g g')) (strat g') = application (the (weight g g')) (the (inverse_application (the (weight g g')) e))\<close> \<open>length e = dimension\<close> \<open>weight g g' \<noteq> None\<close>) 
              hence W: "winning_budget_len (the (application (the (weight g g')) (strat g'))) g'" using E upwards_closure_wb_len
                by blast
              have "energy_leq (the (application (the (weight g g')) (strat g'))) (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None})))" 
                using updates_monotonic 
                by (smt (verit, del_insts) Collect_cong E \<open>application (the (weight g g')) (strat g') \<noteq> None\<close> \<open>length e = dimension\<close> \<open>weight g g' \<noteq> None\<close> len_inv_appl leq)
              thus "winning_budget_len (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}))) g'" 
                using W upwards_closure_wb_len by blast
            qed
          qed
        qed

        thus "length (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) = dimension \<and> g \<notin> attacker \<and>
          (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) \<noteq> None \<and>
          winning_budget_len (the (application (the (weight g g')) (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}))) g') "
          using A1 energy_sup_def
          by (simp add: Ex_list_of_length length_map map_nth)
      qed
    qed

    have min_winning_budget_is_inv_d: "\<And>e g. g\<notin>attacker \<Longrightarrow> minimal_winning_budget e g \<Longrightarrow> \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
    proof-
      fix e g 
      assume A1: "g\<notin>attacker" and A2: " minimal_winning_budget e g"
      show "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
      proof-
        from A2 have "length e =dimension" using winning_budget_len.simps energy_Min_def
          by (metis (no_types, lifting) mem_Collect_eq) 
        from A1 A2 have W: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                  application (the (weight g g')) e \<noteq> None \<and>
                  winning_budget_len (the (application (the (weight g g')) e)) g')" using winning_budget_len.simps energy_Min_def
          by (metis (no_types, lifting) mem_Collect_eq) 

        define strat where S: "\<forall>g'.  strat g' = the ((inverse_application (the (weight g g'))) (the (application (the (weight g g')) e)))"
        have A: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'})" 
        proof
          fix g'
          show "weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}" 
          proof
            assume "weight g g' \<noteq> None"
            hence "winning_budget_len (the (application (the (weight g g')) e)) g'" using W by auto
            thus "strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}" using S by blast
          qed
        qed
        hence W: "winning_budget_len (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) g" using sup_inv_in_winning_budget A1 by simp
        have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> energy_leq (strat g') e" 
        proof-
          fix g'
          assume "weight g g' \<noteq> None"
          hence "application (the (weight g g')) e \<noteq> None" using W
            using A1 A2 winning_budget_len.cases energy_Min_def
            by (metis (mono_tags, lifting) mem_Collect_eq) 
          from \<open>weight g g' \<noteq> None\<close> have "strat g' = the ((inverse_application (the (weight g g'))) (the (application (the (weight g g')) e)))" using S by auto
          thus "energy_leq (strat g') e" using inv_up_leq  \<open>application (the (weight g g')) e \<noteq> None\<close>
            using \<open>length e = dimension\<close> \<open>weight g g' \<noteq> None\<close> by presburger
        qed
        hence "energy_leq (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) e" using energy_sup_leq \<open>length e =dimension\<close>
          by (smt (verit) mem_Collect_eq) 
        hence "e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" using W A1 A2 energy_Min_def
          by force 
        thus ?thesis using A by blast
      qed
    qed


    have  min_winning_budget_d_iff_energy_Min: "\<And>e g. g\<notin>attacker \<Longrightarrow> length e = dimension \<Longrightarrow> ((e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {inv_upd (the (weight g g')) e | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})})
        \<longleftrightarrow> minimal_winning_budget e g)"
    proof-
      fix e g
      show "g \<notin> attacker \<Longrightarrow>
           length e = dimension \<Longrightarrow>
           (e \<in> energy_Min
                  {e''.
                   \<exists>strat.
                      (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                            strat g'
                            \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                      e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}) =
           minimal_winning_budget e g"
      proof-
        assume A1: "g \<notin> attacker" and A2: "length e = dimension"
        show "(e \<in> energy_Min
                  {e''.
                   \<exists>strat.
                      (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                            strat g'
                            \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                      e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}) =
           minimal_winning_budget e g"
        proof
          assume assumption: "e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
          show "minimal_winning_budget e g" 
            unfolding energy_Min_def 
          proof
            show "e \<in> {e. winning_budget_len e g} \<and> (\<forall>e'\<in>{e. winning_budget_len e g}. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e)"
            proof
              show "e \<in> {e. winning_budget_len e g}" 
              proof
                from A1 A2 assumption have "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" 
                  using energy_Min_def by simp
                thus "winning_budget_len e g" using sup_inv_in_winning_budget A1 A2 by blast
              qed
              hence W: "winning_budget_len e g" by simp
              hence "length e = dimension" using winning_budget_len.simps by blast
              hence "e\<in> {e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension}" using W energy_leq.refl \<open>g \<notin> attacker\<close> by simp
              hence "{e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension} \<noteq> {}" by auto
              hence "energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension} \<noteq> {}" using energy_Min_not_empty
                by (metis (mono_tags, lifting) mem_Collect_eq) 
              hence "\<exists>e''. e'' \<in> energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension}" by auto
              from this obtain e'' where "e'' \<in> energy_Min {e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension}" by auto
              hence X: "energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension 
                      \<and> ( \<forall>e'. e'\<in>{e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension }\<longrightarrow> e'' \<noteq> e' \<longrightarrow> \<not> energy_leq e' e'')" using energy_Min_def
                by simp
              have "(\<forall>e' \<noteq> e''. energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g)" 
              proof
                fix e'
                show " e' \<noteq> e'' \<longrightarrow> energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g"
                proof
                  assume " e' \<noteq> e''"
                  show "energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g"
                  proof
                    assume " energy_leq e' e''"
                    hence "length e' = dimension " using energy_leq_def X by auto
                    from \<open>energy_leq e' e''\<close> have "energy_leq e' e" using X energy_leq.trans by blast
                    show "\<not> winning_budget_len e' g"
                    proof
                      assume "winning_budget_len e' g"
                      hence "e'\<in>{e''. energy_leq e'' e \<and> winning_budget_len e'' g \<and> length e'' = dimension}" using \<open>length e' = dimension\<close> \<open>energy_leq e' e\<close> by auto
                      hence "\<not> energy_leq e' e''" using X \<open>e' \<noteq> e''\<close> by simp
                      thus "False" using \<open>energy_leq e' e''\<close> by simp
                    qed
                  qed
                qed
              qed
              hence "energy_leq e'' e \<and> winning_budget_len e'' g \<and> (\<forall>e' \<noteq> e''. energy_leq e' e'' \<longrightarrow> \<not> winning_budget_len e' g)" using X
                by meson
              hence E: "energy_leq e'' e \<and> minimal_winning_budget e'' g" using energy_Min_def
                by (smt (verit) mem_Collect_eq) 
              hence "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" 
                using min_winning_budget_is_inv_d 
                by (simp add: X A1) 
              hence "e=e''" using assumption X energy_Min_def by auto 
              thus "(\<forall>e'\<in>{e. winning_budget_len e g}. e \<noteq> e' \<longrightarrow> \<not> e' e\<le> e)" using E
                using \<open>\<forall>e'. e' \<noteq> e'' \<longrightarrow> e' e\<le> e'' \<longrightarrow> \<not> winning_budget_len e' g\<close> by fastforce
            qed
          qed
        next
          assume assumption: "minimal_winning_budget e g" 
          show "e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
            unfolding energy_Min_def 
          proof
            from assumption have "length e = dimension" using winning_budget_len.simps energy_Min_def
              using A2 by blast
            show "e \<in> {e''.
          \<exists>strat.
             (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                   strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
             e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}} \<and>
          (\<forall>e'\<in>{e''.
           \<exists>strat.
              (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                    strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
              e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}.
          e \<noteq> e' \<longrightarrow> \<not> energy_leq e' e)"
            proof
              from A1 A2 assumption have "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" using min_winning_budget_is_inv_d by simp
              thus "e \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}" by auto
              show " \<forall>e'\<in>{e''.
          \<exists>strat.
             (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                   strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
             e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}.
       e \<noteq> e' \<longrightarrow> \<not> energy_leq e' e"
              proof
                fix e'
                assume "e' \<in> {e''.
                \<exists>strat.
                   (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                         strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
                   e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}"
                hence "\<exists>strat.
                   (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                         strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
                   e' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" by auto
                from this obtain strat where S: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                         strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}) \<and>
                   e' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" by auto
                hence "length e'  = dimension" using energy_sup_def 
                  by (simp add: length_map) 
                show "e \<noteq> e' \<longrightarrow> \<not> energy_leq e' e "
                proof
                  assume "e \<noteq> e'"
                  have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
            application (the (weight g g')) e' \<noteq> None \<and>
            winning_budget_len (the (application (the (weight g g')) e')) g')" 
                  proof
                    fix g'
                    show "weight g g' \<noteq> None \<longrightarrow>
              application (the (weight g g')) e' \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) e')) g' "
                    proof
                      assume "weight g g' \<noteq> None"
                      hence "strat g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'}" using S by auto
                      hence "\<exists>e''. strat g'= the (inverse_application (the (weight g g')) e'') \<and> winning_budget_len e'' g'" by auto
                      from this obtain e'' where E: "strat g'= the (inverse_application (the (weight g g')) e'') \<and> winning_budget_len e'' g'" by auto
                      hence "length e''=dimension" using winning_budget_len.simps by blast
                      show "application (the (weight g g')) e' \<noteq> None \<and> winning_budget_len (the (application (the (weight g g')) e')) g' "
                      proof
                        have "energy_leq (strat g') e'" using S energy_sup_in \<open>weight g g' \<noteq> None\<close> 
                          by (smt (verit) E \<open>length e'' = dimension\<close> len_inv_appl mem_Collect_eq)
                        have "application (the (weight g g')) (strat g') \<noteq> None" using E domain_inv domain_inv \<open>length e''=dimension\<close>
                          by (metis \<open>weight g g' \<noteq> None\<close> )
                        thus "application (the (weight g g')) e' \<noteq> None" using domain_upw_closed \<open>energy_leq (strat g') e'\<close>
                          using \<open>weight g g' \<noteq> None\<close> by blast
                        have "energy_leq e'' (the (application (the (weight g g')) (strat g')))" using E leq_up_inv
                          using \<open>length e'' = dimension\<close> \<open>weight g g' \<noteq> None\<close>  by metis
                        hence W: "winning_budget_len (the (application (the (weight g g')) (strat g'))) g'" using upwards_closure_wb_len
                          using E by blast
                        from \<open>energy_leq (strat g') e'\<close> have "energy_leq (the (application (the (weight g g')) (strat g')))  (the (application (the (weight g g')) e'))" 
                          using updates_monotonic  \<open>application (the (weight g g')) (strat g') \<noteq> None\<close>
                          by (smt (verit) Collect_cong E \<open>length e'' = dimension\<close> \<open>weight g g' \<noteq> None\<close> len_inv_appl)
                        thus "winning_budget_len (the (application (the (weight g g')) e')) g' " using upwards_closure_wb_len W
                          by blast 
                      qed
                    qed
                  qed
                  hence "winning_budget_len e' g" using winning_budget_len.intros(1) A1 \<open>length e'  = dimension\<close>
                    by blast
                  thus "\<not> energy_leq e' e " using assumption \<open>e \<noteq> e'\<close> energy_Min_def by auto
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    have  min_winning_budget_is_minimal_inv_d: "\<And>e g. g\<notin>attacker \<Longrightarrow> minimal_winning_budget e g \<Longrightarrow> \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
    proof-
      fix e g
      assume A1: "g\<notin>attacker" and A2: "minimal_winning_budget e g" 
      show "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
      proof-
        from A1 A2 have "winning_budget_len e g" using energy_Min_def by simp
        from A1 A2 have "\<forall>e' \<noteq> e. energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g" using energy_Min_def
          using mem_Collect_eq by auto 

        hence "e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}" 
          using \<open>winning_budget_len e g\<close> A1 A2 min_winning_budget_d_iff_energy_Min
          by (meson winning_budget_len.cases)
        hence " \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" using energy_Min_def by auto

        from this obtain strat where Strat: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" by auto
        define strat_e where "strat_e \<equiv> \<lambda>g'.(SOME e. strat g' = the (inverse_application (the (weight g g')) e) \<and> winning_budget_len e g')"
  
        have Strat_E: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> strat g' = the (inverse_application (the (weight g g')) (strat_e g')) \<and> winning_budget_len (strat_e g') g'"
        proof-
          fix g'
          have Strat_E: "strat_e g' = (SOME e. strat g' = the (inverse_application (the (weight g g')) e) \<and> winning_budget_len e g')" using strat_e_def by simp 
          assume "weight g g' \<noteq> None"
          hence "strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. winning_budget_len e g'}" using Strat by simp
          hence "\<exists>e. strat g' = the (inverse_application (the (weight g g')) e) \<and> winning_budget_len e g'" by auto
          thus "strat g' = the (inverse_application (the (weight g g')) (strat_e g')) \<and> winning_budget_len (strat_e g') g'" 
            using Strat_E by (smt (verit, del_insts) some_eq_ex) 
        qed

        have exists: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}"
        proof-
          fix g'
          assume "weight g g' \<noteq> None "
          hence notempty: "strat_e g' \<in> {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}" using Strat_E energy_leq.refl by auto
          have "\<forall>e \<in> {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}. length e = dimension"
            using winning_budget_len.cases by auto 
          hence "{} \<noteq> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}"
            using energy_Min_not_empty notempty
            by (smt (verit) empty_iff) 
          thus "\<exists>e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}" by auto
        qed

        define strat' where "strat' \<equiv> \<lambda>g'. the (inverse_application (the (weight g g')) (SOME e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}))"
 
        have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat' g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat' g'| g'. weight g g' \<noteq> None})"
        proof
          show win: "\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat' g' \<in> {the (inverse_application (the (weight g g')) e) |e. minimal_winning_budget e g'}"
          proof
            fix g'
            show "weight g g' \<noteq> None \<longrightarrow> strat' g' \<in> {the (inverse_application (the (weight g g')) e) |e. minimal_winning_budget e g'}"
            proof
              assume "weight g g' \<noteq> None"
              hence "strat' g' = the (inverse_application (the (weight g g')) (SOME e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}))"
                using strat'_def by auto
              hence  "\<exists>e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')} \<and> strat' g' = the (inverse_application (the (weight g g')) e)"
                using exists \<open>weight g g' \<noteq> None\<close> some_eq_ex
                by (metis (mono_tags)) 
              from this obtain e where E: "e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')} \<and> strat' g' = the (inverse_application (the (weight g g')) e)" by auto
              hence "minimal_winning_budget e g'" using energy_Min_def
                by (smt (verit) energy_leq.strict_trans1 mem_Collect_eq) 
              thus "strat' g' \<in> {the (inverse_application (the (weight g g')) e) |e. minimal_winning_budget e g'}" using E
                by blast 
            qed
          qed

          have "(\<And>g'. weight g g' \<noteq> None \<Longrightarrow>
           strat' g' \<in> {the (inverse_application (the (weight g g')) e) |e. winning_budget_len e g'})"
            using win energy_Min_def
            by (smt (verit, del_insts) mem_Collect_eq) 
          hence win: "winning_budget_len (energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None}) g" 
            using sup_inv_in_winning_budget A1 A2 by simp

          have "energy_leq (energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None}) (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
          proof(cases " {g'. weight g g' \<noteq> None} = {}")
            case True
            then show ?thesis using energy_sup_def
              using energy_leq.refl by auto
          next
            case False
            show ?thesis 
            proof(rule energy_sup_leq_energy_sup)
              show "{strat' g' |g'. weight g g' \<noteq> None} \<noteq> {}" using False by simp

              have A: "\<And>a. a \<in> {strat' g' |g'. weight g g' \<noteq> None} \<Longrightarrow> \<exists>b\<in>{strat g' |g'. weight g g' \<noteq> None}. energy_leq a b \<and> length a = dimension" 
              proof-
                fix a 
                assume "a \<in>{strat' g' |g'. weight g g' \<noteq> None}"
                hence "\<exists>g'. a = strat' g' \<and> weight g g' \<noteq> None" by auto
                from this obtain g' where "a = strat' g' \<and> weight g g' \<noteq> None" by auto

                have "(strat' g') = (the (inverse_application (the (weight g g'))
                  (SOME e. e \<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')})))" using strat'_def by auto
                hence  "\<exists>e. e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')} \<and> strat' g' = the (inverse_application (the (weight g g')) e)"
                  using exists \<open>a = strat' g' \<and> weight g g' \<noteq> None\<close> some_eq_ex
                  by (metis (mono_tags)) 
                from this obtain e where E: "e\<in> energy_Min {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')} \<and> strat' g' = the (inverse_application (the (weight g g')) e)" by auto
                hence "energy_leq e (strat_e g')" using energy_Min_def by auto

                hence "length a = dimension " using \<open>a = strat' g' \<and> weight g g' \<noteq> None\<close> energy_Min_def
                  by (metis (no_types, lifting) E len_inv_appl mem_Collect_eq winning_budget_len.cases)

                have leq: "energy_leq (the (inverse_application (the (weight g g')) e)) (the (inverse_application (the (weight g g')) (strat_e g')))" 
                proof(rule inverse_monotonic)
                  show "energy_leq e (strat_e g')" using \<open>energy_leq e (strat_e g')\<close>.
                  show "weight g g' \<noteq> None" using \<open>a = strat' g' \<and> weight g g' \<noteq> None\<close> by simp
                  from E have "e\<in> {e. winning_budget_len e g' \<and> energy_leq e (strat_e g')}" using energy_Min_def
                    by auto 
                  hence "winning_budget_len e g'"
                    by simp 
                  thus "length e = dimension"
                    using winning_budget_len.simps
                    by blast 
                  thus "inverse_application (the (weight g g')) e \<noteq> None"
                    using domain_inv \<open>weight g g' \<noteq> None\<close>
                    by simp
                qed
                have "the (inverse_application (the (weight g g')) (strat_e g')) = strat g'" using Strat_E \<open>a = strat' g' \<and> weight g g' \<noteq> None\<close> by auto
                hence "energy_leq (strat' g') (strat g')" using leq E by simp
                hence "\<exists>b\<in>{strat g' |g'. weight g g' \<noteq> None}. energy_leq a b" using \<open>a = strat' g' \<and> weight g g' \<noteq> None\<close> by auto
                thus "\<exists>b\<in>{strat g' |g'. weight g g' \<noteq> None}. energy_leq a b \<and> length a = dimension" using \<open>length a = dimension\<close> by simp
              qed
              thus "\<And>a. a \<in> {strat' g' |g'. weight g g' \<noteq> None} \<Longrightarrow> \<exists>b\<in>{strat g' |g'. weight g g' \<noteq> None}. energy_leq a b" by simp
              show "\<And>a. a \<in> {strat' g' |g'. weight g g' \<noteq> None} \<Longrightarrow> length a = dimension " using A by simp
            qed
          qed
          thus "e = energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None}" using \<open>g \<notin> attacker\<close> Strat win 
            by (metis (no_types, lifting) \<open>\<forall>e'. e' \<noteq> e \<longrightarrow> energy_leq e' e \<longrightarrow> \<not> winning_budget_len e' g\<close>)
        qed
        thus ?thesis by blast
      qed
    qed

    show "minimal_winning_budget e g =
           (e \<in> energy_Min
                  {e''.
                   \<exists>strat.
                      (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                            strat g'
                            \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}) \<and>
                      e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}})"
    proof
      assume "minimal_winning_budget e g"
      hence exist: "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e= (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" 
        using min_winning_budget_is_minimal_inv_d \<open>g \<notin> attacker\<close> by simp
      have "\<And>e''. e'' e< e \<Longrightarrow> \<not> e'' \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
      proof-
        fix e''
        show "e'' e< e \<Longrightarrow> \<not> e'' \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
        proof-
          assume "e'' e< e"
          show "\<not> e'' \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
          proof
            assume "e'' \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
            hence " \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" by auto
            from this obtain strat where E'': "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" by auto
            hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow>
           strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}" using energy_Min_def
              by (smt (verit, del_insts) mem_Collect_eq) 
            hence "winning_budget_len (energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}) g" using sup_inv_in_winning_budget \<open>g \<notin> attacker\<close> by simp
            hence "winning_budget_len e'' g" using E'' by simp
            thus "False" using \<open>e'' e< e\<close> \<open>minimal_winning_budget e g\<close> energy_Min_def by auto
          qed
        qed
      qed
      thus "e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
        using exist energy_Min_def by (smt (verit) mem_Collect_eq)
    next 
      assume A: "(e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})})"
    
      hence emin: "e\<in> energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}" using A by simp
      hence "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})" using energy_Min_def by auto
      hence "\<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" using energy_Min_def
        by (smt (verit, ccfv_threshold) mem_Collect_eq) 
      hence element_of: "e \<in> {e''.
             \<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}" by auto
      hence "length e = dimension"
        using \<open>g \<notin> attacker\<close> sup_inv_in_winning_budget winning_budget_len.simps by blast

      have "\<And>e'. e' e< e \<Longrightarrow> e' \<notin> {e''.
             \<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}"
      proof
        fix e'
        assume "e' e< e"
        assume A: "e' \<in> {e''. \<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}"
        hence "\<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" by auto
        from this obtain strat where Strat: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" by auto

        define the_e where "the_e \<equiv> \<lambda>g'. (SOME x. strat g' = inv_upd (the (weight g g')) x \<and> winning_budget_len x g')"

        define strat' where "strat' \<equiv> \<lambda>g'. (SOME x. x \<in> {inv_upd (the (weight g g')) x| 
                                                        x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')})"

        have some_not_empty: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> {inv_upd (the (weight g g')) x|x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')} \<noteq> {}"
        proof-
          fix g'
          assume "weight g g' \<noteq> None"
          hence "strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}" using Strat by auto
          hence "\<exists>e. strat g' = inv_upd (the (weight g g')) e \<and> winning_budget_len e g'" by auto
          hence "strat g' = inv_upd (the (weight g g')) (the_e g') \<and> winning_budget_len (the_e g') g'" using the_e_def some_eq_ex
            by (metis (mono_tags, lifting)) 
          hence "the_e g' \<in> {x.  winning_budget_len x g'}" by auto
          hence "\<exists>x.  (minimal_winning_budget x g' \<and> x e\<le> the_e g')" using energy_Min_contains_smaller \<open>the_e g' \<in> {x.  winning_budget_len x g'}\<close>
            by meson
          hence "{x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')} \<noteq> {}" by auto
          thus "{inv_upd (the (weight g g')) x|x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')} \<noteq> {}"
            by auto
        qed
      
        hence len: "\<And>a. a \<in> {strat' g' |g'. weight g g' \<noteq> None} \<Longrightarrow> length a = dimension" 
        proof-
          fix a
          assume "a \<in> {strat' g' |g'. weight g g' \<noteq> None}"
          hence "\<exists> g'. a= strat' g' \<and> weight g g' \<noteq> None" by auto
          from this obtain g' where "a= strat' g' \<and> weight g g' \<noteq> None" by auto
          hence some_not_empty: " {inv_upd (the (weight g g')) x|x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')} \<noteq> {}"
            using some_not_empty by blast

          have "strat' g' = (SOME x. x \<in> {inv_upd (the (weight g g')) x| 
                                                        x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')})" 
            using strat'_def by auto
          hence "strat' g' \<in> {inv_upd (the (weight g g')) x| x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')}"
            using some_not_empty some_in_eq
            by (smt (verit, ccfv_SIG) Eps_cong) 
          hence "\<exists>x. strat' g' = inv_upd (the (weight g g')) x \<and>  minimal_winning_budget x g' \<and> x e\<le> the_e g'"
            by simp
          from this obtain x where X: "strat' g' = inv_upd (the (weight g g')) x \<and>  minimal_winning_budget x g' \<and> x e\<le> the_e g'" by auto
          hence "winning_budget_len x g'" using energy_Min_def by simp
          hence "length x = dimension" using winning_budget_len.simps
            by blast 
          have "a=inv_upd (the (weight g g')) x" using X \<open>a= strat' g' \<and> weight g g' \<noteq> None\<close> by simp
          thus "length a = dimension" 
            using \<open>length x = dimension\<close> len_inv_appl  \<open>a= strat' g' \<and> weight g g' \<noteq> None\<close> by simp
        qed

        show "False" 
        proof(cases "deadend g")
          case True (*  \<Longrightarrow> e = NULLEVEKTOR *)

          from emin have " \<exists>strat.
            (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                  strat g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}) \<and>
            e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" using energy_Min_def by auto
          from this obtain strat where "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                  strat g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}) \<and>
            e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" by auto
          hence "e = energy_sup dimension {}" using True by simp

          hence "\<And>i. i < dimension \<Longrightarrow> e!i = 0" using empty_Sup_is_zero
            by simp
          then show ?thesis using \<open>e' e< e\<close> energy_leq_def
            using \<open>length e = dimension\<close> energy_leq.antisym by auto
        next
          case False
          hence notempty: "{strat' g' |g'. weight g g' \<noteq> None} \<noteq> {}" by auto

          have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> strat' g' e\<le> strat g'" 
          proof-
            fix g'
            assume "weight g g' \<noteq> None"
            hence some_not_empty: "{inv_upd (the (weight g g')) x|x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')} \<noteq> {}" 
              using some_not_empty by auto
            have "strat' g' = (SOME x. x \<in> {inv_upd (the (weight g g')) x| 
                                                        x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')})" 
              using strat'_def by auto
            hence "strat' g' \<in> {inv_upd (the (weight g g')) x| x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')}"
              using some_not_empty some_in_eq
              by (smt (verit, ccfv_SIG) Eps_cong) 
            hence "\<exists>x. strat' g' = inv_upd (the (weight g g')) x \<and>  minimal_winning_budget x g' \<and> x e\<le> the_e g'"
              by simp
            from this obtain x where X: "strat' g' = inv_upd (the (weight g g')) x \<and>  minimal_winning_budget x g' \<and> x e\<le> the_e g'" by auto
            hence "length x = dimension" using winning_budget_len.simps energy_Min_def
              by (metis (mono_tags, lifting) mem_Collect_eq) 
            hence "strat' g' e\<le>  inv_upd (the (weight g g')) (the_e g')" using inverse_monotonic X
              by (metis \<open>weight g g' \<noteq> None\<close> domain_inv)

            have "strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}" using Strat \<open>weight g g' \<noteq> None\<close> by auto
            hence "\<exists>e. strat g' = inv_upd (the (weight g g')) e \<and> winning_budget_len e g'" by auto
            hence "strat g' = inv_upd (the (weight g g')) (the_e g') \<and> winning_budget_len (the_e g') g'" using the_e_def some_eq_ex
              by (metis (mono_tags, lifting))
            thus "strat' g' e\<le> strat g'" using \<open>strat' g' e\<le>  inv_upd (the (weight g g')) (the_e g')\<close> by auto
          qed

          hence "(\<And>a. a \<in> {strat' g' |g'. weight g g' \<noteq> None} \<Longrightarrow> \<exists>b\<in>{strat g' |g'. weight g g' \<noteq> None}. a e\<le> b)" by auto
          hence "energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None} e\<le> e'" 
            using notempty len Strat energy_sup_leq_energy_sup
            by presburger 
          hence le: "energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None} e< e" using \<open>e' e< e\<close>
            using energy_leq.asym energy_leq.trans by blast

          have "energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None} \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}" 
          proof-
            have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat' g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})"
            proof
              fix g'
              show "weight g g' \<noteq> None \<longrightarrow>
                    strat' g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}"
              proof
                assume "weight g g' \<noteq> None"
                hence some_not_empty: "{inv_upd (the (weight g g')) x |x. minimal_winning_budget x g' \<and> x e\<le> the_e g'} \<noteq> {}"
                  using some_not_empty by auto
                have "strat' g' = (SOME x. x \<in> {inv_upd (the (weight g g')) x| 
                                                        x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')})" 
                  using strat'_def by auto
                hence "strat' g' \<in> {inv_upd (the (weight g g')) x| x. (minimal_winning_budget x g' \<and> x e\<le> the_e g')}"
                  using some_not_empty some_in_eq
                  by (smt (verit, ccfv_SIG) Eps_cong) 
                thus "strat' g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}"
                  by auto
              qed
            qed
            hence "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> energy_sup dimension {strat' g' |g'. weight g g' \<noteq> None} = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
              by blast 
            then show ?thesis
              by simp 
          qed

          then show ?thesis 
            using energy_Min_def emin le 
            by (smt (verit) mem_Collect_eq)
        qed
      qed    

      hence "e \<in> energy_Min
            {e''.
             \<exists>strat.
                (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                      strat g' \<in> {inv_upd (the (weight g g')) e |e. winning_budget_len e g'}) \<and>
                e'' = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}}" using element_of energy_Min_def
        by (smt (verit) mem_Collect_eq)  
      thus "minimal_winning_budget e g" 
        using min_winning_budget_d_iff_energy_Min \<open>g \<notin> attacker\<close>  \<open>length e = dimension\<close> by blast
    qed
  qed


  have "\<And>g e. e \<in> a_win_min g \<Longrightarrow> length e = dimension" 
    using winning_budget_len.simps energy_Min_def
    by (metis (no_types, lifting) mem_Collect_eq)
  hence D: "\<And>g e. e \<in> a_win_min g = (e \<in> a_win_min g \<and> length e = dimension)" by auto
  fix g 
  show "iteration a_win_min g = a_win_min g"
  proof(cases "g \<in> attacker")
    case True
    have "a_win_min g = {e. minimal_winning_budget e g}" by simp
    hence "a_win_min g =  energy_Min {e. \<exists>g' e'.
                   weight g g' \<noteq> None \<and>
                   minimal_winning_budget e' g' \<and> e = inv_upd (the (weight g g')) e'}" 
      using minimal_winning_budget_attacker True by simp
    also have "... = energy_Min {inv_upd (the (weight g g')) e'|g' e'.
                   weight g g' \<noteq> None \<and>
                   minimal_winning_budget e' g' }"
      by meson
    also have "... = energy_Min {inv_upd (the (weight g g')) e'|e' g'.
                   weight g g' \<noteq> None \<and>  e' \<in> a_win_min g'}"
      by (metis (no_types, lifting) mem_Collect_eq) 
    also have "... = energy_Min {inv_upd (the (weight g g')) e'|e' g'. length e' = dimension \<and>
                   weight g g' \<noteq> None \<and> e' \<in> a_win_min g'}" 
      using D by meson
    also have "... = iteration a_win_min g" using iteration_def True by simp
    finally show ?thesis by simp
  next
    case False
    have "a_win_min g = {e. minimal_winning_budget e g}" by simp
    hence minwin: "a_win_min g = energy_Min {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
      using minimal_winning_budget_defender False by simp
    hence "a_win_min g = energy_Min {energy_sup dimension {strat g'| g'. weight g g' \<noteq> None} | strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})}"
      by (smt (z3) Collect_cong)
    have iteration: "energy_Min {energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')} = iteration a_win_min g" 
      using iteration_def False by simp
    
    have "{e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}
        ={energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')}"
    proof
      show "{e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}
            \<subseteq>{energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow>(length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')}"
      proof
        fix e 
        assume "e \<in> {e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
        hence "\<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
          by auto
        from this obtain strat where S: "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})"
          by auto
        define e_index where "e_index \<equiv> \<lambda>g'. (SOME e''. e'' \<in> a_win_min g' \<and> strat g' = the (inverse_application (the (weight g g')) e''))"
        hence index: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> (e_index g') \<in> a_win_min g' \<and> strat g' = the (inverse_application (the (weight g g')) (e_index g'))"
        proof-
          fix g'
          have I: "e_index g' = (SOME e''. e'' \<in> a_win_min g' \<and> strat g' = the (inverse_application (the (weight g g')) e''))"
            using e_index_def by simp
          assume "weight g g' \<noteq> None"
          hence "strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'}"
            using S by simp
          hence "strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. e \<in> a_win_min g'}" by simp
          hence "\<exists>e''. e'' \<in> a_win_min g' \<and> strat g' = the (inverse_application (the (weight g g')) e'')" by auto
          thus "(e_index g') \<in> a_win_min g' \<and> strat g' = the (inverse_application (the (weight g g')) (e_index g'))"
            unfolding e_index_def using some_eq_ex
            by (smt (verit, del_insts)) 
        qed

        show "e \<in> {energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')}"
        proof
          show "\<exists>e_index. e = energy_sup dimension {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} \<and>
       (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g'))"
          proof
            show "e = energy_sup dimension {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} \<and>
       (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g'))"
            proof
              show "e = energy_sup dimension {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None}"
                using index S
                by (smt (verit) Collect_cong) 
              have "\<forall>g'. weight g g' \<noteq> None \<longrightarrow> e_index g' \<in> a_win_min g'" 
                using index by simp
              thus "\<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')" 
                using D by meson
            qed
          qed
        qed
      qed
      show "{energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')}
          \<subseteq>{e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
      proof
        fix e
        assume "e \<in> {energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} |
           e_index. \<forall>g'. weight g g' \<noteq> None \<longrightarrow> (length (e_index g') = dimension \<and> e_index g' \<in> a_win_min g')}"
        from this obtain e_index where I: "e = energy_sup dimension {inv_upd (the (weight g g')) (e_index g') | g'. weight g g' \<noteq> None} \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> e_index g' \<in> a_win_min g')"
          by blast
        define strat where "strat \<equiv> \<lambda>g'. inv_upd (the (weight g g')) (e_index g')"
        
        show "e \<in>{e''. \<exists>strat. (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> strat g' \<in> {the (inverse_application (the (weight g g')) e) | e. minimal_winning_budget e g'})
                  \<and> e'' = (energy_sup dimension {strat g'| g'. weight g g' \<noteq> None})}"
        proof
          show "\<exists>strat.
       (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
             strat g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}) \<and>
       e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}"
          proof
            show "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
             strat g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}) \<and>
       e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}"
            proof
              show "\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
         strat g' \<in> {inv_upd (the (weight g g')) e |e. minimal_winning_budget e g'}"
                using I strat_def by blast
              show "e = energy_sup dimension {strat g' |g'. weight g g' \<noteq> None}" using I strat_def
                by blast 
            qed
          qed
        qed
      qed
    qed

    thus ?thesis using minwin iteration by simp
  qed
qed

text\<open>With this we can conclude that \<open>iteration\<close> maps subsets of winning budgets to subsets of winning budgets.\<close>

lemma iteration_stays_winning:
  assumes "F \<in> possible_pareto" and "F \<preceq> a_win_min"
  shows "iteration F \<preceq> a_win_min"
proof-
  have "iteration F \<preceq> iteration a_win_min" 
    using assms iteration_monotonic  a_win_min_in_pareto by blast
  thus ?thesis 
    using a_win_min_is_fp by simp
qed

text\<open>We now prepare the proof that \<open>a_win_min\<close> is the \textit{least} fixed point of \<open>iteration\<close> by introducing \<open>S\<close>.
\<close>

inductive S:: "energy \<Rightarrow> 'position \<Rightarrow> bool" where
  "S e g" if "g \<notin> attacker \<and> (\<exists>index. e = (energy_sup dimension 
              {inv_upd (the (weight g g')) (index g')| g'. weight g g' \<noteq> None})
              \<and> (\<forall>g'.  weight g g' \<noteq> None \<longrightarrow>  S (index g') g'))" |
  "S e g" if "g \<in> attacker \<and> (\<exists>g'.( weight g g' \<noteq> None 
              \<and> (\<exists>e'. S e' g' \<and> e = inv_upd (the (weight g g')) e')))"

lemma length_S: 
  shows "\<And>e g. S e g \<Longrightarrow> length e = dimension"
proof-
  fix e g
  assume "S e g"
  thus "length e = dimension"
  proof(rule S.induct)
    show "\<And>g e. g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> length (index g') = dimension)) \<Longrightarrow>
           length e = dimension"
    proof-
      fix e g 
      assume "g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> length (index g') = dimension))"
      from this obtain index where "e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}" by auto
      thus "length e = dimension" using energy_sup_def by simp
    qed

    show "\<And>g e. g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and> length e' = dimension) \<and>
                       e = inv_upd (the (weight g g')) e')) \<Longrightarrow>
           length e = dimension"
    proof-
      fix e g 
      assume "g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and> length e' = dimension) \<and>
                       e = inv_upd (the (weight g g')) e'))"
      from this obtain g' e' where "weight g g' \<noteq> None" and "(S e' g' \<and> length e' = dimension) \<and>
                       e = inv_upd (the (weight g g')) e'" by auto
      thus "length e = dimension" using len_inv_appl  by simp
    qed
  qed
qed

lemma a_win_min_is_minS:
  shows "energy_Min {e. S e g} = a_win_min g"
proof-
    have "{e. \<exists>e'. S e' g \<and> e' e\<le> e} = a_win g"
  proof
    show "{e. \<exists>e'. S e' g \<and> e' e\<le> e} \<subseteq> a_win g"
    proof
      fix e
      assume "e \<in> {e. \<exists>e'. S e' g \<and> e' e\<le> e}"
      from this obtain e' where "S e' g \<and> e' e\<le> e" by auto
      have "e' \<in> a_win g" 
      proof(rule S.induct)
        show "S e' g" using \<open>S e' g \<and> e' e\<le> e\<close> by simp
        show "\<And>g e. g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> index g' \<in> a_win g')) \<Longrightarrow>
           e \<in> a_win g"
        proof
          fix e g 
          assume A: "g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> index g' \<in> a_win g'))"
          from this obtain index where E: "e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> index g' \<in> a_win g')" by auto
          show "winning_budget_len e g"
          proof(rule winning_budget_len.intros(1))
            show "length e = dimension \<and>
    g \<notin> attacker \<and>
    (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g')"
            proof
              show "length e = dimension"
                using E energy_sup_def
                by simp 
              show "g \<notin> attacker \<and>
    (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g')"
              proof
                show "g \<notin> attacker"
                  using A by simp
                show "\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
         apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g'"
                proof
                  fix g'
                  show "weight g g' \<noteq> None \<longrightarrow>
         apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g'"
                  proof
                    assume "weight g g' \<noteq> None"
                    hence "S (index g') g' \<and> index g' \<in> a_win g'" using E
                      by simp 
                    show "apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g'"
                    proof
                      from E have E:"e = energy_sup dimension {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}" by simp
                      have leq: "inv_upd (the (weight g g')) (index g') e\<le> e" 
                        unfolding E proof(rule energy_sup_in)
                        show "inv_upd (the (weight g g')) (index g')
                             \<in> {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}" using \<open>weight g g' \<noteq> None\<close> by auto
                        show "length (inv_upd (the (weight g g')) (index g')) = dimension" using len_inv_appl  \<open>weight g g' \<noteq> None\<close> \<open>S (index g') g' \<and> index g' \<in> a_win g'\<close> winning_budget_len.simps
                          by (metis mem_Collect_eq)
                      qed

                      show "apply_w g g' e \<noteq> None"
                      using \<open>weight g g' \<noteq> None\<close> proof(rule domain_upw_closed)
                        show "apply_w g g' (inv_upd (the (weight g g')) (index g')) \<noteq> None"
                          using domain_inv  \<open>weight g g' \<noteq> None\<close> \<open>S (index g') g' \<and> index g' \<in> a_win g'\<close> winning_budget_len.simps
                          by (metis domain_inv mem_Collect_eq) 
                        show "inv_upd (the (weight g g')) (index g') e\<le> e" using leq by simp
                      qed
                      
                      have "index g' e\<le> upd (the (weight g g')) e"
                      proof(rule energy_leq.trans) 
                        show "index g' e\<le> upd (the (weight g g')) (inv_upd (the (weight g g')) (index g'))"
                          using leq_up_inv  \<open>S (index g') g' \<and> index g' \<in> a_win g'\<close> winning_budget_len.simps
                          by (metis \<open>weight g g' \<noteq> None\<close> mem_Collect_eq)
                        show "upd (the (weight g g')) (inv_upd (the (weight g g')) (index g')) e\<le>
    upd (the (weight g g')) e" using leq updates_monotonic  \<open>weight g g' \<noteq> None\<close>
                          by (metis \<open>S (index g') g' \<and> index g' \<in> a_win g'\<close> domain_inv len_inv_appl length_S) 
                      qed
                      
                      thus "winning_budget_len (upd (the (weight g g')) e) g'"
                        using upwards_closure_wb_len \<open>S (index g') g' \<and> index g' \<in> a_win g'\<close> by blast
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed


        show "\<And>g e. g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e')) \<Longrightarrow>
           e \<in> a_win g "
        proof
          fix e g 
          assume A: "g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'))"
          from this obtain g' e' where "weight g g' \<noteq> None" and "(S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'" by auto
          hence "e' e\<le> upd (the (weight g g')) e" 
            using  updates_monotonic domain_inv domain_inv
            by (metis length_S leq_up_inv)
          show "winning_budget_len e g" 
          proof(rule winning_budget_len.intros(2))
            show "length e = dimension \<and>
    g \<in> attacker \<and>
    (\<exists>g'. weight g g' \<noteq> None \<and>
          apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g')"
            proof
              have"length e' = dimension" using \<open>(S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'\<close> winning_budget_len.simps
                by blast
              show "length e = dimension"
                using \<open>(S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'\<close> len_inv_appl \<open>length e' = dimension\<close> \<open>weight g g' \<noteq> None\<close>
                by blast               
              show "g \<in> attacker \<and>
    (\<exists>g'. weight g g' \<noteq> None \<and>
          apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g')"
              proof
                show "g \<in> attacker" using A by simp
                show "\<exists>g'. weight g g' \<noteq> None \<and>
         apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g' "
                proof
                  show " weight g g' \<noteq> None \<and>
         apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g'"
                  proof
                    show "weight g g' \<noteq> None"
                      using \<open>weight g g' \<noteq> None\<close> .
                    show "apply_w g g' e \<noteq> None \<and> winning_budget_len (upd (the (weight g g')) e) g'"
                    proof
                      show "apply_w g g' e \<noteq> None"
                        using \<open>weight g g' \<noteq> None\<close> \<open>(S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'\<close>
                        \<open>e' e\<le> upd (the (weight g g')) e\<close>  updates_monotonic domain_inv domain_inv
                        by (metis mem_Collect_eq winning_budget_len.cases)
                      show "winning_budget_len (upd (the (weight g g')) e) g'"
                        using \<open>e' e\<le> upd (the (weight g g')) e\<close> upwards_closure_wb_len \<open>(S e' g' \<and> e' \<in> a_win g') \<and> e = inv_upd (the (weight g g')) e'\<close> by blast
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
      thus "e \<in> a_win g" using \<open>S e' g \<and> e' e\<le> e\<close> upwards_closure_wb_len
        by blast 
    qed
  next
    show "a_win g \<subseteq> {e. \<exists>e'. S e' g \<and> e' e\<le> e}"
    proof

      define P where "P \<equiv> \<lambda>(g,e). (e \<in>{e. \<exists>e'. S e' g \<and> e' e\<le> e})"
      
      fix e
      assume "e \<in> a_win g" 
      from this obtain s where S: "attacker_winning_strategy s e g"
        using nonpos_eq_pos
        by (metis winning_bugget_len_is_wb mem_Collect_eq winning_budget.elims(2))       
      have "reachable_positions_len s g e \<subseteq> reachable_positions s g e" by auto
      hence "wfp_on (strategy_order s) (reachable_positions_len s g e)" 
        using strategy_order_well_founded S
        using Restricted_Predicates.wfp_on_subset by blast
      hence "inductive_on (strategy_order s) (reachable_positions_len s g e)"
        by (simp add: wfp_on_iff_inductive_on)

      hence "P (g,e)" 
      proof(rule inductive_on_induct)
        show "(g,e) \<in> reachable_positions_len s g e"
          unfolding reachable_positions_def proof-
          have "lfinite LNil \<and>
             llast (LCons g LNil) = g \<and>
             valid_play (LCons g LNil) \<and> play_consistent_attacker s (LCons g LNil) e \<and>
            Some e = energy_level e (LCons g LNil) (the_enat (llength LNil))"
            using valid_play.simps play_consistent_attacker.simps energy_level.simps
            by (metis lfinite_code(1) llast_singleton llength_LNil neq_LNil_conv the_enat_0) 
          thus "(g, e)
    \<in> {(g', e').
        (g', e')
        \<in> {(g', e') |g' e'.
            \<exists>p. lfinite p \<and>
                llast (LCons g p) = g' \<and>
                valid_play (LCons g p) \<and>
                play_consistent_attacker s (LCons g p) e \<and> Some e' = energy_level e (LCons g p) (the_enat (llength p))} \<and>
        length e' = dimension}"
            using \<open>e \<in> a_win g\<close> nonpos_eq_pos winning_bugget_len_is_wb
            by auto
        qed

        show "\<And>y. y \<in> reachable_positions_len s g e \<Longrightarrow>
              (\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> P x) \<Longrightarrow> P y"
        proof-
          fix y 
          assume "y \<in> reachable_positions_len s g e"
          hence "\<exists>e' g'. y = (g', e')" using reachable_positions_def by auto
          from this obtain e' g' where "y = (g', e')" by auto

          hence y_len: "(\<exists>p. lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p))))
                \<and> length e' = dimension"
            using \<open>y \<in> reachable_positions_len s g e\<close> unfolding reachable_positions_def
            by auto 
          from this obtain p where P: "(lfinite p \<and> llast (LCons g p) = g' 
                                                    \<and> valid_play (LCons g p) 
                                                    \<and> play_consistent_attacker s (LCons g p) e) 
                                                    \<and> (Some e' = energy_level e (LCons g p) (the_enat (llength p)))" by auto
       
          show "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> P x) \<Longrightarrow> P y"
          proof-
            assume ind: "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> P x)"
            thus "P y" 
            proof(cases "g' \<in> attacker")
              case True 
              then show ?thesis 
              proof(cases "deadend g'")
                case True (* wiederspruchsbeweis *)
                hence "attacker_stuck (LCons g p)" using \<open>g' \<in> attacker\<close> P
                  by (meson defender_wins_play_def attacker_winning_strategy.elims(2)) 
                hence "defender_wins_play e (LCons g p)" using defender_wins_play_def by simp
                have "\<not>defender_wins_play e (LCons g p)" using P S by simp
                then show ?thesis using \<open>defender_wins_play e (LCons g p)\<close> by simp
              next
                case False (* nehme s e' g' und wende ind.hyps. darauf an *)
                hence "(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None" using S attacker_winning_strategy.simps
                  by (simp add: True attacker_strategy_def)

                define x where "x = (the (s e' g'), the (apply_w g' (the (s e' g')) e'))"
                define p' where "p' =  (lappend p (LCons (the (s e' g')) LNil))"
                hence "lfinite p'" using P by simp
                have "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
                  by (simp add: llast_LCons)

                have "the_enat (llength p') > 0" using P
                  by (metis LNil_eq_lappend_iff \<open>lfinite p'\<close> bot_nat_0.not_eq_extremum enat_0_iff(2) lfinite_conv_llength_enat llength_eq_0 llist.collapse(1) llist.distinct(1) p'_def the_enat.simps) 
                hence "\<exists>i. Suc i = the_enat (llength p')"
                  using less_iff_Suc_add by auto 
                from this obtain i where "Suc i = the_enat (llength p')" by auto
                hence "i = the_enat (llength p)" using p'_def P                     
                  by (metis Suc_leI \<open>lfinite p'\<close> length_append_singleton length_list_of_conv_the_enat less_Suc_eq_le less_irrefl_nat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend not_less_less_Suc_eq)
                hence "Some e' = (energy_level e (LCons g p) i)" using P by simp

                have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                proof
                  show "lfinite (LCons g p)" using P by simp
                  show "i < the_enat (llength (LCons g p)) \<and> energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                  proof
                    show "i < the_enat (llength (LCons g p))" using \<open>i = the_enat (llength p)\<close> P
                      by (metis \<open>lfinite (LCons g p)\<close> length_Cons length_list_of_conv_the_enat lessI list_of_LCons) 
                    show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P \<open>i = the_enat (llength p)\<close>
                      using S defender_wins_play_def by auto
                  qed
                qed

                hence "Some e' = (energy_level e (LCons g p') i)" using p'_def energy_level_append P \<open>Some e' = (energy_level e (LCons g p) i)\<close>
                  by (metis lappend_code(2))
                hence "energy_level e (LCons g p') i \<noteq> None"
                  by (metis option.distinct(1))

                have "enat (Suc i) = llength p'" using \<open>Suc i = the_enat (llength p')\<close>
                  by (metis \<open>lfinite p'\<close> lfinite_conv_llength_enat the_enat.simps)
                also have "... < eSuc (llength p')"
                  by (metis calculation iless_Suc_eq order_refl) 
                also have "... = llength (LCons g p')" using \<open>lfinite p'\<close> by simp
                finally have "enat (Suc i) < llength (LCons g p')".

                have "(lnth (LCons g p) i) = g'" using \<open>i = the_enat (llength p)\<close> P
                  by (metis lfinite_conv_llength_enat llast_conv_lnth llength_LCons the_enat.simps) 
                hence "(lnth (LCons g p') i) = g'" using p'_def
                  by (metis P \<open>i = the_enat (llength p)\<close> enat_ord_simps(2) energy_level.elims lessI lfinite_llength_enat lnth_0 lnth_Suc_LCons lnth_lappend1 the_enat.simps) 

                have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" 
                  using \<open>Suc i = the_enat (llength p')\<close> by simp
                also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
                  using energy_level.simps \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>energy_level e (LCons g p') i \<noteq> None\<close>
                  by (meson leD)
                also have "... =  apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) e'" using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
                  by (metis option.sel) 
                also have "... =  apply_w (lnth (LCons g p') i) (the (s e' g')) e'" using p'_def \<open>enat (Suc i) = llength p'\<close>
                  by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>llast (LCons g p') = the (s e' g')\<close> llast_conv_lnth) 
                also have  "... =  apply_w g' (the (s e' g')) e'" using \<open>(lnth (LCons g p') i) = g'\<close> by simp
                finally have "energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'" .
            
                have P': "lfinite p'\<and>
             llast (LCons g p') = (the (s e' g')) \<and>
             valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
            Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                proof
                  show "lfinite p'" using p'_def P by simp
                  show "llast (LCons g p') = the (s e' g') \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                  proof
                    show "llast (LCons g p') = the (s e' g')" using p'_def \<open>lfinite p'\<close>
                      by (simp add: llast_LCons) 
                    show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                    proof
                      show "valid_play (LCons g p')" using p'_def P
                        using \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> valid_play.intros(2) valid_play_append by auto
                      show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                      proof
                        have "(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)" using p'_def
                          by simp
                        have "play_consistent_attacker s (lappend (LCons g p) (LCons (the (s e' g')) LNil)) e"
                        proof (rule play_consistent_attacker_append_one)
                          show "play_consistent_attacker s (LCons g p) e"
                            using P by auto
                          show "lfinite (LCons g p)" using P by auto
                          show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                            using A by auto 
                          show "valid_play (lappend (LCons g p) (LCons (the (s e' g')) LNil))" 
                            using \<open>valid_play (LCons g p')\<close> \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                          show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                          proof
                            assume "llast (LCons g p) \<in> attacker"
                            show "Some (the (s e' g')) =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                              using \<open>llast (LCons g p) \<in> attacker\<close> P
                              by (metis One_nat_def \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> diff_Suc_1' eSuc_enat lfinite_llength_enat llength_LCons option.collapse option.sel the_enat.simps) 
                          qed
                        qed
                        thus "play_consistent_attacker s (LCons g p') e" using \<open>(LCons g p') = lappend (LCons g p) (LCons (the (s e' g')) LNil)\<close> by simp
                    
                        show "Some (the (apply_w g' (the (s e' g')) e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                          by (metis \<open>eSuc (llength p') = llength (LCons g p')\<close> \<open>enat (Suc i) = llength p'\<close> \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> \<open>play_consistent_attacker s (LCons g p') e\<close> \<open>valid_play (LCons g p')\<close> S defender_wins_play_def diff_Suc_1 eSuc_enat option.collapse attacker_winning_strategy.elims(2) the_enat.simps)
                      qed
                    qed
                  qed
                qed

                have x_len: "length (upd (the (weight g' (the (s e' g')))) e') = dimension" using y_len
                  by (metis P' \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> len_appl option.distinct(1)) 
                hence "x \<in> reachable_positions_len s g e" using P' reachable_positions_def x_def by auto

                have "(apply_w g' (the (s e' g')) e') \<noteq> None" using P'
                  by (metis \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> option.distinct(1)) 
    
                have "Some (the (apply_w g' (the (s e' g')) e')) = apply_w g' (the (s e' g')) e' \<and> (if g' \<in> attacker then Some (the (s e' g')) = s e' g' else weight g' (the (s e' g')) \<noteq> None)"
                  using \<open>(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None\<close> \<open>(apply_w g' (the (s e' g')) e') \<noteq> None\<close> by simp
                hence "strategy_order s x y" unfolding strategy_order_def using x_def \<open>y = (g', e')\<close>
                  by blast
                hence "P x" using ind \<open>x \<in> reachable_positions_len s g e\<close> by simp 
               
                hence "\<exists>e''. S e'' (the (s e' g')) \<and> e'' e\<le> ( upd (the (weight g' (the (s e' g')))) e')" unfolding P_def x_def by simp
                from this obtain e'' where E: "S e'' (the (s e' g')) \<and> e'' e\<le> (upd (the (weight g' (the (s e' g')))) e')" by auto
                hence "S (inv_upd (the (weight g' (the (s e' g')))) e'') g'" using True S.intros(2)
                  using \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> by blast

                have "(inv_upd (the (weight g' (the (s e' g')))) e'') e\<le> inv_upd (the (weight g' (the (s e' g')))) (upd (the (weight g' (the (s e' g')))) e')" 
                  using E inverse_monotonic  \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close>
                  using x_len
                  using domain_inv length_S by blast  
                hence "(inv_upd (the (weight g' (the (s e' g')))) e'') e\<le> e'" using inv_up_leq  \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close>
                  using \<open>apply_w g' (the (s e' g')) e' \<noteq> None\<close> energy_leq.trans
                  using y_len by blast
                thus "P y" unfolding P_def \<open>y = (g', e')\<close>
                  using \<open>S (inv_upd (the (weight g' (the (s e' g')))) e'') g'\<close> by blast 
              qed
            next
              case False
              hence P: "g' \<notin> attacker \<and>
            (\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> P (g'', (the (apply_w g' g'' e'))))"
              proof
                show "\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and>  P (g'', (the (apply_w g' g'' e')))"
                proof
                  fix g''
                  show "weight g' g'' \<noteq> None \<longrightarrow>
           apply_w g' g'' e' \<noteq> None \<and>  P (g'', (the (apply_w g' g'' e'))) "
                  proof
                    assume "weight g' g'' \<noteq> None"
                    show "apply_w g' g'' e' \<noteq> None \<and>  P (g'', (the (apply_w g' g'' e')))"
                    proof
                      show "apply_w g' g'' e' \<noteq> None"
                      proof
                        assume "apply_w g' g'' e' = None"
                        define p' where "p' \<equiv> (LCons g (lappend p (LCons g'' LNil)))"
                        hence "lfinite p'" using P by simp
                        have "\<exists>i. llength p = enat i" using P
                          by (simp add: lfinite_llength_enat) 
                        from this obtain i where "llength p = enat i" by auto
                        hence "llength (lappend p (LCons g'' LNil)) = enat (Suc i)"
                          by (simp add: \<open>llength p = enat i\<close> eSuc_enat iadd_Suc_right)
                        hence "llength p' = eSuc (enat(Suc i))" using p'_def
                          by simp 
                        hence "the_enat (llength p') = Suc (Suc i)"
                          by (simp add: eSuc_enat)
                        hence "the_enat (llength p') - 1 = Suc i"
                          by simp 
                        hence "the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))"
                          using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close>
                          by simp

                        have "(lnth p' i) = g'" using p'_def \<open>llength p = enat i\<close> P
                          by (smt (verit) One_nat_def diff_Suc_1' enat_ord_simps(2) energy_level.elims lessI llast_conv_lnth llength_LCons lnth_0 lnth_LCons' lnth_lappend the_enat.simps)
                        have "(lnth p' (Suc i)) = g''" using p'_def \<open>llength p = enat i\<close>
                          by (metis \<open>llength p' = eSuc (enat (Suc i))\<close> lappend.disc(2) llast_LCons llast_conv_lnth llast_lappend_LCons llength_eq_enat_lfiniteD llist.disc(1) llist.disc(2))
                        have "p' = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                        hence "the (energy_level e p' i) = the (energy_level e (lappend (LCons g p) (LCons g'' LNil)) i)" by simp
                        also have "... = the (energy_level e (LCons g p) i)" using \<open>llength p = enat i\<close> energy_level_append P
                          by (metis diff_Suc_1 eSuc_enat lessI lfinite_LConsI llength_LCons option.distinct(1) the_enat.simps) 
                        also have "... = e'" using P
                          by (metis \<open>llength p = enat i\<close> option.sel the_enat.simps) 
                        finally have "the (energy_level e p' i) = e'" . 
                        hence "apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None" using \<open>apply_w g' g'' e'=None\<close> \<open>(lnth p' i) = g'\<close> \<open>(lnth p' (Suc i)) = g''\<close> by simp

                        have "energy_level e p' (the_enat (llength p') - 1) = 
                          energy_level e p' (the_enat (llength (lappend p (LCons g'' LNil))))" 
                          using \<open>the_enat (llength p') - 1 = the_enat (llength (lappend p (LCons g'' LNil)))\<close>
                          by simp 
                        also have "... = energy_level e p' (Suc i)" using \<open>llength (lappend p (LCons g'' LNil)) = enat (Suc i)\<close> by simp
                        also have "... = (if energy_level e p' i = None \<or> llength p' \<le> enat (Suc i) then None
                                      else apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)))" using energy_level.simps by simp
                        also have "... = None " using \<open>apply_w (lnth p' i) (lnth p' (Suc i)) (the (energy_level e p' i)) = None\<close>
                          by simp
                        finally have "energy_level e p' (the_enat (llength p') - 1) = None" .
                        hence "defender_wins_play e p'" unfolding defender_wins_play_def by simp

                        have "valid_play p'"
                          by (metis P \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> \<open>weight g' g'' \<noteq> None\<close> energy_game.valid_play.intros(2) energy_game.valid_play_append lfinite_LConsI)

                        have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                        proof(rule play_consistent_attacker_append_one)
                          show "play_consistent_attacker s (LCons g p) e" 
                            using P by simp
                          show "lfinite (LCons g p)" using P by simp
                          show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                            using P
                            by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                          show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                            using \<open>valid_play p'\<close> \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                          show "llast (LCons g p) \<in> attacker \<longrightarrow>
    Some g'' =
    s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                            using False P by simp
                        qed
                        hence "play_consistent_attacker s p' e"
                          using \<open>p' = lappend (LCons g p) (LCons g'' LNil)\<close> by simp
                        hence "\<not>defender_wins_play e p'" using \<open>valid_play p'\<close> p'_def S by simp
                        thus "False" using \<open>defender_wins_play e p'\<close> by simp
                      (* widerspruch weil in reachable und sonst defender_wins_play *)
                      qed

                      define x where "x = (g'', the (apply_w g' g'' e'))"
                      have "P x" 
                      proof(rule ind)
                        have X: "(\<exists>p. lfinite p \<and>
             llast (LCons g p) = g'' \<and>
             valid_play (LCons g p) \<and> play_consistent_attacker s (LCons g p) e \<and>
            Some (the (apply_w g' g'' e')) = energy_level e (LCons g p) (the_enat (llength p)))"
                        proof
                          define p' where "p' = lappend p (LCons g'' LNil)"
                          show "lfinite p' \<and>
     llast (LCons g p') = g'' \<and>
     valid_play (LCons g p') \<and> play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                          proof
                            show "lfinite p'" using P p'_def by simp
                            show "llast (LCons g p') = g'' \<and>
    valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                            proof
                              show "llast (LCons g p') = g''" using p'_def
                                by (metis \<open>lfinite p'\<close> lappend.disc_iff(2) lfinite_lappend llast_LCons llast_lappend_LCons llast_singleton llist.discI(2))
                              show "valid_play (LCons g p') \<and>
    play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                              proof
                                show "valid_play (LCons g p')" using p'_def P
                                  using \<open>weight g' g'' \<noteq> None\<close> lfinite_LCons valid_play.intros(2) valid_play_append by auto
                                show "play_consistent_attacker s (LCons g p') e \<and>
    Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p')) "
                                proof

                                  have "play_consistent_attacker s (lappend (LCons g p) (LCons g'' LNil)) e"
                                  proof(rule play_consistent_attacker_append_one)
                                    show "play_consistent_attacker s (LCons g p) e" 
                                      using P by simp
                                    show "lfinite (LCons g p)" using P by simp
                                    show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                                      using P
                                      by (meson S defender_wins_play_def attacker_winning_strategy.elims(2))
                                    show "valid_play (lappend (LCons g p) (LCons g'' LNil))"
                                      using \<open>valid_play (LCons g p')\<close> p'_def by simp
                                    show "llast (LCons g p) \<in> attacker \<longrightarrow>
                                        Some g'' =
                                        s (the (energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1))) (llast (LCons g p))"
                                      using False P by simp
                                  qed
                                  thus "play_consistent_attacker s (LCons g p') e" using p'_def
                                    by (simp add: lappend_code(2)) 

                                  have "\<exists>i. Suc i = the_enat (llength p')" using p'_def \<open>lfinite p'\<close>
                                    by (metis P length_append_singleton length_list_of_conv_the_enat lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend)
                                  from this obtain i where "Suc i = the_enat (llength p')" by auto
                                  hence "i = the_enat (llength p)" using p'_def
                                    by (smt (verit) One_nat_def \<open>lfinite p'\<close> add.commute add_Suc_shift add_right_cancel length_append length_list_of_conv_the_enat lfinite_LNil lfinite_lappend list.size(3) list.size(4) list_of_LCons list_of_LNil list_of_lappend plus_1_eq_Suc)  
                                  hence "Suc i = llength (LCons g p)"
                                    using P eSuc_enat lfinite_llength_enat by fastforce
                                  have "(LCons g p') = lappend (LCons g p) (LCons g'' LNil)" using p'_def by simp
                                  have A: "lfinite (LCons g p) \<and> i < the_enat (llength (LCons g p)) \<and>  energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None"
                                  proof
                                    show "lfinite (LCons g p)" using P by simp
                                    show " i < the_enat (llength (LCons g p)) \<and>
    energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None "
                                    proof
                                      have "(llength p') = llength (LCons g p)" using p'_def
                                        by (metis P \<open>lfinite p'\<close> length_Cons length_append_singleton length_list_of lfinite_LConsI lfinite_LNil list_of_LCons list_of_LNil list_of_lappend) 
                                      thus "i < the_enat (llength (LCons g p))" using \<open>Suc i = the_enat (llength p')\<close>
                                        using lessI by force 
                                      show "energy_level e (LCons g p) (the_enat (llength (LCons g p)) - 1) \<noteq> None" using P
                                        by (meson S energy_game.defender_wins_play_def energy_game.play_consistent_attacker.intros(2) attacker_winning_strategy.simps)
                                    qed
                                  qed
                                  hence "energy_level e (LCons g p') i \<noteq> None"
                                    using energy_level_append
                                    by (smt (verit) Nat.lessE Suc_leI \<open>LCons g p' = lappend (LCons g p) (LCons g'' LNil)\<close> diff_Suc_1 energy_level_nth)  
                                  have "enat (Suc i) < llength (LCons g p')" 
                                    using \<open>Suc i = the_enat (llength p')\<close>
                                    by (metis Suc_ile_eq \<open>lfinite p'\<close> ldropn_Suc_LCons leI lfinite_conv_llength_enat lnull_ldropn nless_le the_enat.simps) 
                                  hence  el_prems: "energy_level e (LCons g p') i \<noteq> None \<and> llength (LCons g p') > enat (Suc i)" using \<open>energy_level e (LCons g p') i \<noteq> None\<close> by simp

                                  have "(lnth (LCons g p') i) = lnth (LCons g p) i" 
                                    unfolding \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close> using \<open>i = the_enat (llength p)\<close> lnth_lappend1
                                    by (metis A enat_ord_simps(2) length_list_of length_list_of_conv_the_enat)
                                  have "lnth (LCons g p) i = llast (LCons g p)" using \<open>Suc i = llength (LCons g p)\<close>
                                    by (metis enat_ord_simps(2) lappend_LNil2 ldropn_LNil ldropn_Suc_conv_ldropn ldropn_lappend lessI less_not_refl llast_ldropn llast_singleton)
                                  hence "(lnth (LCons g p') i) = g'" using P
                                    by (simp add: \<open>lnth (LCons g p') i = lnth (LCons g p) i\<close>) 
                                  have "(lnth (LCons g p') (Suc i)) = g''"
                                    using p'_def \<open>Suc i = the_enat (llength p')\<close>
                                    by (smt (verit) \<open>enat (Suc i) < llength (LCons g p')\<close> \<open>lfinite p'\<close> \<open>llast (LCons g p') = g''\<close> lappend_snocL1_conv_LCons2 ldropn_LNil ldropn_Suc_LCons ldropn_Suc_conv_ldropn ldropn_lappend2 lfinite_llength_enat llast_ldropn llast_singleton the_enat.simps wlog_linorder_le)

                                  have "energy_level e (LCons g p) i = energy_level e (LCons g p') i" 
                                    using energy_level_append A \<open>(LCons g p') = lappend (LCons g p) (LCons g'' LNil)\<close>
                                    by presburger
                                  hence "Some e' = (energy_level e (LCons g p') i)" 
                                    using P \<open>i = the_enat (llength p)\<close>
                                    by argo 

                                  have "energy_level e (LCons g p') (the_enat (llength p')) = energy_level e (LCons g p') (Suc i)" using \<open>Suc i = the_enat (llength p')\<close> by simp
                                  also have "... = apply_w (lnth (LCons g p') i) (lnth (LCons g p') (Suc i)) (the (energy_level e (LCons g p') i))" 
                                    using energy_level.simps el_prems
                                    by (meson leD) 
                                  also have "... = apply_w g' g'' (the (energy_level e (LCons g p') i))" 
                                    using \<open>(lnth (LCons g p') i) = g'\<close> \<open>(lnth (LCons g p') (Suc i)) = g''\<close> by simp
                                  finally have "energy_level e (LCons g p') (the_enat (llength p')) = (apply_w g' g'' e')" 
                                    using \<open>Some e' = (energy_level e (LCons g p') i)\<close>
                                    by (metis option.sel) 
                                  thus "Some (the (apply_w g' g'' e')) = energy_level e (LCons g p') (the_enat (llength p'))"
                                    using \<open>apply_w g' g'' e' \<noteq> None\<close> by auto
                                qed
                              qed
                            qed
                          qed
                        qed

                        have x_len: "length (upd (the (weight g' g'')) e') = dimension" using y_len 
                          using \<open>apply_w g' g'' e' \<noteq> None\<close> len_appl
                          using \<open>weight g' g'' \<noteq> None\<close> by blast 

                        thus "x \<in> reachable_positions_len s g e"
                          using X x_def reachable_positions_def
                          by (simp add: mem_Collect_eq) 

                        have "Some (the (apply_w g' g'' e')) = apply_w g' g'' e' \<and>
         (if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                        proof
                          show "Some (the (apply_w g' g'' e')) = apply_w g' g'' e'"
                            using \<open>apply_w g' g'' e' \<noteq> None\<close> by auto
                          show "(if g' \<in> attacker then Some g'' = s e' g' else weight g' g'' \<noteq> None)"
                            using False
                            by (simp add: \<open>weight g' g'' \<noteq> None\<close>) 
                        qed
                        thus "strategy_order s x y" using strategy_order_def x_def \<open>y = (g', e')\<close>
                          by simp
                      qed

                      thus "P (g'', (the (apply_w g' g'' e')))" using x_def by simp
                    qed
                  qed
                qed
              qed

              hence "\<And>g''. weight g' g'' \<noteq> None \<Longrightarrow> \<exists>e0. S e0 g'' \<and> e0 e\<le> (the (apply_w g' g'' e'))" using P_def
                by blast  
              define index where "index = (\<lambda>g''. SOME e0.  S e0 g'' \<and> e0 e\<le> (the (apply_w g' g'' e')))"
              hence I: "\<And>g''. weight g' g'' \<noteq> None \<Longrightarrow> S (index g'') g'' \<and> (index g'') e\<le> (the (apply_w g' g'' e'))" 
                using \<open>\<And>g''. weight g' g'' \<noteq> None \<Longrightarrow> \<exists>e0. S e0 g'' \<and> e0 e\<le> (the (apply_w g' g'' e'))\<close> some_eq_ex
                by (smt (verit, del_insts))
              hence "\<And>g''. weight g' g'' \<noteq> None \<Longrightarrow> inv_upd (the (weight g' g'')) (index g'') e\<le> inv_upd (the (weight g' g'')) (the (apply_w g' g'' e'))"
                using inverse_monotonic P
                by (meson domain_inv length_S)
              hence  "\<And>g''. weight g' g'' \<noteq> None \<Longrightarrow> inv_upd (the (weight g' g'')) (index g'') e\<le> e'" 
                using inv_up_leq P
                by (meson I galois length_S y_len)        
              hence leq: "energy_sup dimension {inv_upd (the (weight g' g'')) (index g'')| g''. weight g' g'' \<noteq> None} e\<le> e'" 
                using energy_sup_leq
                by (smt (z3) \<open>y = (g', e')\<close> \<open>y \<in> {(g', e'). (g', e') \<in> reachable_positions s g e \<and> length e' = dimension}\<close> case_prodD mem_Collect_eq)
              
              have "S (energy_sup dimension {inv_upd (the (weight g' g'')) (index g'')| g''. weight g' g'' \<noteq> None}) g'" 
                using False S.intros(1) I
                by blast
              thus "P y" using leq P_def
                using \<open>y = (g', e')\<close> by blast 
            qed
          qed
        qed
      qed
      thus "e \<in> {e. \<exists>e'. S e' g \<and> e' e\<le> e}" using P_def by simp
    qed
  qed  
  hence "energy_Min {e. \<exists>e'. S e' g \<and> e' e\<le> e} = a_win_min g" by simp
  have "energy_Min {e. \<exists>e'. S e' g \<and> e' e\<le> e} = energy_Min {e. S e g}" unfolding energy_Min_def finite_positions
    by (smt (verit) Collect_cong energy_leq.refl energy_leq.strict_trans1 mem_Collect_eq) 
  thus " energy_Min {e. S e g} = a_win_min g" using \<open>energy_Min {e. \<exists>e'. S e' g \<and> e' e\<le> e} = a_win_min g\<close> by simp
qed

text\<open>We now conclude that the algorithm indeed returns the minimal attacker winning budgets.\<close>

lemma a_win_min_is_lfp_sup:
  shows "pareto_sup {(iteration ^^ i) (\<lambda>g. {}) |. i} = a_win_min"
proof(rule antisymmetry)

  have in_pareto_leq: "\<And>n. (iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
  proof-
    fix n 
    show "(iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
    proof(induct n)
      case 0
      show ?case 
      proof
        show "(iteration ^^ 0) (\<lambda>g. {}) \<in> possible_pareto"
          using funpow_simps_right(1) possible_pareto_def by auto
        have "(\<lambda>g. {}) \<preceq> a_win_min" 
          unfolding pareto_order_def by simp
        thus "(iteration ^^ 0) (\<lambda>g. {}) \<preceq> a_win_min" using funpow_simps_right(1) by simp
      qed
    next
      case (Suc n)
      have "(iteration ^^ (Suc n)) (\<lambda>g. {}) = iteration ((iteration ^^ n) (\<lambda>g. {}))" 
        by simp
      then show ?case using Suc iteration_stays_winning iteration_pareto_functor by simp
    qed
  qed

  show "pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} \<in> possible_pareto"
  proof(rule pareto_sup_is_sup)
    show "{(iteration ^^ n) (\<lambda>g. {}) |. n} \<subseteq> possible_pareto"
      using in_pareto_leq by auto
  qed

  show "a_win_min \<in> possible_pareto"
    using a_win_min_in_pareto by simp
 
  show "pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} \<preceq> a_win_min"
    using pareto_sup_is_sup in_pareto_leq a_win_min_in_pareto image_iff rangeE
    by (smt (verit) subsetI)

  define Smin where "Smin = (\<lambda>g. energy_Min {e. S e g})"

  have "Smin \<preceq> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n}"
    unfolding pareto_order_def proof
    fix g 
    show "\<forall>e. e \<in> Smin g \<longrightarrow>
             (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e)"
    proof
      fix e
      show "e \<in> Smin g \<longrightarrow>
         (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e)"
      proof
        assume "e \<in> Smin g"
        hence "S e g" using energy_Min_def Smin_def by simp
        thus "\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e"
        proof(rule S.induct)
          show "\<And>g e. g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                     S (index g') g' \<and>
                     (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g'))) \<Longrightarrow>
           \<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e"
          proof-
            fix e g 
            assume A: "g \<notin> attacker \<and>
           (\<exists>index.
               e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None} \<and>
               (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                     S (index g') g' \<and>
                     (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g')))"
            from this obtain index where "e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}" and
               "\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                     S (index g') g' \<and>
                     (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g')" by auto

            define index' where "index' \<equiv> \<lambda>g'. SOME e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g'"
            
            have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g'" using \<open>\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                     S (index g') g' \<and>
                     (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           e' e\<le> index g')\<close> by simp
            hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> index' g' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and>
                           index' g' e\<le> index g'" unfolding index'_def using some_eq_ex
              by (metis (mono_tags, lifting)) 
            hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>F. F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> index' g' \<in> F g'"
              unfolding pareto_sup_def using energy_Min_def by simp
            hence index'_len: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> length (index' g') = dimension" using possible_pareto_def
              by (metis \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> index' g' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> index' g' e\<le> index g'\<close> \<open>\<forall>g'. weight g g' \<noteq> None \<longrightarrow> S (index g') g' \<and> (\<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e' e\<le> index g')\<close> energy_leq_def length_S)  

            define index_F where "index_F = (\<lambda>g'. (SOME F. (F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> index' g' \<in> F g')))"
            have IF: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> index_F g' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> index' g' \<in> index_F g' g'"
              unfolding index_F_def using some_eq_ex \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>F. F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> index' g' \<in> F g'\<close>
              by (metis (mono_tags, lifting)) 

            have "\<exists>F. (F\<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> index_F g' \<preceq> F))"
            proof-
              define P' where "P' = {index_F g'| g'. weight g g' \<noteq> None}"
              have "\<exists>F'. F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> (\<forall>F. F \<in> P' \<longrightarrow> F \<preceq> F')"
              proof(rule finite_directed_set_upper_bound)
                show "\<And>F F'.
       F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<Longrightarrow>
       F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<Longrightarrow>
       \<exists>F''. F'' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> F \<preceq> F'' \<and> F' \<preceq> F''"
                proof-
                  fix F F'
                  assume "F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n}" and "F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n}"
                  from this obtain n m where "F = (iteration ^^ n) (\<lambda>g. {})" and "F' = (iteration ^^ m)(\<lambda>g. {})" by auto
                  show "\<exists>F''. F'' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> F \<preceq> F'' \<and> F' \<preceq> F''"
                  proof
                    show "((iteration ^^ (max n m)) (\<lambda>g. {})) \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> F \<preceq> ((iteration ^^ (max n m)) (\<lambda>g. {})) \<and> F' \<preceq> ((iteration ^^ (max n m)) (\<lambda>g. {}))"
                    proof-
                      have "\<And>i j. i \<le> j \<Longrightarrow> ((iteration ^^ i) (\<lambda>g. {})) \<preceq> ((iteration ^^ j) (\<lambda>g. {}))"
                      proof-
                        fix i j 
                        show " i \<le> j \<Longrightarrow> ((iteration ^^ i) (\<lambda>g. {})) \<preceq> ((iteration ^^ j) (\<lambda>g. {}))"
                        proof-
                          assume "i \<le> j"
                          thus "(iteration ^^ i) (\<lambda>g. {}) \<preceq> (iteration ^^ j) (\<lambda>g. {})"
                          proof(induct "j-i" arbitrary: i j)
                            case 0
                            hence "i = j" by simp
                            then show ?case
                              by (simp add: in_pareto_leq reflexivity) 
                          next
                            case (Suc x)
                            show ?case
                            proof(rule transitivity)
                              show A: "(iteration ^^ i) (\<lambda>g. {}) \<in> possible_pareto" using in_pareto_leq by simp
                              show B: "(iteration ^^ (Suc i)) (\<lambda>g. {}) \<in> possible_pareto" using in_pareto_leq by blast
                              show C: "(iteration ^^ j) (\<lambda>g. {}) \<in> possible_pareto" using in_pareto_leq by simp

                              have D: "(iteration ^^ (Suc i)) (\<lambda>g. {}) = iteration ((iteration ^^ i) (\<lambda>g. {}))" using funpow.simps by simp

                              have "((iteration ^^ i) (\<lambda>g. {})) \<preceq> iteration ((iteration ^^ i) (\<lambda>g. {}))"
                              proof(induct i)
                                case 0
                                then show ?case using pareto_minimal_element in_pareto_leq
                                  by simp 
                              next
                                case (Suc i)
                                then show ?case using in_pareto_leq iteration_monotonic funpow.simps(2)
                                  by (smt (verit, del_insts) comp_eq_dest_lhs)
                              qed
                              thus "(iteration ^^ i) (\<lambda>g. {}) \<preceq> (iteration ^^ (Suc i)) (\<lambda>g. {})"
                                unfolding D by simp

                              have "x = j - (Suc i)" using Suc by simp
                              have "(Suc i) \<le> j"
                                using diff_diff_left Suc by simp
                              show "(iteration ^^ (Suc i)) (\<lambda>g. {}) \<preceq> (iteration ^^ j) (\<lambda>g. {})"
                                using Suc \<open>x = j - (Suc i)\<close> \<open>(Suc i) \<le> j\<close> by blast
                            qed                   
                          qed
                        qed
                      qed
                      thus ?thesis
                        using \<open>F = (iteration ^^ n) (\<lambda>g. {})\<close> \<open>F' = (iteration ^^ m)(\<lambda>g. {})\<close> \<open>F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n}\<close> max.cobounded2 by auto 
                    qed
                  qed
                qed

                show "{(iteration ^^ n) (\<lambda>g. {}) |. n} \<noteq> {}"
                  by auto 
                show "P' \<subseteq> {(iteration ^^ n) (\<lambda>g. {}) |. n}" using P'_def IF
                  by blast 
                have "finite {g'. weight g g' \<noteq> None}" using finite_positions
                  by (smt (verit) Collect_cong finite_Collect_conjI) 
                thus "finite P'" unfolding P'_def using nonpos_eq_pos
                  by auto
                show "{(iteration ^^ n) (\<lambda>g. {}) |. n} \<subseteq> possible_pareto" using in_pareto_leq by auto
              qed
              from this obtain F' where "F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> (\<forall>F. F \<in> P' \<longrightarrow> F \<preceq> F')" by auto
              hence "F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> index_F g' \<preceq> F')"
                using P'_def
                by auto
              thus ?thesis by auto
            qed
            from this obtain F' where F': "F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> (\<forall>g'. weight g g' \<noteq> None \<longrightarrow> index_F g' \<preceq> F')" by auto
            
            have IE: "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> \<exists>e'. e' \<in> F' g' \<and> e' e\<le> index' g'"
            proof-
              fix g'
              assume "weight g g' \<noteq> None"
              hence "index_F g' \<preceq> F'" using F' by simp
              thus "\<exists>e'. e' \<in> F' g' \<and> e' e\<le> index' g'" unfolding pareto_order_def using IF \<open>weight g g' \<noteq> None\<close>
                by simp
            qed

            define e_index where "e_index = (\<lambda>g'. SOME e'.  e' \<in> F' g' \<and> e' e\<le> index' g')"
            hence "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'"
              using IE some_eq_ex
              by (metis (no_types, lifting)) 

            have sup_leq1: "energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None} e\<le> energy_sup dimension {inv_upd (the (weight g g')) (index' g')| g'. weight g g' \<noteq> None}"
            proof(cases "{g'. weight g g' \<noteq> None} = {}")
              case True
              then show ?thesis using empty_Sup_is_zero
                using energy_leq.order_iff_strict by fastforce
            next
              case False
              hence "{inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} \<noteq> {}" by simp
              then show ?thesis 
              proof(rule energy_sup_leq_energy_sup)
                show "\<And>a. a \<in> {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
         \<exists>b\<in>{inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None}. a e\<le> b"
                proof-
                  fix a 
                  assume "a \<in> {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None}"
                  from this obtain g' where "weight g g' \<noteq> None" and "a=inv_upd (the (weight g g')) (e_index g')" by auto
                  have "a e\<le> inv_upd (the (weight g g')) (index' g')"
                    unfolding \<open>a=inv_upd (the (weight g g')) (e_index g')\<close> 
                    using \<open>weight g g' \<noteq> None\<close> 
                  proof(rule inverse_monotonic)
                    show "e_index g' e\<le> index' g'" using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'\<close> \<open>weight g g' \<noteq> None\<close> by auto
                    hence "length (e_index g') = dimension" using index'_len \<open>weight g g' \<noteq> None\<close> energy_leq_def
                      by auto 
                    thus "inverse_application (the (weight g g')) (e_index g') \<noteq> None"
                      using domain_inv \<open>weight g g' \<noteq> None\<close>
                      by auto 
                    show "length (e_index g') = dimension"
                      using \<open>length (e_index g') = dimension\<close> by auto
                  qed
                  thus "\<exists>b\<in>{inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None}. a e\<le> b"
                    using \<open>weight g g' \<noteq> None\<close>
                    by blast 
                qed
                show "\<And>a. a \<in> {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
         length a = dimension"
                  using len_inv_appl  index'_len \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'\<close>
                  using energy_leq_def by force 
              qed             
            qed

            have sup_leq2: "energy_sup dimension {inv_upd (the (weight g g')) (index' g')|g'. weight g g' \<noteq> None} e\<le> energy_sup dimension {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}"
            proof(cases "{g'. weight g g' \<noteq> None} = {}")
              case True
              then show ?thesis using empty_Sup_is_zero
                using energy_leq.order_iff_strict by fastforce
            next
              case False
              hence "{inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None} \<noteq> {}" by simp
              then show ?thesis 
              proof(rule energy_sup_leq_energy_sup)
                show "\<And>a. a \<in> {inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
         \<exists>b\<in>{inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}. a e\<le> b"
                proof-
                  fix a 
                  assume "a \<in> {inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None}"
                  from this obtain g' where "weight g g' \<noteq> None" and "a=inv_upd (the (weight g g')) (index' g')" by auto
                  hence "a e\<le> inv_upd (the (weight g g')) (index g')"
                    using inverse_monotonic  \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'\<close> F' possible_pareto_def
                    using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> index' g' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> index' g' e\<le> index g'\<close> energy_leq_def
                    by (meson domain_inv index'_len) 
                  thus "\<exists>b\<in>{inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}. a e\<le> b"
                    using \<open>weight g g' \<noteq> None\<close>
                    by blast 
                qed
                show "\<And>a. a \<in> {inv_upd (the (weight g g')) (index' g') |g'. weight g g' \<noteq> None} \<Longrightarrow>
         length a = dimension"
                  using len_inv_appl  index'_len by blast 
              qed             
            qed
            

            have "\<And>g'. weight g g' \<noteq> None \<Longrightarrow> length (e_index g') = dimension" 
              using index'_len \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'\<close> energy_leq_def by simp
            hence "energy_sup dimension {inv_upd (the (weight g g')) (e_index g')|g'. weight g g' \<noteq> None} \<in> {energy_sup dimension
                        {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} |
                       e_index.
                       \<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                            length (e_index g') = dimension \<and> e_index g' \<in> F' g'}"
              using \<open>\<And>g'. weight g g' \<noteq> None \<Longrightarrow> e_index g' \<in> F' g' \<and> e_index g' e\<le> index' g'\<close>
              by blast 
            hence "\<exists>em. em \<in>  energy_Min
                      {energy_sup dimension
                        {inv_upd (the (weight g g')) (e_index g') |g'. weight g g' \<noteq> None} |
                       e_index.
                       \<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                            length (e_index g') = dimension \<and> e_index g' \<in> F' g'} 
                  \<and> em e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}"
              using energy_Min_contains_smaller by meson
            hence "\<exists>em. em\<in> iteration F' g \<and> em e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}"
              unfolding iteration_def using A
              by simp 
            from this obtain em where EM: "em \<in> iteration F' g \<and> em e\<le> energy_sup dimension {inv_upd (the (weight g g')) (e_index g')| g'. weight g g' \<noteq> None}"
              by auto
            from F' have F': "iteration F' \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n}" using funpow.simps image_iff rangeE
              by (smt (z3) UNIV_I comp_eq_dest_lhs)
            hence "em \<in> {e. \<exists>F. F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> e \<in> F g}" 
              using EM by auto
            hence "\<exists>em'. em' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> em' e\<le> em"
              unfolding pareto_sup_def using F' energy_Min_contains_smaller by meson
            from this obtain em' where EM': "em' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> em' e\<le> em" by auto
            hence "em' e\<le> e" using EM sup_leq1 sup_leq2 \<open>e =
               energy_sup dimension
                {inv_upd (the (weight g g')) (index g') |g'. weight g g' \<noteq> None}\<close> energy_leq.trans
              by blast 
            thus " \<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e"
              using EM' by auto
          qed

          show "\<And>g e. g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and>
                        (\<exists>e'a. e'a \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'a e\<le> e')) \<and>
                       e = inv_upd (the (weight g g')) e')) \<Longrightarrow>
           \<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e"
          proof-
            fix g e 
            assume A: "g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 (\<exists>e'. (S e' g' \<and>
                        (\<exists>e'a. e'a \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'a e\<le> e')) \<and>
                       e = inv_upd (the (weight g g')) e'))"
            from this obtain g' e' e'' where " weight g g' \<noteq> None" and "S e' g'" and "e = inv_upd (the (weight g g')) e'" and 
                      "e'' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'' e\<le> e'" by auto
            have "inv_upd (the (weight g g')) e'' e\<le> inv_upd (the (weight g g')) e'" 
              using \<open>weight g g' \<noteq> None\<close>
            proof(rule inverse_monotonic)
              show "e'' e\<le> e'" using \<open>e'' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'' e\<le> e'\<close> by auto
              have "length e' = dimension" using length_S \<open>weight g g' \<noteq> None\<close> \<open>S e' g'\<close> by auto
              hence "length e''=  dimension" using \<open>e'' e\<le> e'\<close> energy_leq_def by auto
              thus"inverse_application (the (weight g g')) e'' \<noteq> None"
                using domain_inv \<open>weight g g' \<noteq> None\<close>
                by blast 
              show "length e'' = dimension"
                by (simp add: \<open>length e'' = dimension\<close>)
            qed
            have "e'' \<in> energy_Min {e. \<exists>F. F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> e \<in> F g'}"
              using \<open>e'' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'' e\<le> e'\<close> unfolding pareto_sup_def by simp
            hence "\<exists>n. e'' \<in> (iteration ^^ n) (\<lambda>g. {}) g'"
              using energy_Min_def
              by auto 
            from this obtain n where "e'' \<in> (iteration ^^ n) (\<lambda>g. {}) g'" by auto

            hence e''in: "inv_upd (the (weight g g')) e'' \<in> {inv_upd (the (weight g g')) e' |e' g'.
           length e' = dimension \<and> weight g g' \<noteq> None \<and> e' \<in> (iteration ^^ n) (\<lambda>g. {}) g'}"
              using \<open>weight g g' \<noteq> None\<close> length_S \<open>S e' g'\<close> \<open>e'' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g' \<and> e'' e\<le> e'\<close>
              using energy_leq_def by auto

            define Fn where "Fn =  (iteration ^^ n) (\<lambda>g. {})"

            have "\<exists>e'''. e''' \<in> iteration Fn g \<and> e''' e\<le> inv_upd (the (weight g g')) e''"
              unfolding iteration_def using Fn_def energy_Min_contains_smaller A e''in
              by meson
            from this obtain e''' where E''': "e''' \<in> iteration ((iteration ^^ n) (\<lambda>g. {})) g \<and> e''' e\<le> inv_upd (the (weight g g')) e''"
              using Fn_def by auto 
            hence "e''' \<in> ((iteration ^^ (Suc n)) (\<lambda>g. {})) g" by simp
            hence "e''' \<in> {e. \<exists>F. F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<and> e \<in> F g}" by blast
            hence "\<exists>em. em \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> em e\<le> e'''"
              unfolding pareto_sup_def using energy_Min_contains_smaller
              by meson 
            from this obtain em where EM: "em \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> em e\<le> e'''" by auto

            show " \<exists>e'. e' \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> e' e\<le> e"
            proof
              show "em \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g \<and> em e\<le> e"
              proof
                show "em \<in> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} g" using EM by simp
                have "inv_upd (the (weight g g')) e'' e\<le> e"
                  using \<open>e = inv_upd (the (weight g g')) e'\<close> \<open>inv_upd (the (weight g g')) e'' e\<le> inv_upd (the (weight g g')) e'\<close> by simp
                hence "e''' e\<le> e" using E'''
                  using energy_leq.trans by blast
                thus "em e\<le> e" using EM energy_leq.trans by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed

  thus "a_win_min \<preceq> pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n}" 
    using a_win_min_is_minS Smin_def by simp
qed

text\<open>We can argue that the algorithm always terminates by showing that only finitely many iterations 
are needed before a fixed point (the minimal attacker winning budgets) is reached.\<close>

lemma finite_iterations: 
  shows "\<exists>i. a_win_min = (iteration ^^ i) (\<lambda>g. {})"
proof
  have in_pareto_leq: "\<And>n. (iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
  proof-
    fix n 
    show "(iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
    proof(induct n)
      case 0
      show ?case 
      proof
        show "(iteration ^^ 0) (\<lambda>g. {}) \<in> possible_pareto"
          using funpow.simps possible_pareto_def by auto
        have "(\<lambda>g. {}) \<preceq> a_win_min" 
          unfolding pareto_order_def by simp
        thus "(iteration ^^ 0) (\<lambda>g. {}) \<preceq> a_win_min" using funpow.simps by simp
      qed
    next
      case (Suc n)
      have "(iteration ^^ (Suc n)) (\<lambda>g. {}) = iteration ((iteration ^^ n) (\<lambda>g. {}))" 
        using funpow.simps by simp
      then show ?case using Suc iteration_stays_winning iteration_pareto_functor by simp
    qed
  qed

  have A: "\<And>g n m e. n \<le> m \<Longrightarrow>  e \<in> a_win_min g \<Longrightarrow> e\<in> (iteration ^^ n) (\<lambda>g. {}) g \<Longrightarrow> e \<in> (iteration ^^ m)(\<lambda>g. {}) g"
  proof-
    fix g n m e 
    assume "n \<le> m" and "e \<in> a_win_min g" and "e\<in> (iteration ^^ n) (\<lambda>g. {}) g"
    thus "e\<in>(iteration ^^ m)(\<lambda>g. {}) g"
    proof(induct "m-n" arbitrary: n m)
      case 0
      then show ?case by simp
    next
      case (Suc x)
      hence "Suc n \<le> m"
        by linarith 
      have "x = m - (Suc n)" using Suc by simp
      have "e \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g"
      proof-
        have "(iteration ^^ n) (\<lambda>g. {}) \<preceq> (iteration ^^ (Suc n)) (\<lambda>g. {})"
        proof(induct n)
          case 0
          then show ?case
            by (simp add: pareto_minimal_element)
        next
          case (Suc n)
          have "(iteration ^^ (Suc (Suc n))) (\<lambda>g. {}) = iteration ((iteration ^^ (Suc n)) (\<lambda>g. {}))" 
            using funpow.simps by simp
          then show ?case using Suc iteration_monotonic in_pareto_leq funpow.simps(2)
            by (smt (verit) comp_apply)
        qed
        hence "\<exists>e'. e' \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g \<and> e' e\<le> e"
          unfolding pareto_order_def using Suc by simp
        from this obtain e' where "e' \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g \<and> e' e\<le> e" by auto
        hence "(\<exists>e''. e'' \<in> a_win_min g \<and> e'' e\<le> e')" using in_pareto_leq unfolding pareto_order_def
          by blast 
        from this obtain e'' where "e'' \<in> a_win_min g \<and> e'' e\<le> e'" by auto
        hence "e'' = e" using Suc energy_Min_def \<open>e' \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g \<and> e' e\<le> e\<close>
          by (smt (verit, ccfv_SIG) energy_leq.trans mem_Collect_eq) 
        hence "e = e'" using \<open>e' \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g \<and> e' e\<le> e\<close> \<open>e'' \<in> a_win_min g \<and> e'' e\<le> e'\<close>
          using energy_leq.strict_iff_not by auto
        thus ?thesis using \<open>e' \<in> (iteration ^^ (Suc n)) (\<lambda>g. {}) g \<and> e' e\<le> e\<close> by simp
      qed
      then show ?case using Suc \<open>x = m - (Suc n)\<close> \<open>Suc n \<le> m\<close> by auto
    qed
  qed
  hence A1: "\<And>g n m. n \<le> m \<Longrightarrow>  a_win_min g = (iteration ^^ n) (\<lambda>g. {}) g \<Longrightarrow>  a_win_min g = (iteration ^^ m)(\<lambda>g. {}) g"
  proof-
    fix g n m 
    assume "n \<le> m" and "a_win_min g = (iteration ^^ n) (\<lambda>g. {}) g"
    show "a_win_min g = (iteration ^^ m)(\<lambda>g. {}) g"
    proof
      show "a_win_min g \<subseteq> (iteration ^^ m)(\<lambda>g. {}) g"
      proof
        fix e
        assume "e \<in> a_win_min g"
        hence "e \<in> (iteration ^^ n) (\<lambda>g. {}) g" using \<open>a_win_min g = (iteration ^^ n) (\<lambda>g. {}) g\<close> by simp
        thus "e \<in> (iteration ^^ m)(\<lambda>g. {}) g" using A \<open>n \<le> m\<close> \<open>e \<in> a_win_min g\<close> by auto
      qed
      show "(iteration ^^ m)(\<lambda>g. {}) g \<subseteq> a_win_min g"
      proof
        fix e
        assume "e \<in> (iteration ^^ m)(\<lambda>g. {}) g"
        hence "\<exists>e'. e' \<in> a_win_min g \<and> e' e\<le> e" using in_pareto_leq unfolding pareto_order_def by auto
        from this obtain e' where "e' \<in> a_win_min g \<and> e' e\<le> e" by auto
        hence "e' \<in> (iteration ^^ n) (\<lambda>g. {}) g" using \<open>a_win_min g = (iteration ^^ n) (\<lambda>g. {}) g\<close> by simp
        hence "e' \<in> (iteration ^^ m)(\<lambda>g. {}) g" using A \<open>n \<le> m\<close> \<open>e' \<in> a_win_min g \<and> e' e\<le> e\<close> by simp
        hence "e = e'" using in_pareto_leq unfolding possible_pareto_def
          using \<open>e \<in> (iteration ^^ m)(\<lambda>g. {}) g\<close> \<open>e' \<in> a_win_min g \<and> e' e\<le> e\<close> by blast 
        thus "e \<in> a_win_min g" using \<open>e' \<in> a_win_min g \<and> e' e\<le> e\<close> by simp
      qed
    qed
  qed

  have "\<And>g e. e \<in> a_win_min g \<Longrightarrow> \<exists>n. e \<in> (iteration ^^ n) (\<lambda>g. {}) g"
  proof-
    fix g e
    assume "e \<in> a_win_min g"
    hence "e \<in> (pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n}) g" using a_win_min_is_lfp_sup finite_positions nonpos_eq_pos by simp
    thus "\<exists>n. e \<in> (iteration ^^ n) (\<lambda>g. {}) g" unfolding pareto_sup_def energy_Min_def
      by auto 
  qed
  define n_e where "n_e = (\<lambda> g e. SOME n. e \<in> (iteration ^^ n) (\<lambda>g. {}) g)"
  hence "\<And>g e. n_e g e = (SOME n. e \<in> (iteration ^^ n) (\<lambda>g. {}) g)"
    by simp
  hence n_e: "\<And>g e. e \<in> a_win_min g \<Longrightarrow> e \<in> (iteration ^^ (n_e g e)) (\<lambda>g. {}) g"
    using some_eq_ex \<open>\<And>g e. e \<in> a_win_min g \<Longrightarrow> \<exists>n. e \<in> (iteration ^^ n) (\<lambda>g. {}) g\<close>
    by metis

  have fin_e: "\<And>g. finite {n_e g e | e. e \<in> a_win_min g}"
    using minimal_winning_budget_finite by fastforce  
  define m_g where "m_g = (\<lambda>g. Max {n_e g e | e. e \<in> a_win_min g})"
  hence n_e_leq: "\<And>g e. e \<in> a_win_min g \<Longrightarrow> n_e g e \<le> m_g g" using A fin_e
    using Collect_mem_eq Max.coboundedI by fastforce 
  have MG: "\<And>g. a_win_min g = (iteration ^^ (m_g g)) (\<lambda>g. {}) g"
  proof
    fix g 
    show "a_win_min g \<subseteq> (iteration ^^ (m_g g)) (\<lambda>g. {}) g"
    proof
      fix e 
      assume "e\<in> a_win_min g" 
      hence "e \<in> (iteration ^^ (n_e g e)) (\<lambda>g. {}) g"
        using n_e by simp
      thus "e \<in> (iteration ^^ (m_g g)) (\<lambda>g. {}) g"
        using A \<open>e\<in> a_win_min g\<close> n_e_leq
        by blast 
    qed
    show "(iteration ^^ (m_g g)) (\<lambda>g. {}) g \<subseteq> a_win_min g"
    proof
      fix e 
      assume "e \<in> (iteration ^^ (m_g g)) (\<lambda>g. {}) g"
      hence "\<exists>e'. e' \<in> a_win_min g \<and> e' e\<le> e" 
        using in_pareto_leq unfolding pareto_order_def      
        by simp 
      from this obtain e' where "e' \<in> a_win_min g \<and> e' e\<le> e" by auto
      hence "e' \<in> (iteration ^^ (m_g g)) (\<lambda>g. {}) g" using \<open>a_win_min g \<subseteq> (iteration ^^ (m_g g)) (\<lambda>g. {}) g\<close> by auto
      hence "e = e'" using \<open>e' \<in> a_win_min g \<and> e' e\<le> e\<close> in_pareto_leq unfolding possible_pareto_def
        using \<open>e \<in> (iteration ^^ (m_g g)) (\<lambda>g. {}) g\<close> by blast 
      thus "e \<in> a_win_min g" using \<open>e' \<in> a_win_min g \<and> e' e\<le> e\<close> by auto
    qed
  qed

  have fin_m: "finite {m_g g| g. g\<in>positions}"
  proof-
    have "finite {p. p \<in> positions}"
      using finite_positions by fastforce
    then show ?thesis
      using finite_image_set by blast
  qed
  hence "\<And>g. m_g g \<le> Max {m_g g| g. g \<in> positions}"
    using Max_ge by blast 
  have "\<And>g. a_win_min g = (iteration ^^ (Max {m_g g| g. g \<in> positions})) (\<lambda>g. {}) g"
  proof-
    fix g 
    have G: "a_win_min g = (iteration ^^ (m_g g)) (\<lambda>g. {}) g" using MG by simp

    from fin_m have "\<And>g. m_g g \<le> Max {m_g g| g. g \<in> positions}"
      using Max_ge by blast
    thus "a_win_min g = (iteration ^^ (Max {m_g g| g. g \<in> positions})) (\<lambda>g. {}) g"
      using A1 G by simp
  qed

  hence "a_win_min \<preceq> (iteration ^^ (Max {m_g g| g. g \<in> positions})) (\<lambda>g. {})" 
    using pareto_order_def
    using in_pareto_leq by auto
  thus "a_win_min = (iteration ^^ (Max {m_g g| g. g \<in> positions})) (\<lambda>g. {})"
    using in_pareto_leq \<open>\<And>g. a_win_min g = (iteration ^^ (Max {m_g g| g. g \<in> positions})) (\<lambda>g. {}) g\<close> by auto
qed

subsection\<open>Applying Kleene's Fixed Point Theorem\<close>

text\<open>We now establish compatablity with Complete\_Non\_Orders.thy.\<close>

sublocale attractive possible_pareto pareto_order
  unfolding attractive_def using pareto_partial_order(2,3) 
  by (smt (verit) attractive_axioms_def semiattractiveI transp_on_def)

abbreviation pareto_order_dual (infix "\<succeq>" 80) where 
  "pareto_order_dual \<equiv> (\<lambda>x y. y \<preceq> x)"

text\<open>We now conclude, that Kleene's fixed point theorem is applicable.\<close>

lemma kleene_lfp_iteration:
  shows "extreme_bound possible_pareto (\<preceq>) {(iteration ^^ i) (\<lambda>g. {}) |. i} =
        extreme {s \<in> possible_pareto. sympartp (\<preceq>) (iteration s) s} (\<succeq>)"
proof(rule kleene_qfp_is_dual_extreme)
  show "omega_chain-complete possible_pareto (\<preceq>)"
    unfolding omega_chain_def complete_def 
  proof
    fix P 
    show "P \<subseteq> possible_pareto \<longrightarrow>
         (\<exists>f. monotone (\<le>) (\<preceq>) f \<and> range f = P) \<longrightarrow> (\<exists>s. extreme_bound possible_pareto (\<preceq>) P s)"
    proof
      assume "P \<subseteq> possible_pareto"
      show "(\<exists>f. monotone (\<le>) (\<preceq>) f \<and> range f = P) \<longrightarrow> (\<exists>s. extreme_bound possible_pareto (\<preceq>) P s) "
      proof
        assume "\<exists>f. monotone (\<le>) (\<preceq>) f \<and> range f = P"
        show "\<exists>s. extreme_bound possible_pareto (\<preceq>) P s"
        proof
          show "extreme_bound possible_pareto (\<preceq>) P (pareto_sup P)"
            unfolding extreme_bound_def extreme_def using pareto_sup_is_sup
            using \<open>P \<subseteq> possible_pareto\<close> by fastforce
        qed
      qed
    qed
  qed
  show "omega_chain-continuous possible_pareto (\<preceq>) possible_pareto (\<preceq>) iteration"
    using finite_positions iteration_scott_continuous scott_continuous_imp_omega_continuous by simp
  show "(\<lambda>g. {}) \<in> possible_pareto"
    unfolding possible_pareto_def
    by simp
  show "\<forall>x\<in>possible_pareto. x \<succeq> (\<lambda>g. {})"
    using pareto_minimal_element
    by simp
qed

text\<open>We now apply Kleene's fixed point theorem, showing that minimal attacker winning budgets are the least fixed point.\<close>

lemma a_win_min_is_lfp:
  shows "extreme {s \<in> possible_pareto. (iteration s) = s} (\<succeq>) a_win_min"
proof-
  have in_pareto_leq: "\<And>n. (iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
  proof-
    fix n 
    show "(iteration ^^ n) (\<lambda>g. {}) \<in> possible_pareto \<and> (iteration ^^ n) (\<lambda>g. {}) \<preceq> a_win_min"
    proof(induct n)
      case 0
      show ?case 
      proof
        show "(iteration ^^ 0) (\<lambda>g. {}) \<in> possible_pareto"
          using funpow.simps possible_pareto_def by auto
        have "(\<lambda>g. {}) \<preceq> a_win_min" 
          unfolding pareto_order_def by simp
        thus "(iteration ^^ 0) (\<lambda>g. {}) \<preceq> a_win_min" using funpow.simps by simp
      qed
    next
      case (Suc n)
      have "(iteration ^^ (Suc n)) (\<lambda>g. {}) = iteration ((iteration ^^ n) (\<lambda>g. {}))" 
        using funpow.simps by simp
      then show ?case using Suc iteration_stays_winning iteration_pareto_functor by simp
    qed
  qed

  have "extreme_bound possible_pareto (\<preceq>) {(iteration ^^ n) (\<lambda>g. {}) |. n} a_win_min"
  proof
    show "\<And>b. bound {(iteration ^^ n) (\<lambda>g. {}) |. n} (\<preceq>) b \<Longrightarrow> b \<in> possible_pareto \<Longrightarrow> b \<succeq> a_win_min"
    proof-
      fix b 
      assume "bound {(iteration ^^ n) (\<lambda>g. {}) |. n} (\<preceq>) b" and "b \<in> possible_pareto"
      hence "\<And>n. (iteration ^^ n) (\<lambda>g. {}) \<preceq> b"
        by blast  
      hence "pareto_sup {(iteration ^^ n) (\<lambda>g. {}) |. n} \<preceq> b" 
        using pareto_sup_is_sup in_pareto_leq \<open>b \<in> possible_pareto\<close>
        using nonpos_eq_pos finite_iterations a_win_min_is_lfp_sup by auto
      thus "b \<succeq> a_win_min" 
        using nonpos_eq_pos a_win_min_is_lfp_sup
        by simp 
    qed
    show "\<And>x. x \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n} \<Longrightarrow> a_win_min \<succeq> x"
    proof-
      fix F
      assume "F \<in> {(iteration ^^ n) (\<lambda>g. {}) |. n}"
      thus "a_win_min \<succeq> F" 
        using pareto_sup_is_sup in_pareto_leq by force 
    qed

    show "a_win_min \<in> possible_pareto"
      by (simp add: a_win_min_in_pareto)
  qed

  thus "extreme {s \<in> possible_pareto. (iteration s) = s} (\<succeq>) a_win_min"
    using kleene_lfp_iteration nonpos_eq_pos
    by (smt (verit, best) Collect_cong antisymmetry iteration_pareto_functor reflexivity sympartp_def) 
qed

end
end