section \<open>Bisping's Declining Energy Games\<close>

theory Bispings_Energy_Game
  imports Energy_Game Update
begin

text\<open>Bisping's declining energy games are energy games with only valid updates
and a fixed dimension. 
In this theory we introduce Bisping's declining energy games. \<close>

locale bispings_energy_game = energy_game attacker weight apply_update 
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> update option"
+ 
  fixes dimension :: "nat"
  assumes
    valid_updates: "\<forall>p. \<forall>p'. ((weight p p' \<noteq> None ) 
                    \<longrightarrow> ((length (the (weight p p')) = dimension) 
                    \<and> valid_update (the (weight p p'))))"
begin

text\<open>The set of energies is \<open>{e::energy. length e = dimension}\<close>. For this reason length checks are needed 
and we redefine attacker winning budgets.\<close>

inductive winning_budget_len::"energy \<Rightarrow> 'position \<Rightarrow> bool" where
 defender: "winning_budget_len e g" if "length e = dimension \<and> g \<notin> attacker 
            \<and> (\<forall>g'. (weight g g' \<noteq> None) \<longrightarrow> 
                    ((apply_update (the (weight g g')) e)\<noteq> None 
                     \<and> (winning_budget_len (upd (the (weight g g')) e)) g'))" |
 attacker: "winning_budget_len e g" if "length e = dimension \<and> g \<in> attacker 
            \<and> (\<exists>g'. (weight g g' \<noteq> None) 
                    \<and> (apply_update (the (weight g g')) e)\<noteq> None 
                    \<and> (winning_budget_len (upd (the (weight g g')) e) g'))"

text\<open>We first restate the upward-closure of winning budgets.\<close>

lemma upwards_closure_wb_len:
  assumes "winning_budget_len e g" and "e e\<le> e'"
  shows "winning_budget_len e' g"
using assms proof (induct arbitrary: e' rule: winning_budget_len.induct)
  case (defender e g)
  have "(\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
          apply_update (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e')) g')" 
  proof
    fix g'
    show " weight g g' \<noteq> None \<longrightarrow>
          apply_update (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e')) g'" 
    proof
      assume "weight g g' \<noteq> None"
      hence A: "apply_update (the (weight g g')) e \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e)) g'" using assms(1) winning_budget_len.simps defender by blast
      show "apply_update (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e')) g'" 
      proof
        show "apply_update (the (weight g g')) e' \<noteq> None" using upd_domain_upward_closed assms(2) A defender by blast
        have "energy_leq (the (apply_update (the (weight g g')) e)) (the (apply_update (the (weight g g')) e'))" using assms A updates_monotonic valid_updates
          by (metis (mono_tags, lifting) Collect_cong \<open>weight g g' \<noteq> None\<close> apply_update.simps defender.prems) 
        thus "winning_budget_len (the (apply_update (the (weight g g')) e')) g'" using defender \<open>weight g g' \<noteq> None\<close> by blast
      qed
    qed
  qed
thus ?case using winning_budget_len.intros(1) defender
    by (smt (verit, del_insts) energy_leq_def)
next
  case (attacker e g)
  from this obtain g' where G: "weight g g' \<noteq> None \<and>
          apply_update (the (weight g g')) e \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e)) g' \<and>
          (\<forall>x. energy_leq (the (apply_update (the (weight g g')) e)) x \<longrightarrow> winning_budget_len x g')" by blast
  have "weight g g' \<noteq> None \<and>
          apply_update (the (weight g g')) e' \<noteq> None \<and>
          winning_budget_len (the (apply_update (the (weight g g')) e')) g'" 
  proof
    show "weight g g' \<noteq> None" using G by auto
    show "apply_update (the (weight g g')) e' \<noteq> None \<and> winning_budget_len (the (apply_update (the (weight g g')) e')) g' " 
    proof
      show "apply_update (the (weight g g')) e' \<noteq> None" using G  upd_domain_upward_closed assms attacker by blast
      have "energy_leq (the (apply_update (the (weight g g')) e)) (the (apply_update (the (weight g g')) e'))" using assms G updates_monotonic valid_updates
          by (metis (mono_tags, lifting) Collect_cong \<open>weight g g' \<noteq> None\<close> apply_update.simps attacker.prems) 
      thus "winning_budget_len (the (apply_update (the (weight g g')) e')) g' " using G by blast
    qed
  qed
  thus ?case using winning_budget_len.intros(2) attacker by (smt (verit, del_insts) energy_leq_def)
qed

text\<open>We now show that this definition is consistent with our previous definition of winning budgets.
We show this by well-founded induction.\<close>

abbreviation "reachable_positions_len s g e \<equiv> {(g',e') \<in> reachable_positions s g e . length e' = dimension}"

lemma winning_bugget_len_is_wb:
  assumes "nonpos_winning_budget = winning_budget"
  shows "winning_budget_len e g = (winning_budget e g \<and> length e = dimension)"
proof
  assume "winning_budget_len e g"
  show "winning_budget e g \<and> length e = dimension"
  proof
    have "winning_budget_ind e g" 
      using \<open>winning_budget_len e g\<close> proof(rule winning_budget_len.induct)
      show "\<And>e g. length e = dimension \<and>
           g \<notin> attacker \<and>
           (\<forall>g'. weight g g' \<noteq> None \<longrightarrow>
                 apply_w g g' e \<noteq> None \<and>
                 winning_budget_len (upd (the (weight g g')) e) g' \<and>
                 winning_budget_ind (upd (the (weight g g')) e) g') \<Longrightarrow>
           winning_budget_ind e g"
        using winning_budget_ind.simps
        by meson 
      show "\<And>e g. length e = dimension \<and>
           g \<in> attacker \<and>
           (\<exists>g'. weight g g' \<noteq> None \<and>
                 apply_w g g' e \<noteq> None \<and>
                 winning_budget_len (upd (the (weight g g')) e) g' \<and>
                 winning_budget_ind (upd (the (weight g g')) e) g') \<Longrightarrow>
           winning_budget_ind e g "
        using winning_budget_ind.simps
        by meson 
    qed
    thus "winning_budget e g" using assms inductive_winning_budget
      by fastforce 
    show "length e = dimension" using \<open>winning_budget_len e g\<close> winning_budget_len.simps by blast 
  qed
next
  show "winning_budget e g \<and> length e = dimension \<Longrightarrow> winning_budget_len e g" 
  proof-
    assume A: "winning_budget e g \<and> length e = dimension"
    hence "winning_budget_ind e g" using assms inductive_winning_budget by fastforce
    show "winning_budget_len e g" 
    proof-

      define wb where "wb \<equiv> \<lambda>(g,e). winning_budget_len e g"

      from A have "\<exists>s. attacker_winning_strategy s e g" using winning_budget.simps by blast
      from this obtain s where S: "attacker_winning_strategy s e g" by auto

      have "reachable_positions_len s g e \<subseteq> reachable_positions s g e" by auto
      hence "wfp_on (strategy_order s) (reachable_positions_len s g e)" 
        using strategy_order_well_founded S
        using Restricted_Predicates.wfp_on_subset by blast
      hence "inductive_on (strategy_order s) (reachable_positions_len s g e)"
        by (simp add: wfp_on_iff_inductive_on)

      hence "wb (g,e)" 
      proof(rule inductive_on_induct)
        show "(g,e) \<in> reachable_positions_len s g e"
          unfolding reachable_positions_def proof-
          have "lfinite LNil \<and>
             llast (LCons g LNil) = g \<and>
             valid_play (LCons g LNil) \<and> play_consistent_attacker s (LCons g LNil) e \<and>
            Some e = energy_level e (LCons g LNil) (the_enat (llength LNil))"
            using valid_play.simps play_consistent_attacker.simps energy_level.simps
            by (metis lfinite_code(1) llast_singleton llength_LNil neq_LNil_conv the_enat_0) 
          thus "(g, e) \<in> {(g', e').
        (g', e')
        \<in> {(g', e') |g' e'.
            \<exists>p. lfinite p \<and>
                llast (LCons g p) = g' \<and>
                valid_play (LCons g p) \<and>
                play_consistent_attacker s (LCons g p) e \<and>
                Some e' = energy_level e (LCons g p) (the_enat (llength p))} \<and>
        length e' = dimension}" using A

            by blast 
        qed

        show "\<And>y. y \<in> reachable_positions_len s g e \<Longrightarrow>
              (\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
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
       
          show "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x) \<Longrightarrow> wb y"
          proof-
            assume ind: "(\<And>x. x \<in> reachable_positions_len s g e \<Longrightarrow> strategy_order s x y \<Longrightarrow> wb x)"
            have "winning_budget_len e' g'" 
            proof(cases "g' \<in> attacker")
              case True 
              then show ?thesis 
              proof(cases "deadend g'")
                case True (* wiederspruchsbeweis *)
                hence "attacker_stuck (LCons g p)" using \<open>g' \<in> attacker\<close> P
                  by (meson A defender_wins_play_def attacker_winning_strategy.elims(2)) 
                hence "defender_wins_play e (LCons g p)" using defender_wins_play_def by simp
                have "\<not>defender_wins_play e (LCons g p)" using P A S by simp
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

                have x_len: "length (upd (the (weight g' (the (s e' g')))) e') = dimension" using y_len valid_updates
                  by (metis P' \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> len_appl option.discI)
                hence "x \<in> reachable_positions_len s g e" using P' reachable_positions_def x_def by auto

                have "(apply_w g' (the (s e' g')) e') \<noteq> None" using P'
                  by (metis \<open>energy_level e (LCons g p') (the_enat (llength p')) = apply_w g' (the (s e' g')) e'\<close> option.distinct(1)) 
    
                have "Some (the (apply_w g' (the (s e' g')) e')) = apply_w g' (the (s e' g')) e' \<and> (if g' \<in> attacker then Some (the (s e' g')) = s e' g' else weight g' (the (s e' g')) \<noteq> None)"
                  using \<open>(s e' g') \<noteq> None \<and> (weight g' (the (s e' g')))\<noteq>None\<close> \<open>(apply_w g' (the (s e' g')) e') \<noteq> None\<close> by simp
                hence "strategy_order s x y" unfolding strategy_order_def using x_def \<open>y = (g', e')\<close>
                  by blast
                hence "wb x" using ind \<open>x \<in> reachable_positions_len s g e\<close> by simp
                hence "winning_budget_len (the (apply_w g' (the (s e' g')) e')) (the (s e' g'))" using wb_def x_def by simp
                then show ?thesis using \<open>g' \<in> attacker\<close> winning_budget_ind.simps
                  by (metis \<open>apply_w g' (the (s e' g')) e' \<noteq> None\<close> \<open>s e' g' \<noteq> None \<and> weight g' (the (s e' g')) \<noteq> None\<close> len_appl winning_budget_len.attacker x_len) 
              qed
            next
              case False
              hence "g' \<notin> attacker \<and>
            (\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g'')"
              proof
                show "\<forall>g''. weight g' g'' \<noteq> None \<longrightarrow>
          apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g''"
                proof
                  fix g''
                  show "weight g' g'' \<noteq> None \<longrightarrow>
           apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g'' "
                  proof
                    assume "weight g' g'' \<noteq> None"
                    show "apply_w g' g'' e' \<noteq> None \<and> winning_budget_len (the (apply_w g' g'' e')) g''"
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
                      have "wb x" 
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

                        have x_len: "length (upd (the (weight g' g'')) e') = dimension" using y_len valid_updates
                          using \<open>apply_w g' g'' e' \<noteq> None\<close> len_appl by blast 

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

                      thus "winning_budget_len (the (apply_w g' g'' e')) g'' " using x_def wb_def 
                        by force 
                    qed
                  qed
                qed
              qed
              thus ?thesis using winning_budget_len.intros y_len by blast
            qed
            thus "wb y" using \<open>y = (g', e')\<close> wb_def by simp
          qed
        qed
      qed
      thus ?thesis using wb_def by simp
    qed
  qed
qed

end
end