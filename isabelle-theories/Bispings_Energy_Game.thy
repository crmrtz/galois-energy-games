section \<open>Bisping's Declining Energy Games\<close>

theory Bispings_Energy_Game
  imports Energy_Game Update Decidability
begin

text\<open>Bisping's only considers declining energy games over vectors of naturals. We generalise this by considering all valid updates. 
We formalise this in this theory as an \<open>energy_game\<close> with a fixed dimension and show that such games are Galois energy games. \<close>

locale bispings_energy_game = energy_game attacker weight apply_update 
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> update option"
+ 
  fixes dimension :: "nat"
  assumes
    valid_updates: "\<forall>p. \<forall>p'. ((weight p p' \<noteq> None ) 
                    \<longrightarrow> ((length (the (weight p p')) = dimension) 
                    \<and> valid_update (the (weight p p'))))"

sublocale bispings_energy_game \<subseteq> galois_energy_game attacker weight apply_update apply_inv_update dimension
proof
  show "\<And>p p' e e'. weight p p' \<noteq> None \<Longrightarrow> e e\<le> e' \<Longrightarrow> apply_w p p' e \<noteq> None \<Longrightarrow> apply_w p p' e' \<noteq> None"
    using upd_domain_upward_closed
    by blast
  show "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> apply_w p p' e \<noteq> None \<Longrightarrow> length (upd (the (weight p p')) e) = length e"
    using len_appl
    by simp
  show "\<And>p p' e. weight p p' \<noteq> None \<Longrightarrow> length e = dimension \<Longrightarrow> length (inv_upd (the (weight p p')) e) = length e"
    using len_inv_appl valid_updates
    by blast
  show "\<And>p p' e.
       weight p p' \<noteq> None \<Longrightarrow>
       length e = dimension \<Longrightarrow>
       apply_inv_update (the (weight p p')) e \<noteq> None \<and> apply_w p p' (inv_upd (the (weight p p')) e) \<noteq> None"
    using  inv_not_none  inv_not_none_then
    using valid_updates by presburger
  show "\<And>p p' e e'.
       weight p p' \<noteq> None \<Longrightarrow>
       apply_w p p' e' \<noteq> None \<Longrightarrow>
       length e = dimension \<Longrightarrow>
       length e' = dimension \<Longrightarrow> inv_upd (the (weight p p')) e e\<le> e' = e e\<le> upd (the (weight p p')) e'"
    using galois_connection
    by (metis valid_updates) 
qed

locale bispings_energy_game_assms = bispings_energy_game attacker weight dimension
  for attacker ::  "'position set" and 
      weight :: "'position \<Rightarrow> 'position \<Rightarrow> update option" and 
      dimension :: "nat"
+
assumes nonpos_eq_pos: "nonpos_winning_budget = winning_budget" and
        finite_positions: "finite positions"

sublocale bispings_energy_game_assms \<subseteq> galois_energy_game_assms attacker weight apply_update apply_inv_update dimension
proof
  show "nonpos_winning_budget = winning_budget" using nonpos_eq_pos.
  show "finite positions" using finite_positions .
qed

end