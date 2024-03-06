theory Two_nested_sim
imports Transition_Systems HML formula_prices_list Simulation
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
inductive hml_2_nested_sim :: "('a, 's) hml \<Rightarrow> bool" 
  where
"hml_2_nested_sim TT" |
"hml_2_nested_sim (hml_pos \<alpha> \<phi>)" if "hml_2_nested_sim \<phi>" |
"hml_2_nested_sim (hml_conj I J \<Phi>)" 
if "(\<forall>x \<in> (\<Phi> ` I). hml_2_nested_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). hml_simulation y)"

definition hml_2_nested_sim_formulas where
"hml_2_nested_sim_formulas \<equiv> {\<phi>. hml_2_nested_sim \<phi>}"

definition expr_2_nested_sim
  where
"expr_2_nested_sim = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, \<infinity>, 1))}"

context lts
begin

definition expr_2_nested_sim_equivalent
  where
"expr_2_nested_sim_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_2_nested_sim \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

lemma nested_sim_right:
  assumes "hml_2_nested_sim \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, \<infinity>, 1)"
using assms
proof(induction \<phi> rule: hml_2_nested_sim.induct)
  case 1
  then show ?case by simp
next
  case (2 \<phi> \<alpha>)
  then show ?case 
    by simp
next
  case (3 \<Phi> I J)
  hence fa: "\<forall>y\<in>\<Phi> ` J. less_eq_t (expr y) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
    using simulation_right by blast
  hence "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using expr.simps less_eq_t.simps
     apply (metis "3" SUP_image SUP_least)
    using fa
    by (metis SUP_image SUP_least expr.simps less_eq_t.simps)
  hence "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    by (smt (verit, del_insts) Sup_union_distrib comp_assoc complete_linorder_sup_max dual_order.order_iff_strict eSuc_Sup expr_6.expr_6_conj image_comp image_is_empty le_zero_eq max_def one_eSuc)
  then show ?case 
    by simp
qed

lemma e5_e6_ge_1: 
  fixes \<phi>
  assumes "expr_5 \<phi> \<ge> 1"
  shows "expr_6 \<phi> \<ge> 1"
  using assms
proof(induction \<phi>)
  case TT
  then have "expr_5 TT = 0"
    using expr_5_tt by blast
  with TT have False
    by fastforce
  then show ?case by blast
next
  case (hml_pos x1 \<phi>)
  hence "1 \<le> expr_6 \<phi>"
    by force
  then show ?case
    by force
next
  case (hml_conj x1 x2 x3)
  have "expr_5 (hml_conj x1 x2 x3) = (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))"
    using expr_5_conj by blast
  hence "1 \<le> (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))"
    using hml_conj(2) dual_order.trans 
    by simp
  have e6_eq: "expr_6 (hml_conj x1 x2 x3) = (Sup ((expr_6 \<circ> x3) ` x1 \<union> ((eSuc \<circ> expr_6 \<circ> x3) ` x2)))"
    using expr_6_conj
    by force
  have "(x3 ` x2 \<noteq> {}) \<longrightarrow> Sup(((eSuc \<circ> expr_6 \<circ> x3) ` x2)) \<ge> 1"
    using eSuc_def 
    by (metis eSuc_Sup eSuc_ile_mono empty_iff equals0I i0_lb imageI image_comp one_eSuc)
  hence "(x3 ` x2 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)"
    by (simp add: Sup_union_distrib le_supI2)
  have "(x3 ` x2 = {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)"
  proof
    assume "x3 ` x2 = {}"
    hence "1 \<le> (Sup ((expr_5 \<circ> x3) ` x1))" 
      using \<open>1 \<le> (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))\<close>
      using bot_enat_def by force
    then obtain x where "x \<in> (x3 ` x1)" "1 \<le> expr_5 x"
      using bot_enat_def comp_apply
      by (metis (no_types, lifting) SUP_bot_conv(2) iless_eSuc0 image_eqI linorder_not_le one_eSuc)
    hence "1 \<le> expr_6 x"
      using hml_conj
      by blast
    hence "Sup ((expr_6 \<circ> x3) ` x1) \<ge> 1"
      using \<open>x \<in> (x3 ` x1)\<close> SUP_image SUP_lessD linorder_not_le 
      by metis
    then show "1 \<le> expr_6 (hml_conj x1 x2 x3)" 
      using expr_6_conj e6_eq Un_empty_right image_is_empty 
      using \<open>x3 ` x2 = {}\<close> by auto
  qed
  with \<open>(x3 ` x2 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)\<close> 
  show "1 \<le> expr_6 (hml_conj x1 x2 x3)"
    by blast
qed

lemma nested_sim_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, \<infinity>, 1)"
  shows "hml_2_nested_sim \<phi>"
using assms
proof (induction \<phi>)
  case TT
  then show ?case 
    using hml_2_nested_sim.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    by (simp add: hml_2_nested_sim.intros(2))
next
  case (hml_conj I J \<Phi>)
  hence sup: "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    using expr.simps less_eq_t.simps expr_6.expr_6_conj
    by auto
  hence "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 1"
    by (metis Sup_le_iff UnCI comp_apply image_iff)
  hence "\<forall>x \<in> \<Phi> ` I. hml_2_nested_sim x"
    using hml_conj 
    by force
  from sup have "\<forall>x \<in> \<Phi> ` J. expr_6 x \<le> 0"
    using eSuc_def Sup_le_iff comp_apply
    by (metis Un_iff eSuc_ile_mono image_iff one_eSuc)
  hence "\<forall>x \<in> \<Phi> ` J. expr_5 x \<le> 0"
    using e5_e6_ge_1 iless_eSuc0 linorder_not_le one_eSuc by fastforce
  hence "\<forall>x \<in> \<Phi> ` J. hml_simulation x"
    using \<open>\<forall>x \<in> \<Phi> ` J. expr_6 x \<le> 0\<close> simulation_left 
    by fastforce
  then show ?case 
    using \<open>\<forall>x \<in> \<Phi> ` I. hml_2_nested_sim x\<close> hml_2_nested_sim.intros(3) by blast
qed

end