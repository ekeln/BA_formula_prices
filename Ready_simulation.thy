theory Ready_simulation
imports Transition_Systems HML formula_prices_list Simulation Ready_traces
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
text \<open>\<close>
inductive hml_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"hml_ready_sim TT" |
"hml_ready_sim (hml_pos \<alpha> \<phi>)" if "hml_ready_sim \<phi>" |
"hml_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). hml_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). (\<exists>\<alpha>. y = (hml_pos \<alpha> TT)))"

definition hml_ready_sim_formulas where
"hml_ready_sim_formulas \<equiv> {\<phi>. hml_ready_sim \<phi>}"

definition expr_ready_sim
  where
"expr_ready_sim = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1))}"

context lts
begin

definition expr_ready_sim_equivalent 
  where
"expr_ready_sim_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_ready_sim \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

text \<open>Proposition\<close>

inductive HML_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"HML_ready_sim TT" |
"HML_ready_sim (hml_pos \<alpha> \<phi>)" if "HML_ready_sim \<phi>" |
"HML_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). HML_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"

lemma expr_single_pos_pos:
  assumes "single_pos_pos \<phi>"
  shows "less_eq_t (expr \<phi>) (1, \<infinity>, 1, 1, 0, 0)"
  using assms
proof(induction \<phi>)
  case 1
  then show ?case by simp
next
  case (2 \<psi> \<alpha>)
  hence "less_eq_t (expr \<psi>) (0, \<infinity>, 0, 0, 0, 0)"
    using expr_nested_empty_pos_conj by auto
  then show ?case 
    by simp
next
  case (3 \<Phi> I J)
  hence "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1"
    by (simp add: SUP_least)
  hence "expr_1 (hml_conj I J \<Phi>) \<le> 1"
    by simp
  from 3 have "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1"
"Sup((expr_3 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 1"
    
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> apply fastforce
    using 3 
     apply (simp add: Sup_enat_def)
    using 3 
    by (simp add: SUP_least)
  hence "(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J)) \<le> 1"
    using Sup_union_distrib
    by (metis "3.hyps" Un_empty_right empty_is_image sup_least)
  hence "expr_3 (hml_conj I J \<Phi>) \<le> 1"
    by simp
  from 3 have "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 1"
    by (smt (z3) SUP_image SUP_least Sup_union_distrib \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> dual_order.trans expr.simps image_is_empty less_eq_t.simps mon_expr_1_pos_r sup.bounded_iff sup_bot.right_neutral)
  hence "expr_4 (hml_conj I J \<Phi>) \<le> 1"
    by (metis expr_4_conj)
  from 3 have "expr_5 (hml_conj I J \<Phi>) <= 0"
"expr_6 (hml_conj I J \<Phi>) <= 0"
     apply (metis SUP_image SUP_least expr.simps expr_5_conj image_is_empty less_eq_t.simps sup_bot_right)
    using 3 SUP_image SUP_least expr.simps image_is_empty less_eq_t.simps sup_bot_right
    by (metis expr_6.expr_6_conj)
  then show ?case 
    by (metis \<open>expr_1 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_3 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_4 (hml_conj I J \<Phi>) \<le> 1\<close> enat_ord_code(3) expr.elims less_eq_t.simps)
qed

lemma ready_sim_right:
  assumes "HML_ready_sim \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
  using assms
proof(induction \<phi> rule:HML_ready_sim.induct)
  case 1
  then show ?case 
    by simp 
next
  case (2 \<phi> \<alpha>) 
  then show ?case 
    by simp
next
  case (3 \<Phi> I J)
  hence "\<forall>y\<in>\<Phi> ` J. less_eq_t (expr y) (1, \<infinity>, 1, 1, 0, 0)"
    using expr_single_pos_pos 
    by (metis Ready_traces.single_pos_pos.intros(2) nested_empty_pos_conj.intros(1))
  hence fa_neg: "\<forall>y \<in>\<Phi> ` J.  expr_1 y \<le> 1"
"\<forall>y \<in>\<Phi> ` J.  expr_5 y \<le> 0"
"\<forall>y \<in>\<Phi> ` J.  expr_6 y \<le> 0"
    using less_eq_t.simps expr.simps 
    by force+
  from 3 have "\<forall>x\<in>\<Phi> ` I. less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
    by blast
  hence fa_pos: "\<forall>x \<in>\<Phi> ` I.  expr_5 x \<le> 1"
"\<forall>x \<in>\<Phi> ` I.  expr_6 x \<le> 1"
    using less_eq_t.simps expr.simps 
    by force+
  with fa_neg have e5: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
    by (simp add: SUP_least Sup_union_distrib)
  from fa_neg have "Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def 
    by (simp add: SUP_least one_eSuc)
  with fa_neg fa_pos have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    by (simp add: SUP_least Sup_union_distrib)
  then show ?case using e5 less_eq_t.simps expr.simps 
    by simp
qed

lemma expr_5_expr_6_le_1_stacked_pos_conj_J_empty_neg:
  assumes "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 1"
  shows "(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_J_empty y)"
proof
  fix y
  assume "y \<in> \<Phi> ` J"
  have sup: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
"(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    using assms expr_5_conj expr_6_conj
    by force+
  hence "expr_5 y \<le> 1" "expr_1 y \<le> 1" "expr_6 y \<le> 0"
      prefer 3 using \<open>y \<in> \<Phi> ` J\<close> sup 
    apply (metis Sup_le_iff UnCI comp_apply eSuc_ile_mono image_iff one_eSuc)
    using \<open>y \<in> \<Phi> ` J\<close> sup 
    by (metis Sup_le_iff UnCI comp_apply image_iff)+
  then show "stacked_pos_conj_J_empty y"
  proof(induction y)
    case TT
    then show ?case 
      using stacked_pos_conj_J_empty.intros(1) by blast
  next
    case (hml_pos x1 \<chi>)
    hence "expr_1 \<chi> \<le> 0"
"expr_6 \<chi> \<le> 1"
"expr_5 \<chi> \<le> 1"
      using expr_1_pos expr_6_pos
      by simp+
    hence "stacked_pos_conj_J_empty \<chi>"
      using hml_pos.IH hml_pos.prems(3) by auto
    then show ?case 
      using stacked_pos_conj_J_empty.simps by blast
  next
    case (hml_conj x1 x2 x3)
    hence "Sup ((eSuc \<circ> expr_6 \<circ> x3) ` x2) \<le> 0"
      using Sup_union_distrib expr_6_conj
      by (metis SUP_image Sup_empty bot_enat_def image_empty le_zero_eq not_one_le_zero)
    hence "\<forall>x \<in> x3 ` x2. eSuc (expr_6 x) \<le> 0"
      by (metis SUP_image eSuc_Sup empty_iff empty_is_image not_eSuc_ilei0)
    hence "x3 ` x2 = {}"
      by simp
    have "Sup ((expr_5 \<circ> x3) ` x1) \<le> 1"
"Sup ((expr_1 \<circ> x3) ` x1) \<le> 1"
"Sup ((expr_6 \<circ> x3) ` x1) \<le> 0"
      using expr_1_conj expr_5_conj expr_6.expr_6_conj Sup_union_distrib hml_conj
      using \<open>x3 ` x2 = {}\<close> by force+
    hence "\<forall>x \<in> x3 ` x1. expr_1 x \<le> 1"
"\<forall>x \<in> x3 ` x1. expr_5 x \<le> 1"
"\<forall>x \<in> x3 ` x1. expr_6 x \<le> 0"
      using Sup_le_iff 
      by (metis SUP_image imageI)+
    hence "\<forall>x \<in> x3 ` x1. stacked_pos_conj_J_empty x"
      using hml_conj 
      by blast
    then show ?case using \<open>x3 ` x2 = {}\<close> stacked_pos_conj_J_empty.simps 
      by fastforce
  qed
qed

lemma ready_sim_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
  shows "HML_ready_sim \<phi>"
  using assms
proof (induction \<phi>)
  case TT
  then show ?case 
    using HML_ready_sim.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    by (simp add: HML_ready_sim.intros(2)) 
next
  case (hml_conj I J \<Phi>)
  hence "expr_5 (hml_conj I J \<Phi>) \<le> 1"
"expr_6 (hml_conj I J \<Phi>) \<le> 1"
    by (metis expr.simps less_eq_t.simps)+
  hence "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
    using expr_5_conj expr_6.expr_6_conj Sup_union_distrib 
    by (metis le_sup_iff)+
  hence "\<forall>x \<in> \<Phi> ` I. expr_5 x \<le> 1"
"\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 1"
    using Sup_le_iff
    by (metis image_comp image_eqI)+   
  hence "\<forall>x \<in> \<Phi> ` I. less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
    by simp
  hence "\<forall>x \<in> \<Phi> ` I. HML_ready_sim x" using hml_conj
    by blast
  have "Sup((expr_5 \<circ> \<Phi>) ` J) \<le> 1" "Sup((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
    using \<open>expr_5 (hml_conj I J \<Phi>) \<le> 1\<close>
    by (simp add: Sup_union_distrib)+
  hence "\<forall>x \<in> \<Phi> ` J. expr_1 x \<le> 1"
    using Sup_le_iff
    by (metis image_comp image_eqI)
  have "Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) <= 1"
    using \<open>expr_6 (hml_conj I J \<Phi>) \<le> 1\<close>
    by (simp add: Sup_union_distrib)
  hence "Sup((expr_6 \<circ> \<Phi>) ` J) <= 0"
    by (metis (no_types, opaque_lifting) SUP_image Sup_enat_def eSuc_Sup eSuc_ile_mono one_eSuc zero_le)
  hence "\<forall>x \<in> \<Phi> ` J. expr_6 x \<le> 0"
    using Sup_le_iff
    by (metis image_comp image_eqI)
  with \<open>\<forall>x \<in> \<Phi> ` J. expr_1 x \<le> 1\<close> have "\<forall>x \<in> \<Phi> ` J. single_pos_pos x"
    using single_pos_pos_expr by blast
  then show ?case using \<open>\<forall>x \<in> \<Phi> ` I. HML_ready_sim x\<close> hml_ready_sim.intros(3) 
    by (meson Ready_simulation.HML_ready_sim.intros(3))
qed
end