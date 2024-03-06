theory Simulation
imports Transition_Systems HML formula_prices_list Traces
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
inductive hml_simulation :: "('a, 's)hml \<Rightarrow> bool"
  where
sim_tt: "hml_simulation TT" |
sim_pos: "hml_simulation (hml_pos \<alpha> \<phi>)" if "hml_simulation \<phi>"|
sim_conj: "hml_simulation (hml_conj I J \<psi>s) " 
if "(\<forall>x \<in> (\<psi>s ` I). hml_simulation x) \<and> (\<psi>s ` J = {})"

definition hml_simulation_formulas where
"hml_simulation_formulas \<equiv> {\<phi>. hml_simulation \<phi>}"

definition expr_simulation
  where
"expr_simulation = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))}"

context lts
begin

definition expr_simulation_equivalent
  where
"expr_simulation_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_simulation \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

lemma simulation_right:
  assumes "hml_simulation \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using assms
proof(induction \<phi> rule:hml_simulation.induct)
  case sim_tt
  then show ?case by simp 
next
  case (sim_pos \<phi> \<alpha>)
  then show ?case 
    using trace_right by force
next
  case (sim_conj \<Phi> I J)
  have e5_eq: "expr_5 (hml_conj I J \<Phi>) = (Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J))"
    using expr_5.simps
    by force
  from sim_conj have "\<forall>x\<in>\<Phi> ` I. expr_5 x \<le> 0"
    using expr.simps 
    by force
  hence "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff comp_apply image_iff
    by (smt (verit, ccfv_SIG))
  hence e5: "expr_5 (hml_conj I J \<Phi>) \<le> 0" 
    using e5_eq local.sim_conj by force

  have e6_eq: "expr_6 (hml_conj I J \<Phi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J)))"
    using expr_6.simps
    by force
  from sim_conj have "\<forall>x\<in>\<Phi> ` I. expr_6 x \<le> 0"
    using expr.simps 
    by force
    hence "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff comp_apply image_iff
    by (smt (verit, ccfv_SIG))
  hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 0" 
    using e6_eq local.sim_conj
    by force
  then show ?case 
    using less_eq_t.simps expr.simps e5 e6 
    by simp 
qed


lemma Max_eq_expr_6:
  fixes x1 x2
  defines DA: "A \<equiv> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
  defines DB: "B \<equiv> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})}"
  shows "Max A = Max B"
proof- 
  have fin_A: "finite A" using DA by simp

  have fin_B: "finite B" using DB by simp
  have left: "Max A \<ge> Max B" using Max.coboundedI DA DB by simp
  have right: "Max A \<le> Max B" using Max.coboundedI DA DB assms(2) Max_ge Max_in fin_A fin_B
    by (smt (z3) Max.union Un_infinite Un_insert_left inf_sup_aci(5) insert_iff max_def sup_bot.right_neutral)
  with left show ?thesis by simp
qed

lemma x2_empty:
  assumes "(less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" 
  shows "(\<Phi> ` J) = {}"
proof(rule ccontr)
  assume "\<Phi> ` J \<noteq> {}"
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<ge> 1"
    using Sup_enat_def eSuc_def
    by (metis SUP_image eSuc_Sup iless_eSuc0 image_is_empty linorder_not_le one_eSuc zero_ne_eSuc)
  hence "expr_6 (hml_conj I J \<Phi>) \<ge> 1"
    using expr_6.simps
    by (simp add: Sup_union_distrib sup.coboundedI2)
  thus False using assms by simp
qed

lemma simulation_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  shows "(hml_simulation \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case 
    using sim_tt by blast 
next
  case (hml_pos x1 \<phi>)
  then show ?case using sim_pos by simp 
next
  case (hml_conj I J \<Phi>)
  have "\<forall>x \<in> (\<Phi> ` I). less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
"\<forall>x \<in> (\<Phi> ` J). less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
    using hml_conj mon_conj
    by metis+
  hence "\<forall>x \<in> (\<Phi> ` I). hml_simulation x"
"\<forall>x \<in> (\<Phi> ` J).hml_simulation x"
    using hml_conj
    by (metis image_iff range_eqI)+
  have "\<Phi> ` J = {}" using x2_empty
    using hml_conj.prems by blast
  with \<open>\<forall>x \<in> (\<Phi> ` I). hml_simulation x\<close> show ?case using sim_conj by blast
qed

end