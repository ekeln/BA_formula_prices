theory Ready_traces
imports Transition_Systems HML formula_prices_list Failure_traces Readiness
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
inductive hml_ready_trace :: "('a, 's)hml \<Rightarrow> bool" where
r_trace_tt: "hml_ready_trace TT" |
r_trace_pos: "hml_ready_trace (hml_pos \<alpha> \<phi>)" if "hml_ready_trace \<phi>" |
r_trace_conj: "hml_ready_trace (hml_conj I J \<Phi>)" 
  if "((\<forall>i \<in> \<Phi> ` I. \<exists>\<alpha>. i = hml_pos \<alpha> TT) \<or> (\<exists>i \<in> \<Phi> ` I. hml_ready_trace i \<and> (\<forall>j \<in> \<Phi> ` I. i \<noteq> j \<longrightarrow> (\<exists>\<alpha>. j = hml_pos \<alpha> TT))))"
     "\<forall>j \<in> \<Phi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT) \<or> j = TT" 

definition hml_ready_trace_formulas
  where
"hml_ready_trace_formulas \<equiv> {\<phi>. hml_ready_trace \<phi>}"

inductive single_pos_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"single_pos_pos TT" |
"single_pos_pos (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"single_pos_pos (hml_conj I J \<Phi>)" if 
"(\<forall>\<phi> \<in> (\<Phi> `I). (single_pos_pos \<phi>))"
"(\<Phi> ` J) = {}"

inductive single_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"single_pos TT" |
"single_pos (hml_pos _ \<psi>)" if "nested_empty_conj \<psi>" |
"single_pos (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). (single_pos \<phi>)"
"\<forall>\<phi> \<in> (\<Phi> ` J). single_pos_pos \<phi>"


inductive HML_ready_trace :: "('a, 's)hml \<Rightarrow> bool"
  where
r_trace_tt: "HML_ready_trace TT" |
r_trace_pos: "HML_ready_trace (hml_pos \<alpha> \<phi>)" if "HML_ready_trace \<phi>"|
r_trace_conj: "HML_ready_trace (hml_conj I J \<Phi>)" 
if "(\<exists>x \<in> (\<Phi> ` I). HML_ready_trace x \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> single_pos y))
\<or> (\<forall>y \<in> (\<Phi> ` I).single_pos y)"
"(\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"


definition expr_readiness
  where
"expr_readiness = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))}"

context lts
begin

definition expr_readiness_equivalent 
  where
"expr_readiness_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_readiness \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

end

inductive stacked_pos_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where 
"stacked_pos_conj TT" |
"stacked_pos_conj (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"stacked_pos_conj (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). ((stacked_pos_conj \<phi>) \<or> nested_empty_conj \<phi>)"
"(\<forall>\<psi> \<in> (\<Phi> ` J). nested_empty_conj \<psi>)"

inductive stacked_pos_conj_J_empty :: "('a, 'i) hml \<Rightarrow> bool"
  where
"stacked_pos_conj_J_empty TT" |
"stacked_pos_conj_J_empty (hml_pos _ \<psi>)" if "stacked_pos_conj_J_empty \<psi>" |
"stacked_pos_conj_J_empty (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). (stacked_pos_conj_J_empty \<phi>)" "\<Phi> ` J = {}"


lemma expr_stacked_pos_conj:
  assumes "stacked_pos_conj \<phi>"
  shows "less_eq_t (expr \<phi>) (1, \<infinity>, 1, 1, 1, 2)"
  using assms
proof(induction \<phi> rule: stacked_pos_conj.induct)
  case 1
  then show ?case using expr_TT 
    by simp
next
  case (2 \<psi> \<alpha>)
  have "less_eq_t (expr \<psi>) (0, \<infinity>, 0, 0, 0, 0)"
    using expr_nested_empty_pos_conj 2
    by blast
  then show ?case using 2 
    by simp 
next
  case (3 \<Phi> I J)
  from expr_nested_empty_conj have fa: "\<forall>x \<in> \<Phi> ` J. less_eq_t (expr x) (0, \<infinity>, 0, 0, 0, 1)"
    using "3.hyps" by blast
  hence sup_j: "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
"Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 1"
        apply (simp add: Sup_le_iff SUP_image)
    using SUP_least SUP_image
    by (metis \<open>\<forall>x\<in>\<Phi> ` J. less_eq_t (expr x) (0, \<infinity>, 0, 0, 0, 1)\<close> expr.simps less_eq_t.simps)+
  hence sup_esuc: "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 2"
    using one_add_one eSuc_def
    by (metis (no_types, lifting) SUP_image eSuc_Sup eSuc_ile_mono i0_lb ile0_eq image_is_empty plus_1_eSuc(1))
  from 3 expr_nested_empty_conj have fa: " \<forall>\<phi>\<in>\<Phi> ` I. less_eq_t (expr \<phi>) (1, \<infinity>, 1, 1, 1, 2)"
    using order_trans by fastforce
  hence sup_i: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 2"
using SUP_least SUP_image
  by (metis expr.simps less_eq_t.simps)+

  hence "expr_1 (hml_conj I J \<Phi>) \<le> 1" "expr_3 (hml_conj I J \<Phi>) \<le> 1" "expr_3 (hml_conj I J \<Phi>) \<le> 1"
"expr_4 (hml_conj I J \<Phi>) \<le> 1" "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 2"
    using sup_j Sup_union_distrib
     apply (metis Sup_union_distrib expr_1_conj le_sup_iff)
    using sup_j sup_i
     apply (simp add: Sup_union_distrib)
    using sup_i sup_j Sup_union_distrib expr_3_conj le_zero_eq max_def sup_enat_def
       apply (smt (verit, ccfv_threshold) )
    using sup_i sup_j Sup_union_distrib
    apply (smt (verit, del_insts) SUP_image expr_4_conj le_sup_iff linordered_nonzero_semiring_class.zero_le_one mon_expr_1_pos_r order_trans)
     using sup_i sup_j Sup_union_distrib expr_5_conj
      apply (smt (verit, del_insts) bot.extremum_uniqueI bot_enat_def max_def sup_max)
     using sup_i sup_j Sup_union_distrib sup_esuc
     by (metis expr_6.expr_6_conj le_supI)
    then show ?case 
      by simp
qed

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

lemma expr_single_pos:
  assumes "single_pos \<phi>"
  shows "less_eq_t (expr \<phi>) (1, \<infinity> , 1, 1, 1, 1)"
  using assms
proof(induction \<phi>)
  case 1
  then show ?case by simp
next
  case (2 \<psi> \<alpha>)
  with expr_nested_empty_conj have "less_eq_t (expr \<psi>) (0, \<infinity>, 0, 0, 0, 1)"
    by blast
  then show ?case by simp
next
  case (3 \<Phi> I J)
  hence fa_neg: "\<forall>\<phi>\<in>\<Phi> ` J. less_eq_t (expr \<phi>) (1, \<infinity>, 1, 1, 0, 0)"
    using expr_single_pos_pos
    by blast
  hence fa_neg: "\<forall>\<phi>\<in>\<Phi> ` J. expr_1 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` J. expr_3 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` J. expr_4 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` J. expr_5 \<phi> \<le> 0"
"\<forall>\<phi>\<in>\<Phi> ` J. expr_6 \<phi> \<le> 0"
    using less_eq_t.simps expr.simps
    by simp+
  have fa_pos: "\<forall>\<phi>\<in>\<Phi> ` I. less_eq_t (expr \<phi>) (1, \<infinity>, 1, 1, 1, 1)"
    using 3 by blast
  hence fa_pos: "\<forall>\<phi>\<in>\<Phi> ` I. expr_1 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` I. expr_3 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` I. expr_4 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` I. expr_5 \<phi> \<le> 1"
"\<forall>\<phi>\<in>\<Phi> ` I. expr_6 \<phi> \<le> 1"
    using less_eq_t.simps expr.simps
    by simp+
  hence "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1"
"(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J)) \<le> 1"
"Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 1"
"(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
"(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
        prefer 5
    using Sup_le_iff fa_neg
    using one_eSuc apply fastforce
    using Sup_le_iff fa_neg fa_pos
    by fastforce+
  then show ?case 
    by (simp add: Pair_inject)
qed

lemma single_pos_pos_expr:
  assumes "expr_1 \<phi> \<le> 1" "expr_6 \<phi> \<le> 0"
  shows "single_pos_pos \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case 
    by (simp add: single_pos_pos.intros(1))
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    using expr_1_expr_6_le_0_is_nested_empty_pos_conj single_pos_pos.intros(2) by fastforce
next
  case (hml_conj I J \<Phi>)
  hence "\<forall>x \<in> \<Phi> ` I. expr_1 x \<le> 1"
    by (simp add: Sup_le_iff)
  from hml_conj have "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 0"
    using Sup_le_iff bot.extremum_uniqueI bot_enat_def expr_6.expr_6_conj image_comp image_empty image_eqI not_one_le_zero sup_bot_right
    by (smt (verit, del_insts) Sup_union_distrib le_sup_iff)
  hence "\<forall>x \<in> \<Phi> ` I. single_pos_pos x"
    using \<open>\<forall>x \<in> \<Phi> ` I. expr_1 x \<le> 1\<close> hml_conj
    by blast
  from hml_conj have "\<Phi> ` J = {}"
    using not_one_le_zero order_trans
    by (metis Failure_traces.expr_6_conj)
  then show ?case using \<open>\<forall>x \<in> \<Phi> ` I. single_pos_pos x\<close> single_pos_pos.intros(3) by blast
qed

lemma single_pos_expr:
assumes "expr_5 \<phi> \<le> 1" "expr_6 \<phi> \<le> 1"
"expr_1 \<phi> \<le> 1"
shows "single_pos \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case 
    by (simp add: single_pos.intros(1))
next
  case (hml_pos x1 \<phi>)
  hence "expr_1 \<phi> \<le> 0"
"expr_5 \<phi> \<le> 1"
"expr_6 \<phi> \<le> 1"
    by simp+
  hence "nested_empty_conj \<phi>"
    using expr_1_0_expr_6_1_nested_empty_conj by blast
  then show ?case 
    using single_pos.intros(2) 
    by fastforce
next
  case (hml_conj I J \<Phi>)
  hence "\<forall>x \<in> (\<Phi> ` (I \<union> J)). expr_1 x \<le> 1"
    using expr_1_conj Sup_union_distrib
    by (metis (no_types, lifting) SUP_image SUP_lessD SUP_union dual_order.order_iff_strict linorder_not_le)
  from hml_conj have "\<forall>x \<in> (\<Phi> ` (I \<union> J)). expr_5 x \<le> 1"
    using expr_5_conj Sup_union_distrib 
    by (smt (verit, ccfv_threshold) SUP_image Sup_le_iff UnCI image_Un image_eqI)
  from hml_conj have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    by simp
  hence "\<forall>x \<in> (\<Phi> ` I). expr_6 x \<le> 1"
"\<forall>x \<in> (\<Phi> ` J). expr_6 x \<le> 0"
    prefer 2 using eSuc_def eSuc_ile_mono one_eSuc
    by (metis (no_types, opaque_lifting) 
SUP_image Sup_le_iff Sup_union_distrib image_iff sup.bounded_iff)+
  hence "\<forall>x \<in> (\<Phi> ` I). single_pos x"
    using \<open>\<forall>x \<in> (\<Phi> ` (I \<union> J)). expr_5 x \<le> 1\<close> \<open>\<forall>x \<in> (\<Phi> ` (I \<union> J)). expr_1 x \<le> 1\<close> hml_conj(1)
    by fastforce
  from \<open>\<forall>x \<in> (\<Phi> ` J). expr_6 x \<le> 0\<close> \<open>\<forall>x \<in> (\<Phi> ` (I \<union> J)). expr_1 x \<le> 1\<close>
  have "\<forall>x \<in> (\<Phi> ` J). single_pos_pos x"
    using single_pos_pos_expr
    by blast
  then show ?case using single_pos.intros(3) \<open>\<forall>x \<in> (\<Phi> ` I). single_pos x\<close>
    by blast
qed

lemma stacked_pos_conj_right:
  assumes "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 1"
"expr_4 (hml_conj I J \<Phi>) \<le> 1" "\<forall>\<phi> \<in> (\<Phi> ` I). HML_ready_trace \<phi>"
shows "(\<exists>x \<in> (\<Phi> ` I). HML_ready_trace x \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> single_pos y))
\<or> (\<forall>y \<in> (\<Phi> ` I).single_pos y)"
proof(cases "\<exists>\<psi> \<in> (\<Phi> ` I). expr_1 \<psi> \<ge> 2")
  case True
  then obtain \<psi> where "\<psi> \<in> (\<Phi> ` I)" "expr_1 \<psi> \<ge> 2"
    by blast
  have "\<forall>\<chi> \<in> \<Phi> ` I. \<chi> \<noteq> \<psi> \<longrightarrow> expr_1 \<chi> \<le> 1"
  proof(rule ccontr)
    assume assm: "\<not> (\<forall>\<chi>\<in>\<Phi> ` I. \<chi> \<noteq> \<psi> \<longrightarrow> expr_1 \<chi> \<le> 1)"
    then obtain \<chi> where "\<chi> \<noteq> \<psi>" "expr_1 \<chi> \<ge> 2"
      by (metis ileI1 linorder_not_le one_add_one plus_1_eSuc(1))
    then have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) >= 2"
      using \<open>expr_1 \<psi> \<ge> 2\<close> \<open>\<psi> \<in> (\<Phi> ` I)\<close> assm pos_r.simps one_add_one plus_1_eSuc(1)
      by (metis (no_types, lifting) Diff_iff SUP_upper2 empty_iff ileI1 insertE not_le_imp_less)
    hence "expr_4 (hml_conj I J \<Phi>) \<ge> 2"
      using expr_4_conj 
      by (metis (no_types, lifting) Sup_union_distrib le_sup_iff nle_le sup.orderE)
    then show False using assms(3)
      by (meson numeral_le_one_iff order_trans semiring_norm(69))
  qed
  have expr_x: "expr_5 \<psi> \<le> 1" "expr_6 \<psi> \<le> 1" "expr_4 \<psi> \<le> 1"
    using expr_5_conj expr_6_conj expr_4_conj \<open>\<psi> \<in> (\<Phi> ` I)\<close> assms
      apply (smt (verit, del_insts) Sup_le_iff UnCI comp_apply image_iff)
    using assms expr_6_conj  \<open>\<psi> \<in> \<Phi> ` I\<close>
     apply (smt (verit) SUP_image SUP_upper2 Sup_union_distrib expr_6.expr_6_conj le_supE nle_le)
    using assms expr_4_conj  \<open>\<psi> \<in> \<Phi> ` I\<close>
    by (smt (verit, del_insts) Sup_le_iff UnCI comp_apply image_iff)
  from assms have expr_4_5_6: "\<forall>\<psi> \<in> \<Phi> ` I. expr_4 \<psi> \<le> 1 \<and> expr_5 \<psi> \<le> 1 \<and> expr_6 \<psi> \<le> 1"
    using expr_4_conj expr_5_conj expr_6_conj Sup_union_distrib 
    by (smt (verit, del_insts) Sup_le_iff comp_apply expr_6.expr_6_conj image_iff le_sup_iff)
  have single_pos_\<chi>: "\<forall>\<chi> \<in> \<Phi> ` I. \<chi> \<noteq> \<psi> \<longrightarrow> single_pos \<chi>" 
    using expr_4_5_6 single_pos_expr \<open>\<forall>\<chi> \<in> \<Phi> ` I. \<chi> \<noteq> \<psi> \<longrightarrow> expr_1 \<chi> \<le> 1\<close>
    by blast
  from assms(4) have "HML_ready_trace \<psi>" using \<open>\<psi> \<in> (\<Phi> ` I)\<close>
    by blast
  then show ?thesis using single_pos_\<chi> 
    by metis
next
  case False
  hence "\<forall>\<phi> \<in> \<Phi> ` I. expr_1 \<phi> \<le> 1"
    by (metis ileI1 not_le_imp_less one_add_one plus_1_eSuc(1))
  from assms have "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J)) \<le> 1"
    using expr_5_conj Sup_union_distrib 
    by (metis le_supE)
  hence "Sup ((expr_5 \<circ> \<Phi>) ` (I \<union> J)) \<le> 1"
    by (simp add: image_Un)
  hence "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_5 x <= 1"
    by (simp add: Sup_le_iff)
  from assms have "(Sup ((expr_6 \<circ> \<Phi>) ` I)) \<le> 1"
    using expr_6.expr_6_conj Sup_union_distrib
    by (metis le_supE)
  hence "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 1"
    by (simp add: Sup_le_iff)
  hence "\<forall>\<psi> \<in> \<Phi> ` I. single_pos \<psi>" 
    using single_pos_expr \<open>\<forall>x \<in> \<Phi> ` (I \<union> J). expr_5 x <= 1\<close> \<open>\<forall>\<phi> \<in> \<Phi> ` I. expr_1 \<phi> \<le> 1\<close>
    by blast
  then show ?thesis by blast
qed

lemma stacked_pos_conj_left:
  assumes "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 1"
"expr_4 (hml_conj I J \<Phi>) \<le> 1"
shows "(\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"
proof
  fix y
  have sup_neg: "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
"Sup ((expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1"
"Sup((expr_4 \<circ> \<Phi>) ` J) \<le> 1"
    using assms Sup_union_distrib expr_6.expr_6_conj le_sup_iff expr_4_conj expr_5_conj
    by metis+
  hence "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using SUP_image Sup_enat_def eSuc_Sup
    by (metis eSuc_ile_mono le_zero_eq one_eSuc)
  assume "y \<in> \<Phi> ` J"
  have expr_y: "expr_6 y \<le> 0" "expr_1 y \<le> 1" "expr_4 y \<le> 1"
    using sup_neg \<open>y \<in> \<Phi> ` J\<close> \<open>Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0\<close>
      apply (metis SUP_image SUP_upper dual_order.trans)
    using sup_neg \<open>y \<in> \<Phi> ` J\<close> Sup_le_iff comp_apply image_iff image_subset_iff
    by (metis Un_upper2)+
  show "single_pos_pos y"
    using expr_y
  proof(induction y)
    case TT
    then show ?case 
      using single_pos_pos.intros(1) by blast
  next
    case (hml_pos x1 y)
    hence expr_y: "expr_6 y \<le> 0" "expr_1 y \<le> 0" "expr_4 y \<le> 1"
      by simp+
    hence "nested_empty_pos_conj y"
      using expr_1_expr_6_le_0_is_nested_empty_pos_conj
      by blast 
    then show ?case using single_pos_pos.intros(2) 
      by fastforce
  next
    case (hml_conj x1 x2 x3)
have "(Sup ((expr_1 \<circ> x3) ` x1) \<le> 1)"
"(Sup ((expr_6 \<circ> x3) ` x1) \<le> 0)"
"(Sup ((expr_4 \<circ> x3) ` x1) \<le> 1)"
      using hml_conj Sup_union_distrib expr_1_conj expr_6.expr_6_conj expr_4_conj
      by (metis le_supE)+
    hence "\<forall>x \<in> (x3 ` x1). expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x \<le> 1"
      by (metis SUP_image SUP_upper dual_order.trans)
    hence "\<forall>x \<in> (x3 ` x1). single_pos_pos x"
      using hml_conj
      by blast
    then show ?case using single_pos_pos.intros(3) 
      by (metis Failure_traces.expr_6_conj hml_conj.prems(1) le_zero_eq not_one_le_zero)
  qed
qed

lemma ready_trace_right:
  assumes "HML_ready_trace \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1)"
  using assms
proof(induction \<phi> rule: HML_ready_trace.induct)
  case r_trace_tt
  hence "expr_4 TT = 0" "expr_5 TT = 0" "expr_6 TT = 0"
    using expr_4_tt expr_5_tt expr_6_tt by blast+
  then show ?case by simp
next
  case (r_trace_pos \<phi> \<alpha>)
  hence "expr_4 (hml_pos \<alpha> \<phi>) \<le> 1" "expr_5 (hml_pos \<alpha> \<phi>) \<le> 1" "expr_6 (hml_pos \<alpha> \<phi>) \<le> 1"
    by simp+
  then show ?case by simp
next
  case (r_trace_conj \<Phi> I J)
  hence fa_neg: "\<forall>y\<in>\<Phi> ` J. less_eq_t (expr y) (1, \<infinity>, 1, 1, 0, 0)"
    using expr_single_pos_pos HML_list.single_pos_pos.intros(1) HML_list.single_pos_pos.intros(2)
    by (metis mon_pos)
  hence fa_neg: "\<forall>x\<in>\<Phi> ` J. expr_1 x \<le> 1"
"\<forall>x\<in>\<Phi> ` J. expr_3 x \<le> 1"
"\<forall>x\<in>\<Phi> ` J. expr_4 x \<le> 1"
"\<forall>x\<in>\<Phi> ` J. expr_5 x \<le> 0"
"\<forall>x\<in>\<Phi> ` J. expr_6 x \<le> 0"
    using expr.simps less_eq_t.simps
    by force+
  show ?case
    using r_trace_conj(1)
  proof(rule disjE)
    assume "\<forall>y\<in>\<Phi> ` I. single_pos y"
    hence fa_pos: "\<forall>y\<in>\<Phi> ` I. less_eq_t (expr y) (1, \<infinity>, 1, 1, 1, 1)"
      using expr_single_pos 
      by blast
    hence fa_pos: "\<forall>y\<in>\<Phi> ` I. expr_1 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_3 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_4 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_5 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_6 y \<le> 1"
      using expr.simps less_eq_t.simps
      by force+
    with fa_neg have e1: "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1"
and e5: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
      using expr.simps less_eq_t.simps Sup_le_iff
      by (simp add: SUP_least Sup_union_distrib)+
    have e3: "(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J)) \<le> 1"
      using fa_neg fa_pos expr.simps less_eq_t.simps Sup_le_iff
      by (simp add: SUP_least Sup_union_distrib le_sup_iff)
    from fa_pos have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 1"
      by (metis SUP_image Sup_union_distrib \<open>Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> dual_order.trans mon_expr_1_pos_r sup.coboundedI1)
    hence e4: "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 1"
      using fa_pos fa_neg expr.simps less_eq_t.simps Sup_le_iff SUP_least Sup_union_distrib le_sup_iff
      by (metis (no_types, opaque_lifting) image_comp)
    have e6: "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) <= 1"
      using fa_pos fa_neg expr.simps less_eq_t.simps Sup_le_iff SUP_least Sup_union_distrib le_sup_iff
      using one_eSuc by fastforce
    then show ?thesis using e1 e3 e4 e5
      by (metis enat_ord_code(3) expr.simps expr_4_conj expr_5_conj expr_6.expr_6_conj less_eq_t.simps)
  next
    assume "\<exists>x\<in>\<Phi> ` I.
       (HML_ready_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1)) \<and>
       (\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> single_pos y)"
    then obtain x where "x\<in>\<Phi> ` I" and x_prop: "(HML_ready_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1)) \<and>
       (\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> single_pos y)" by blast
    hence fa_pos: "\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> less_eq_t (expr y) (1, \<infinity>, 1, 1, 1, 1)"
      using expr_single_pos 
      by blast
    hence fa_pos: "\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_1 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_3 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_4 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_5 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_6 y \<le> 1"
      using expr.simps less_eq_t.simps
      by force+ 
    with x_prop have fa_pos: "\<forall>y\<in>\<Phi> ` I. expr_4 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_5 y \<le> 1"
"\<forall>y\<in>\<Phi> ` I. expr_6 y \<le> 1"
      by auto
    have sup_pos_r: "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 1"
    proof(cases "expr_1 x \<ge> 2")
      case True
      hence "\<forall>y \<in> (\<Phi> ` I) - {x}. expr_1 y < expr_1 x"
        using \<open>\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_1 y \<le> 1\<close>
        by (metis DiffD1 DiffD2 dual_order.trans not_le_imp_less numeral_le_one_iff semiring_norm(69) singletonI)
      hence "(pos_r (\<Phi> ` I)) = (\<Phi> ` I) - {x}"
        using pos_r_del_max
        by (metis Un_commute \<open>x \<in> \<Phi> ` I\<close> insert_Diff insert_is_Un)
      then show ?thesis 
        using \<open>\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_1 y \<le> 1\<close> 
        by (metis DiffD1 Diff_insert_absorb SUP_least mk_disjoint_insert)
    next
      case False
      hence "\<forall>x \<in> \<Phi> ` I. expr_1 x \<le> 1"
        using \<open>\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> expr_1 y \<le> 1\<close> 
        using eSuc_plus_1 ileI1 linorder_not_le by fastforce
      then show ?thesis 
        by (metis \<open>x \<in> \<Phi> ` I\<close> image_iff pos_r_bounded)
    qed
    from fa_neg fa_pos have e4: "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 1" "Sup((expr_4 \<circ> \<Phi>) ` J) \<le> 1"
      using Sup_le_iff
      by fastforce+
    hence e4: "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 1"
      using sup_pos_r Sup_union_distrib
      by (metis le_sup_iff)
    from fa_neg fa_pos have e5: "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1" "Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 1" "Sup((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
      using fa_neg fa_pos 
      by (simp add: SUP_le_iff)+
    hence e5: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
      using Sup_union_distrib
      by (metis le_sup_iff)
    from fa_pos fa_neg have e6: "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1" "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
      using Sup_le_iff 
       apply fastforce
      using fa_pos fa_neg 
      by (simp add: Sup_le_iff one_eSuc)
    hence "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
      using Sup_union_distrib
      by (metis le_sup_iff)
    then show ?thesis using e4 e5 expr_5_conj
      by simp
  qed
qed

lemma ready_trace_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1)" 
  shows "HML_ready_trace \<phi>"
  using assms
proof (induction \<phi>)
  case TT
  then show ?case 
    using r_trace_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case
    using r_trace_pos by simp
next
  case (hml_conj I J \<Phi>)
  hence "(\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"
    using stacked_pos_conj_left less_eq_t.simps expr.simps
    by metis
  from hml_conj have "\<forall>\<phi> \<in> (\<Phi> ` I). HML_ready_trace \<phi>"
    by (metis (mono_tags, lifting) image_iff mon_conj(1) rangeI)
  hence "(\<exists>x \<in> (\<Phi> ` I). HML_ready_trace x \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> single_pos y))
\<or> (\<forall>y \<in> (\<Phi> ` I).single_pos y)"
    using stacked_pos_conj_right hml_conj less_eq_t.simps expr.simps
    by metis
  thus ?case using \<open>(\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)\<close> HML_ready_trace.intros(3)
    by metis
qed
end