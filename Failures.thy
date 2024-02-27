theory Failures
imports Transition_Systems HML formula_prices_list HML_list
begin

subsection \<open>Failures semantics\<close>

text \<open>We can imagine the observer not only observing all traces of a system but also identifying scenarios where specific behavior is not possible. 
For Failures in particular, the observer can distinguish between step-sequences based on what actions are possible in the resulting state. 
Another way to think about Failures is that the process autonomously chooses an execution path, but only using a set of free are allowed actions.
We want the failure formulas to represent either a trace (of the form $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\textsf{T}$)
or a failure pair, where some set of actions is not possible (so $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\bigwedge \Phi$ with $$)\<close>

text \<open>\textbf{Definition} The language $\mathcal{O}_F$ of failure-formulas is defined recursively:
$$\langle a \rangle \varphi if \varphi \in \mathcal[O}_F | \bigwedge_{i\inI}\lnot\langle a \rangle \textsf{T}$$\<close>

inductive hml_failure :: "('a, 's)hml \<Rightarrow> bool"
  where
failure_tt: "hml_failure TT" |
failure_pos: "hml_failure (hml_pos \<alpha> \<phi>)" if "hml_failure \<phi>" |
failure_conj: "hml_failure (hml_conj I J \<psi>s)" 
if "I = {}" "(\<forall>j \<in> J. (\<exists>\<alpha>. ((\<psi>s j) = hml_pos \<alpha> TT)) \<or> \<psi>s j = TT)" 

definition hml_failure_formulas
  where
"hml_failure_formulas \<equiv> {\<phi>. hml_failure \<phi>}"

definition expr_failure
  where
"expr_failure = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))}"
       
context lts
begin

definition hml_failure_equivalent
  where
"hml_failure_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> hml_failure_formulas \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

definition expr_failure_equivalent 
  where
"expr_failure_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_failure \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

lemma expr_TT:
  assumes "TT_like \<chi>"
  shows "expr \<chi> = (0, 1, 0, 0, 0, 0)"
using assms
proof (induction \<chi>)
  case 1
  then show ?case by simp
next
  case (2 \<Phi> I J)
  then show ?case using expr.simps Sup_enat_def by force+
qed

lemma assumes "TT_like \<chi>"
shows e1_tt: "expr_1 (hml_pos \<alpha> \<chi>) = 1"
and e2_tt: "expr_2 (hml_pos \<alpha> \<chi>) = 1"
and e3_tt: "expr_3 (hml_pos \<alpha> \<chi>) = 0"
and e4_tt: "expr_4 (hml_pos \<alpha> \<chi>) = 0"
and e5_tt: "expr_5 (hml_pos \<alpha> \<chi>) = 0"
and e6_tt: "expr_6 (hml_pos \<alpha> \<chi>) = 0"
  using expr_TT assms
  by auto

lemma mon_expr_1_pos_r: 
  "Sup (expr_1 ` (pos_r xs)) \<le> Sup (expr_1 ` xs)"
  by (simp add: Sup_subset_mono image_mono)

lemma failure_right:
  assumes "HML_failure \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using assms
proof(induction \<phi> rule:HML_failure.induct)
  case failure_tt
  then show ?case by force
next
  case (failure_pos \<phi> \<alpha>)
  then show ?case by force
next
  case (failure_conj I \<Phi> J)
  have expr_\<psi>s: "\<forall>\<phi>. \<phi> \<in> \<Phi> ` I \<longrightarrow> expr \<phi> = (0, 1, 0, 0, 0, 0)"
    using expr_TT HML_failure.simps local.failure_conj 
    by blast
  hence e1_pos: "\<forall>e \<in> (expr_1 \<circ> \<Phi>) ` I. e = 0"
and e2_pos: "\<forall>e \<in> (expr_2 \<circ> \<Phi>) ` I. e = 1"
and e3_pos: "\<forall>e \<in> (expr_3 \<circ> \<Phi>) ` I. e = 0"
and e4_pos: "\<forall>e \<in> (expr_4 \<circ> \<Phi>) ` I. e = 0"
and e5_pos: "\<forall>e \<in> (expr_5 \<circ> \<Phi>) ` I. e = 0"
and e6_pos: "\<forall>e \<in> (expr_6 \<circ> \<Phi>) ` I. e = 0"
    by simp+

  hence e1_2: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
and e2_2: "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1"
and e3_2: "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
and e4_2: "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and e5_2: "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
and e6_2: "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_enat_def dual_order.refl local.failure_conj 
    by (metis Sup_le_iff)+

  from failure_conj have e1_neg: "\<forall>j \<in> J. expr_1 (\<Phi> j) \<le> 1"
and e2_neg: "\<forall>j \<in> J. expr_2 (\<Phi> j) = 1"
and e3_neg: "\<forall>j \<in> J. expr_3 (\<Phi> j) = 0"
and e4_neg: "\<forall>j \<in> J. expr_4 (\<Phi> j) = 0"
and e5_neg: "\<forall>j \<in> J. expr_5 (\<Phi> j) = 0"
and e6_neg: "\<forall>j \<in> J. expr_6 (\<Phi> j) = 0"
    using e1_tt e5_tt e2_tt e3_tt e4_tt e6_tt
    by fastforce+
  hence "(Sup ((expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
    using Sup_enat_def
    by (smt (verit, del_insts) Sup_le_iff Un_iff comp_apply image_iff nle_le not_one_le_zero)
  hence e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1"
    using expr_5_conj expr_\<psi>s e5_2 
    by (simp add: Sup_union_distrib)
  from e2_2 e2_neg failure_conj have "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff Sup_union_distrib)
  hence e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2" 
    using expr_2_conj one_add_one
    by (metis add_left_mono)
  from e1_2 e3_2 have "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J) \<le> 0"
    by (metis (no_types, lifting) SUP_bot_conv(2) Sup_union_distrib bot_enat_def comp_apply e3_neg le_zero_eq sup.orderE)
  hence e3: "expr_3 (hml_conj I J \<Phi>) \<le> 0" 
    using expr_3_conj
    by auto
  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    by (metis SUP_image e1_2 le_zero_eq mon_expr_1_pos_r)
  hence "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 0"
    using e4_2 failure_conj Sup_union_distrib bot_enat_def comp_apply e4_neg
    by (metis (no_types, lifting) SUP_bot_conv(2) le_zero_eq max_def sup_max) 
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0" 
    using expr_4_conj
    by auto
  from failure_conj e6_2 e6_neg have "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    by (metis (mono_tags, lifting) SUP_least comp_apply le_zero_eq)
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def comp_apply
    by (metis eSuc_Sup image_comp image_empty le_zero_eq nle_le one_eSuc) 
  with failure_conj e6_2 e6_tt have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    using one_eSuc e6_neg image_cong le_sup_iff bot.extremum_uniqueI bot_enat_def comp_apply
    by (simp add: Sup_union_distrib)
  hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using expr_6_conj
    by auto
  from e2 e3 e4 e5 e6 show ?case
    using less_eq_t.simps expr.simps 
    by fastforce
qed

lemma "hml_failure_equivalent p q \<longleftrightarrow> expr_failure_equivalent p q"  oops







text \<open>Failure Pairs\<close>

abbreviation failure_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a set) set\<close>
  where
\<open>failure_pairs p \<equiv> {(xs, F)|xs F. \<exists>p'. p \<mapsto>$ xs p' \<and> (initial_actions p' \<inter> F = {})}\<close>

text \<open>Failure preorder and -equivalence\<close>

definition failure_preordered (infix \<open>\<lesssim>F\<close> 60) where
\<open>p \<lesssim>F q \<equiv> failure_pairs p \<subseteq> failure_pairs q\<close>

abbreviation failure_equivalent (infix \<open>\<simeq>F\<close> 60) where
\<open> p \<simeq>F q \<equiv> p \<lesssim>F q \<and> q \<lesssim>F p\<close>
end
end