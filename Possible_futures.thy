theory Possible_futures
imports Transition_Systems HML formula_prices_list Impossible_futures
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
inductive hml_possible_futures :: "('a, 's)hml \<Rightarrow> bool"
  where
pf_tt: "hml_possible_futures TT" |
pf_pos: "hml_possible_futures (hml_pos \<alpha> \<phi>)" if "hml_possible_futures \<phi>" |
pf_conj: "hml_possible_futures (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> ` (I\<union> J)). (hml_trace x)"

definition hml_possible_futures_formulas where
"hml_possible_futures_formulas \<equiv> {\<phi>. hml_possible_futures \<phi>}"

definition expr_possible_futures
  where
"expr_possible_futures = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1))}"

context lts
begin

definition expr_possible_futures_equivalent 
  where
"expr_possible_futures_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_possible_futures \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end
lemma possible_futures_right:
  assumes "hml_possible_futures \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  using assms
proof(induction \<phi> rule: hml_possible_futures.induct)
  case pf_tt
  then show ?case
    by simp
next
  case (pf_pos \<phi> \<alpha>)
  then show ?case 
    by simp 
next
  case (pf_conj \<Phi> I J)
  hence fa_le: "\<forall>x\<in>\<Phi> ` I \<union> \<Phi> ` J. less_eq_t (expr x) (\<infinity>, 1, 0, 0, 0, 0)"
    using trace_right
    by blast
  hence "\<forall>x \<in> \<Phi> ` I \<union> \<Phi> ` J. expr_6 x <= 0"
and "\<forall>x \<in> \<Phi> ` I \<union> \<Phi> ` J. expr_2 x \<le> 1"
    using expr.simps less_eq_t.simps
    by auto
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1" and
"Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 1"
    using SUP_image SUP_least
    by (metis UnCI)+
  hence e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using expr_2_conj one_add_one
    by (metis Sup_union_distrib add_mono_thms_linordered_semiring(2) sup.bounded_iff)
  have "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using \<open>\<forall>x \<in> \<Phi> ` I \<union> \<Phi> ` J. expr_6 x <= 0\<close> SUP_image SUP_least
    by (metis Un_iff)+
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def 
    by (metis (no_types, opaque_lifting) SUP_image eSuc_Sup image_empty le_zero_eq nle_le one_eSuc)
  hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> Sup_union_distrib expr_6.expr_6_conj
    by (smt (verit) le_sup_iff le_zero_eq linordered_nonzero_semiring_class.zero_le_one)
  then show ?case using e2
    by auto
qed

lemma possible_futures_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  shows "hml_possible_futures \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case 
    using pf_tt by blast 
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    using pf_pos by simp
next
  case (hml_conj I J \<Phi>)
  hence "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using expr.simps less_eq_t.simps
    by metis
  then show ?case using expr_2_le_2_is_trace
    using pf_conj 
    by (metis image_Un)
qed

lemma possible_futures_lemma:
  shows "hml_possible_futures \<phi> = less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  using possible_futures_right possible_futures_left by blast

end