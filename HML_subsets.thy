theory HML_subsets
  imports 
    "HOL-Library.Extended_Nat"
    Main
    HML_list
  formula_prices_list
begin

section \<open>definition of component wise comparison\<close>

fun less_eq_t :: "(enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> bool"
  where
"less_eq_t (n1, n2, n3, n4, n5, n6) (i1, i2, i3, i4, i5, i6) =
    (n1 \<le> i1 \<and> n2 \<le> i2 \<and> n3 \<le> i3 \<and> n4 \<le> i4 \<and> n5 \<le> i5 \<and> n6 \<le> i6)"

definition less where
"less x y \<equiv> less_eq_t x y \<and> \<not> (less_eq_t y x)"

definition e_sup :: "(enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) set \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat)"
  where
"e_sup S \<equiv> ((Sup (fst ` S)), (Sup ((fst \<circ> snd) ` S)), (Sup ((fst \<circ> snd \<circ> snd) ` S)), 
(Sup ((fst \<circ> snd \<circ> snd \<circ> snd) ` S)), (Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` S)), 
(Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` S)))"


section \<open>general auxillary lemmas to argue about formulas and prices\<close>
subsection \<open>The price of formulas is monotonic with respect to subformulas. 
I.e.: If (expr \<phi>) <= (expr \<langle>\<alpha>\<rangle>\<phi>) and (\<forall>\<psi>_i \<in> \<Psi>. expr \<psi>_i \<le> n) --> (expr \<And>\<Psi>) <= n\<close> 

lemma mon_pos:
  fixes n1 and n2 and n3 and n4::enat and n5 and n6 and \<alpha>
  assumes A1: "less_eq_t (expr (hml_pos \<alpha> \<phi>)) (n1, n2, n3, n4, n5, n6)"
  shows "less_eq_t (expr \<phi>) (n1, n2, n3, n4, n5, n6)" 
proof-
  from A1 have E_rest: 
"expr_2 \<phi> \<le> n2 \<and> expr_3 \<phi> \<le> n3 \<and> expr_4 \<phi> \<le> n4 \<and> expr_5 \<phi> \<le> n5 \<and>expr_6 \<phi> \<le> n6" 
    using expr.simps 
    by simp
  from A1 have "1 + expr_1 \<phi> \<le> n1"
    using expr_1.simps(1) by simp
  hence "expr_1 \<phi> \<le> n1" 
    using ile_eSuc plus_1_eSuc(1) dual_order.trans by fastforce
  with E_rest show ?thesis by simp
qed

subsection \<open>lemmas to work with Max, that i didnt find in linorder_class.Max (might have missed them)\<close>

lemma Max_le_set:
  fixes A::"nat set" and B::"nat set"
  assumes A1: "finite A" and A2: "finite B" and "A \<noteq> {}" and "B \<noteq> {}"
  shows "(Max A \<le> Max B) = (\<forall>x \<in> A. \<exists>y \<in> B. x \<le> y)"
proof cases
  assume "A = {}" thus ?thesis using assms by simp
next
  assume "A \<noteq> {}" 
  then show "(Max A \<le> Max B) = (\<forall>x\<in>A. \<exists>y\<in>B. x \<le> y)"
  proof-
    have left: "(Max A \<le> Max B) \<Longrightarrow> (\<forall>x\<in>A. \<exists>y\<in>B. x \<le> y)" 
      using assms
      by (meson Max.boundedE Max_in)
    have right: "(\<forall>x\<in>A. \<exists>y\<in>B. x \<le> y) \<Longrightarrow> (Max A \<le> Max B)"
      using assms by (blast intro: order.antisym Max_in Max_ge_iff[THEN iffD2])
    from left right show ?thesis by auto
  qed
qed

lemma Max_of_union:
  assumes fin_A: "finite A" and fin_B: "finite B" and ne_A: "A \<noteq> {}" and ne_B: "B \<noteq> {}"
  shows "Max (A \<union> B) = Max ({Max A} \<union> {Max B})"
proof-
  have A1: "Max (A \<union> B) \<le> Max ({Max A} \<union> {Max B})"
    by (simp add: Max.union fin_A fin_B ne_A ne_B)
  have A2: "Max ({Max A} \<union> {Max B}) \<le> Max (A \<union> B)"
    using fin_A fin_B ne_A ne_B by auto
  from A1 A2 show ?thesis by (rule Orderings.antisym)
qed

subsection \<open>lemmas to handle the pos_r function\<close>

lemma "less_eq_t (e_sup (expr ` (pos_r (xs)))) (e_sup (expr ` xs))"
proof-
  have "(pos_r xs) \<subseteq> xs" 
    using pos_r.simps filter_is_subset
    by force 
  thus ?thesis
    using less_eq_t.simps expr.simps e_sup_def
    oops

lemma expr_mon_wrt_pos_r: 
"less_eq_t (e_sup (expr ` (pos_r xs))) (e_sup (expr ` (pos_r (xs \<union> {a}))))"
  sorry

lemma expr_1_mon_wrt_pos_r: 
"Sup (expr_1 ` (pos_r xs)) \<le> Sup (expr_1 ` (pos_r (xs \<union> {a})))"
proof-
  from expr_mon_wrt_pos_r have 
1: "(Sup (fst ` (expr ` (pos_r xs)))) \<le> (Sup (fst ` (expr ` (pos_r (xs \<union> {a})))))"
    using less_eq_t.simps
    unfolding e_sup_def
    by blast
  fix \<phi>:: "('a, 's)hml"
  have "\<forall>S. (fst ` expr ` S) = {fst(expr s)|s. s \<in> S}" 
    by blast
  hence "\<forall>S. (fst ` expr ` S) = expr_1 ` S"
    by auto
  hence "(fst ` (expr ` (pos_r xs))) = expr_1 ` (pos_r xs)" 
"(fst ` (expr ` (pos_r (xs \<union> {a})))) = expr_1 ` (pos_r (xs \<union> {a}))"
    by blast+
  with 1 show ?thesis 
    by simp
qed

lemma mon_expr_1_pos_r: 
  "Sup (expr_1 ` (pos_r xs)) \<le> Sup (expr_1 ` xs)"
  sorry

lemma pos_r_del_max:
  assumes "\<forall>x\<in> xs. expr_1 x < expr_1 a"
  shows "pos_r (xs \<union> {a}) = xs"
proof-
  define max_val where "max_val \<equiv> (Sup (expr_1 ` (xs \<union> {a})))"
  define max_elem where "max_elem \<equiv> (SOME \<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val)"
  define xs_new where "xs_new = (xs \<union> {a}) - {max_elem}"
  have ne: "(xs \<union> {a}) \<noteq> {}" 
    by blast
  show ?thesis
  proof(cases "finite (expr_1 ` xs)")
    case True
    hence "Sup (expr_1 ` (xs \<union> {a})) = (sup (expr_1 a) (Sup (expr_1 ` xs)))"
      by simp
    hence "max_val = expr_1 a"
      using assms sup_enat_def True Sup_enat_def
      unfolding max_val_def
      by fastforce
    hence "max_elem = a"
      using assms Sup_enat_def
      unfolding max_elem_def max_val_def Un_insert_right insert_iff order_less_irrefl 
      by fastforce 
    hence "xs_new = xs"
      unfolding xs_new_def
      using assms 
      by fastforce
    then show ?thesis 
      using pos_r.simps
      unfolding xs_new_def max_elem_def max_val_def by simp 
  next
    case False
    hence "Sup (expr_1 ` xs) = \<infinity>"
      using Sup_enat_def 
      by auto
    hence "expr_1 a = \<infinity>" 
      using assms
      by (metis enat_ord_simps(6) less_SUP_iff not_less_iff_gr_or_eq)
    hence "\<forall>x \<in> xs. expr_1 x < \<infinity>"
      using assms
      by presburger
    have "max_val = \<infinity>"
      unfolding max_val_def
      using False Sup_enat_def
      by simp
    have "max_elem = a" 
      using False Sup_enat_def \<open>\<forall>x\<in>xs. expr_1 x < \<infinity>\<close> \<open>expr_1 a = \<infinity>\<close> 
      unfolding max_elem_def max_val_def
      by force
    hence "xs_new = xs"
      unfolding xs_new_def
      using assms by fastforce
    then show ?thesis using pos_r.simps 
      unfolding xs_new_def max_elem_def max_val_def 
      by metis 
  qed
qed

lemma mon_conj:
  fixes n1 and n2 and n3 and n4 and n5 and n6 and xs and ys
  assumes "less_eq_t (expr (hml_conj I \<Phi> J \<Psi>)) (n1, n2, n3, n4, n5, n6)"
  shows "(\<forall>x \<in> (\<Phi> ` I). less_eq_t (expr x) (n1, n2, n3, n4, n5, n6))" 
"(\<forall>y \<in> (\<Psi> ` J). less_eq_t (expr y) (n1, n2, n3, n4, n5, n6))"
proof-
  have e1_eq: "expr_1 (hml_conj I \<Phi> J \<Psi>) = Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Psi>) ` J)"
    using expr_1_conj by blast
  have e2_eq: "expr_2 (hml_conj I \<Phi> J \<Psi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J)"
    using expr_2_conj by blast
  have e3_eq: "expr_3 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Psi>) ` J))"
    using expr_3_conj by blast
  have e4_eq: "expr_4 (hml_conj I \<Phi> J \<Psi>) = Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Psi>) ` J)"
    using expr_4_conj by blast
  have e5_eq: "expr_5 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Psi>) ` J \<union> (expr_1 \<circ> \<Psi>) ` J))"
    using expr_5_conj by blast
  have e6_eq: "expr_6 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J)))"
    using expr_6_conj by blast

  have e1_le: "expr_1 (hml_conj I \<Phi> J \<Psi>) \<le> n1" and
e2_le: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> n2" and
e3_le: "expr_3 (hml_conj I \<Phi> J \<Psi>) \<le> n3" and
e4_le: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> n4" and
e5_le: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> n5" and
e6_le: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> n6"
    using less_eq_t.simps expr.simps assms
    by metis+

  from e1_eq e1_le have e1_pos: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> n1"
and e1_neg: "Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> n1"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by metis+
  hence e1_le_pos: "\<forall>x\<in>\<Phi> ` I. expr_1 x \<le> n1"
and e1_le_neg: "\<forall>y\<in>\<Psi> ` J. expr_1 y \<le> n1"
    by (simp add: Sup_le_iff)+

  from e2_eq e2_le have e2_pos: "Sup ((expr_2 \<circ> \<Phi>) ` I) <= n2"
and e2_neg: "Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> n2"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (metis (no_types, lifting) dual_order.trans ile_eSuc plus_1_eSuc(1))+

  from e3_eq e3_le have e3_pos: "Sup ((expr_3 \<circ> \<Phi>) ` I) <= n3"
and e3_neg: "Sup ((expr_3 \<circ> \<Psi>) ` J) <= n3"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e4_eq e4_le have e4_pos: "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> n4"
and e4_neg: "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> n4"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e5_eq e5_le have e5_pos: "Sup ((expr_5 \<circ> \<Phi>) ` I) <= n5"
and e5_neg: "Sup ((expr_5 \<circ> \<Psi>) ` J) <= n5"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e6_eq e6_le have e6_pos: "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> n6"
and e6_neg: "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> n6"
    using Sup_union_distrib le_sup_iff sup_enat_def
     apply (simp add: Sup_le_iff)
    using Sup_union_distrib le_sup_iff sup_enat_def e6_eq e6_le
    by metis

  from e6_neg have e6_neg: "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> n6"
    using Sup_enat_def eSuc_def
    by (metis dual_order.trans eSuc_Sup i0_lb ile_eSuc image_comp)


  show "\<forall>x\<in>\<Phi> ` I. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6)"
    using e1_pos e2_pos e3_pos e4_pos e5_pos e6_pos
expr.simps less_eq_t.simps
    by (simp add: Sup_le_iff)

  show "\<forall>y\<in>\<Psi> ` J. less_eq_t (expr y) (n1, n2, n3, n4, n5, n6)"
    using e1_neg e2_neg e3_neg e4_neg e5_neg e6_neg
expr.simps less_eq_t.simps
    by (simp add: Sup_le_iff)
qed

lemma expr_TT:
  assumes "TT_like \<chi>"
  shows "expr \<chi> = (0, 1, 0, 0, 0, 0)"
using assms
proof (induction \<chi>)
  case 1
  then show ?case by simp
next
  case (2 \<Phi> I \<Psi> J)
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

lemma expr_2_lb: "expr_2 f \<ge> 1"
proof(induction f)
  case TT
  then show ?case by simp
next
  case (hml_pos x1 f)
  then show ?case by simp
next
  case (hml_conj x1 x2 x3 x4)
  then show ?case
    by simp 
qed

subsection \<open>The set of formulas with prices less then or equal to 
(\<infinity>, 1, 0, 0, 0, 0) is a subset of the HML trace subset\<close>

lemma trace_right: 
  assumes "HML_trace \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using assms
proof(induct \<phi> rule:HML_trace.induct)
  case trace_tt
  then show ?case by simp
next
  case (trace_conj \<psi>s n\<psi>s)
  have "(expr_4 (hml_conj {} \<psi>s {} n\<psi>s)) = 0"
    using expr_4.simps Sup_enat_def by auto
  then show ?case by auto
next
  case (trace_pos \<phi> \<alpha>)
  then show ?case by simp
qed

subsection \<open>The HML trace set is a subset of the set of formulas with prices less then or equal to 
(\<infinity>, 1, 0, 0, 0, 0)\<close>

\<comment> \<open>The set induced by the coordinates (\<infinity>, 1, 0, 0, 0, 0) only includes empty conjunctions\<close>
lemma HML_trace_conj_empty:
  assumes A1: "less_eq_t (expr (hml_conj I \<Phi> J \<Psi>)) (\<infinity>, 1, 0, 0, 0, 0)" 
  shows "I = {} \<and> J = {}"
proof-
  have "expr_2 (hml_conj I \<Phi> J \<Psi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J)"
    using formula_prices_list.expr_2_conj by blast
  with assms have "... \<le> 1"
    using expr.simps less_eq_t.simps
    by simp
  hence le_0: "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 0"
    by simp
  hence le_0: "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<le> 0" "\<forall>x \<in> ((expr_2 \<circ> \<Psi>) ` J). x \<le> 0"
    using Sup_le_iff UnCI
    by metis+
  have "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<ge> 1" 
    "\<forall>x \<in> ((expr_2 \<circ> \<Psi>) ` J). x \<ge> 1" using expr_2_lb
    by fastforce+
  with le_0 show ?thesis using imageI 
    by simp
qed

lemma trace_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  shows "(HML_trace \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using trace_tt by blast
next
  case (hml_pos \<alpha> \<phi>)
  then show ?case 
    using trace_pos by simp
next
  case (hml_conj I \<Phi> J \<Psi>)
  then show ?case using HML_trace_conj_empty trace_conj
    by metis
qed

lemma HML_trace_lemma: 
"(HML_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using trace_left trace_right by blast

lemma simulation_right:
  assumes "HML_simulation \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using assms
proof(induction \<phi> rule:HML_simulation.induct)
  case sim_tt
  then show ?case by simp 
next
  case (sim_pos \<phi> \<alpha>)
  then show ?case 
    using trace_right by force
next
  case (sim_conj \<Phi> I \<Psi> J)
  have e5_eq: "expr_5 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Psi>) ` J \<union> (expr_1 \<circ> \<Psi>) ` J))"
    using expr_5.simps
    by force
  from sim_conj have "\<forall>x\<in>\<Phi> ` I. expr_5 x \<le> 0"
    using expr.simps 
    by force
  hence "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff comp_apply image_iff
    by (smt (verit, ccfv_SIG))
  hence e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 0" 
    using e5_eq local.sim_conj by force

  have e6_eq: "expr_6 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J)))"
    using expr_6.simps
    by force
  from sim_conj have "\<forall>x\<in>\<Phi> ` I. expr_6 x \<le> 0"
    using expr.simps 
    by force
    hence "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff comp_apply image_iff
    by (smt (verit, ccfv_SIG))
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 0" 
    using e6_eq local.sim_conj
    by force
  then show ?case 
    using less_eq_t.simps expr.simps e5 e6 
    by simp 
qed

lemma expr_6_conj:
  assumes "(\<Psi> ` J) \<noteq> {}"
  shows "expr_6 (hml_conj I \<Phi> J \<Psi>) \<ge> 1"
proof-
  have e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J)))"
    using expr.simps
    by simp
  have "\<forall>A::enat set. Sup A \<ge> 0" 
    by simp
  from assms have "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<ge> 1"
    using eSuc_def Sup_enat_def SUP_image eSuc_Sup bot_enat_def
    by (metis iless_eSuc0 image_is_empty linorder_not_le one_eSuc zero_ne_eSuc)
  hence "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J))) \<ge> 1"
    by (simp add: Sup_union_distrib sup.coboundedI2)
  with e6 show ?thesis by simp
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
  assumes "(less_eq_t (expr (hml_conj I \<Phi> J \<Psi>)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" 
  shows "(\<Psi> ` J) = {}"
proof(rule ccontr)
  assume "\<Psi> ` J \<noteq> {}"
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<ge> 1"
    using Sup_enat_def eSuc_def
    by (metis SUP_image eSuc_Sup iless_eSuc0 image_is_empty linorder_not_le one_eSuc zero_ne_eSuc)
  hence "expr_6 (hml_conj I \<Phi> J \<Psi>) \<ge> 1"
    using expr_6.simps
    by (simp add: Sup_union_distrib sup.coboundedI2)
  thus False using assms by simp
qed

lemma simulation_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  shows "(HML_simulation \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case 
    using sim_tt by blast 
next
  case (hml_pos x1 \<phi>)
  then show ?case using sim_pos by simp 
next
  case (hml_conj I \<Phi> J \<Psi>)
  have "\<forall>x \<in> (\<Phi> ` I). less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
"\<forall>x \<in> (\<Psi> ` J). less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
    using hml_conj mon_conj
    by metis+
  hence "\<forall>x \<in> (\<Phi> ` I). HML_simulation x"
"\<forall>x \<in> (\<Psi> ` J).HML_simulation x"
    using hml_conj
    by (metis image_iff range_eqI)+
  have "\<Psi> ` J = {}" using x2_empty
    using hml_conj.prems by blast
  with \<open>\<forall>x \<in> (\<Phi> ` I). HML_simulation x\<close> show ?case using sim_conj by blast
qed

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
  case (failure_conj I \<Phi> J \<Psi>)
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

  from failure_conj have e1_neg: "\<forall>j \<in> J. expr_1 (\<Psi> j) \<le> 1"
and e2_neg: "\<forall>j \<in> J. expr_2 (\<Psi> j) = 1"
and e3_neg: "\<forall>j \<in> J. expr_3 (\<Psi> j) = 0"
and e4_neg: "\<forall>j \<in> J. expr_4 (\<Psi> j) = 0"
and e5_neg: "\<forall>j \<in> J. expr_5 (\<Psi> j) = 0"
and e6_neg: "\<forall>j \<in> J. expr_6 (\<Psi> j) = 0"
    using e1_tt e5_tt e2_tt e3_tt e4_tt e6_tt
    by fastforce+
  hence "(Sup ((expr_5 \<circ> \<Psi>) ` J \<union> (expr_1 \<circ> \<Psi>) ` J)) \<le> 1"
    using Sup_enat_def
    by (smt (verit, del_insts) Sup_le_iff Un_iff comp_apply image_iff nle_le not_one_le_zero)
  hence e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using expr_5_conj expr_\<psi>s e5_2 
    by (simp add: Sup_union_distrib)
  from e2_2 e2_neg failure_conj have "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff Sup_union_distrib)
  hence e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2" 
    using expr_2_conj one_add_one
    by (metis add_left_mono)
  from e1_2 e3_2 have "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Psi>) ` J) \<le> 0"
    by (metis (no_types, lifting) SUP_bot_conv(2) Sup_union_distrib bot_enat_def comp_apply e3_neg le_zero_eq sup.orderE)
  hence e3: "expr_3 (hml_conj I \<Phi> J \<Psi>) \<le> 0" 
    using expr_3_conj
    by auto
  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    by (metis SUP_image e1_2 le_zero_eq mon_expr_1_pos_r)
  hence "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Psi>) ` J) \<le> 0"
    using e4_2 failure_conj Sup_union_distrib bot_enat_def comp_apply e4_neg
    by (metis (no_types, lifting) SUP_bot_conv(2) le_zero_eq max_def sup_max) 
  hence e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0" 
    using expr_4_conj
    by auto
  from failure_conj e6_2 e6_neg have "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
    by (metis (mono_tags, lifting) SUP_least comp_apply le_zero_eq)
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using eSuc_def comp_apply
    by (metis eSuc_Sup image_comp image_empty le_zero_eq nle_le one_eSuc) 
  with failure_conj e6_2 e6_tt have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J))) \<le> 1"
    using one_eSuc e6_neg image_cong le_sup_iff bot.extremum_uniqueI bot_enat_def comp_apply
    by (simp add: Sup_union_distrib)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using expr_6_conj
    by auto
  from e2 e3 e4 e5 e6 show ?case
    using less_eq_t.simps expr.simps 
    by fastforce
qed

(*
function conj_flattened :: "('a, 's) hml \<Rightarrow> bool"
  where
"conj_flattened TT = True" |
"conj_flattened (hml_pos \<alpha> \<psi>) = conj_flattened \<psi>" |
"conj_flattened (hml_conj I \<Phi> J \<Psi>) = 
(\<forall>x \<in> (\<Phi> ` I). (x \<noteq> TT) \<and> (\<nexists>K \<chi>s L n\<chi>s. x = hml_conj K \<chi>s L n\<chi>s) \<and> conj_flattened x)"
  using hml.exhaust by blast+

text \<open>A well-founded order on formulas\<close>
inductive_set HML_wf_rel :: \<open>('a, 's)hml rel\<close>
  where
\<open>(\<phi> = (\<Phi> i) \<and> i \<in> I) \<Longrightarrow> (\<phi>, hml_conj I \<Phi> J \<Psi>) \<in> HML_wf_rel\<close> |
    \<open>(\<phi>, (hml_pos \<alpha> \<phi>)) \<in> HML_wf_rel\<close>

lemma HML_wf_rel_is_wf: "wf HML_wf_rel"
  unfolding wf_def
proof safe
  fix P \<phi>
  assume "\<forall>(\<phi>::('a, 's)hml). (\<forall>(\<phi>'::('a, 's)hml). (\<phi>', \<phi>) \<in> HML_wf_rel \<longrightarrow> P \<phi>') \<longrightarrow> P \<phi>"
  thus "P \<phi>"
  proof(induct \<phi>)
    case TT
    then show ?case
      using HML_wf_rel.cases by blast
  next
    case (hml_pos \<alpha> \<psi>)
    have "(\<psi>, (hml_pos \<alpha> \<psi>)) \<in> HML_wf_rel"
      by (simp add: HML_wf_rel.intros(2)) 
    then show ?case
      using hml_pos 
      by (smt (verit, ccfv_SIG) HML_wf_rel.simps hml.distinct(5) hml.inject(1))
  next
    case (hml_conj I \<Phi> J \<Psi>)
    hence "\<forall>x \<in> (\<Phi> ` I). P x"
and "\<forall>y \<in> (\<Psi> ` J). P y"
      by blast+
    hence "(\<forall>i j \<phi>. ((\<phi> = (\<Phi> i) \<and> i \<in> I) \<or> (\<phi> = (\<Psi> j) \<and> j \<in> J)) \<longrightarrow> P \<phi>)"
      by blast
    hence "(\<forall>\<phi>'. (\<phi>', (hml_conj I \<Phi> J \<Psi>)) \<in> HML_wf_rel \<longrightarrow> P \<phi>')"
      using HML_wf_rel.cases
      by (metis hml.distinct(6) hml.inject(2))
    thus ?case using hml_conj(3)
      by blast
  qed
qed

termination 
  using HML_wf_rel_is_wf
  apply standard
  apply (simp add: HML_wf_rel.intros)
  by (metis (no_types, lifting) HML_wf_rel.intros(1) image_iff)

lemma conj_flattened_alt: "conj_flattened (hml_conj I \<Phi> J \<Psi>) =
(\<forall>x \<in> (\<Phi> ` I). (\<exists>\<alpha> \<phi>. x = hml_pos \<alpha> \<phi>) \<and> conj_flattened x)"
proof
  show "(\<forall>x\<in>\<Phi> ` I. (\<exists>\<alpha> \<phi>. x = hml_pos \<alpha> \<phi>) \<and> conj_flattened x) \<Longrightarrow>
    conj_flattened (hml_conj I \<Phi> J \<Psi>)"
    using conj_flattened.simps Un_iff hml.simps(8) 
    by auto
  show "conj_flattened (hml_conj I \<Phi> J \<Psi>) \<Longrightarrow>
    (\<forall>x\<in>\<Phi> ` I. (\<exists>\<alpha> \<phi>. x = hml_pos \<alpha> \<phi>) \<and> conj_flattened x)"
    using conj_flattened.simps(3) hml.distinct(2) hml.simps(4, 8)
    by (metis (no_types, opaque_lifting) hml.exhaust)
qed
*)

(*Idee: statt alles zu flatten nur positive Conj flatten?,
(weil nur dort expr function flatten benötigt? - prüfen)*)
(*Can really every formula be flattened? (negated conjunction wird zu disjunktion über negierte klauseln, wie übersetzen?)*)

(*
primrec flatten_\<phi> ::"('a, 'i) hml \<Rightarrow> ('a, 'i) hml" and
    flatten_\<phi>_conj :: "('a, 'i) hml set \<Rightarrow> ('a, 'i) hml set" where
"flatten_\<phi> TT = TT" |
"flatten_\<phi> (hml_pos \<alpha> \<psi>) = (hml_pos \<alpha> (flatten_\<phi> \<psi>))" |
"flatten_\<phi> (hml_conj I \<Phi> J \<Psi>) = (
let \<Psi>_new = (\<lambda>x. if x \<in> J then flatten_\<phi> (\<Psi> x) else undefined);
    \<Phi>_new = (\<lambda>x. if x \<in> J then flatten_\<phi>_conj {\<Psi> x} else undefined)
in hml_conj I \<Phi> J \<Psi>_new
)" |
"flatten_\<phi>_conj {} = {}" |
"flatten_\<phi>_conj (hml_pos \<alpha> \<psi>) = (hml_pos \<alpha> \<psi>)" |
"flatten_\<phi>_conj (hml_conj I \<Phi> J \<Psi>) = "
*)
(*
let x1_flat = (map flatten_\<phi>_conj x1);
    x2_flat = (map flatten_\<phi>_conj x2);
    new_x1 = foldl (\<lambda>(y1, y2) (input1, input2). (y1 @ input1, y2 @ input2)) ([], []) x1_flat;
    new_x2 = foldl (\<lambda>(y1, y2) (input1, input2). (y1 @ input1, y2 @ input2)) ([], []) x2_flat
in (HML_conj ((fst new_x1) @ (snd new_x2)) ((snd new_x1) @ (fst new_x2))))" |
"flatten_\<phi>_conj (HML_poss \<alpha> \<psi>) = ([(HML_poss \<alpha> (flatten_\<phi> \<psi>))], ([]::'a formula_list list))" |
"flatten_\<phi>_conj (HML_conj x1 x2) = (
let x1_flat = (map flatten_\<phi>_conj x1);
    x2_flat = map flatten_\<phi>_conj x2;
    new_x1 = foldl (\<lambda>(y1, y2) (input1, input2). (y1 @ input1, y2 @ input2)) ([], []) x1_flat;
    new_x2 = foldl (\<lambda>(y1, y2) (input1, input2). (y1 @ input1, y2 @ input2)) ([], []) x2_flat
in (fst(new_x1) @ snd (new_x2), snd(new_x1) @ fst(new_x2)))"
*)

context lts
begin

(*
(*TODO*)
lemma flatten_\<phi>_flattens:
  shows "conj_flattened (flatten_\<phi> \<phi>)"
  using conj_flattened.simps flatten_\<phi>.simps
  oops

lemma flattened_equivalent:
  shows "(p \<Turnstile> \<phi>) = (p \<Turnstile> (flatten_\<phi> \<phi>))"
proof
  oops
*)

end

lemma failure_pos_tt_like:
  assumes "less_eq_t (expr (hml_conj I \<Phi> J \<Psi>)) (\<infinity>, 2, 0, 0, 1, 1)"
shows "(\<forall>i \<in> I. TT_like (\<Phi> i))"
proof(rule ccontr)
  assume "\<not> (\<forall>i\<in>I. TT_like (\<Phi> i))"
  then obtain x where "x \<in> (\<Phi> ` I)" "\<not> TT_like x"
    using ex_in_conv 
    by fastforce 
  have "expr_2 x \<ge> 1"
    using expr_2_lb
    by blast
  from assms have "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    by simp
  hence "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 2"
    using expr_2_conj
    by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 1"
    by (metis enat_add_left_cancel_le i1_ne_infinity one_add_one)
  hence "expr_2 x \<le> 1"
    using \<open>x \<in> (\<Phi> ` I)\<close> Sup_enat_def
    by (metis Sup_le_iff UnCI comp_apply image_iff)
  show False
  proof(cases x)
    case TT
    with \<open>\<not> TT_like x\<close> show False
      using TT_like.intros(1) by blast
  next
    case (hml_pos \<alpha> \<phi>)
    hence "expr_1 x \<ge> 1" 
      by simp
    hence "expr_3 (hml_conj I \<Phi> J \<Psi>) \<ge> 1"
      using expr_3_conj \<open>x \<in> \<Phi> ` I\<close>
      by (smt (verit, del_insts) SUP_bot_conv(2) Sup_union_distrib bot_enat_def comp_apply 
iless_eSuc0 image_iff linorder_not_le one_eSuc sup_eq_bot_iff)
    with assms show False 
      using expr_3.simps
      by auto
  next
    case (hml_conj x31 x32 x33 x34)
    with \<open>expr_2 x \<le> 1\<close> have "expr_2 (hml_conj x31 x32 x33 x34) \<le> 1"
      by blast
    from hml_conj have "(\<not>(x32 ` x31) = {} \<or> \<not>(x34 ` x33) = {})"
      using TT_like.intros(2) \<open>\<not> TT_like x\<close> 
      by auto
    then show False
    proof
      assume "x34 ` x33 \<noteq> {}"
      then obtain y where "y \<in> (x34 ` x33)" 
        by blast
      from expr_2_lb have "expr_2 y \<ge> 1"
        by blast
      hence "expr_2 (hml_conj x31 x32 x33 x34) \<ge> 2"
        using expr_2_conj \<open>y \<in> (x34 ` x33)\<close> 
        by (smt (verit) SUP_bot_conv(2) SUP_image Sup_union_distrib add_left_mono bot_enat_def 
iless_eSuc0 linorder_not_le one_add_one one_eSuc sup_eq_bot_iff)
      then show False using \<open>expr_2 (hml_conj x31 x32 x33 x34) \<le> 1\<close>
        by simp
    next
      assume "x32 ` x31 \<noteq> {}"
then obtain y where "y \<in> (x32 ` x31)" 
        by blast
      from expr_2_lb have "expr_2 y \<ge> 1"
        by blast
      hence "expr_2 (hml_conj x31 x32 x33 x34) \<ge> 2"
        using expr_2_conj \<open>y \<in> (x32 ` x31)\<close> 
        by (smt (verit) SUP_bot_conv(2) SUP_image Sup_union_distrib add_left_mono bot_enat_def 
iless_eSuc0 linorder_not_le one_add_one one_eSuc sup_eq_bot_iff)
      then show False using \<open>expr_2 (hml_conj x31 x32 x33 x34) \<le> 1\<close>
        by simp
    qed
  qed
qed

lemma expr_2_le_1:  
  assumes "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
  shows "\<Phi> ` I = {}" "\<Psi> ` J = {}"
proof-
  from assms have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J)  \<le> 1"
    using expr_2_conj
    by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 0"
    by fastforce
  hence "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J). x \<le> 0"
    using Sup_le_iff    
    by metis
  with expr_2_lb have "(expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J = {}"
    using all_not_in_conv comp_apply imageI image_empty not_one_le_zero
    by (metis Orderings.order_eq_iff UnI2 Un_empty_right all_not_in_conv zero_le)
  then show "\<Phi> ` I = {}" "\<Psi> ` J = {}"
    by fastforce+
qed

lemma expr_2_expr_5_restrict_negations: 
  assumes "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2" "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
  shows "(\<forall>j \<in> J. (TT_like (\<Psi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Psi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
proof
  fix j 
  assume "j \<in> J"
  then obtain \<psi> where "\<psi> = (\<Psi> j)"
    by blast
  hence "\<psi> \<in> (\<Psi> ` J)"
    using \<open>j \<in> J\<close> 
    by blast
  from assms(1) have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 2"
    using expr_2_conj by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 1"
    using one_add_one enat_add_left_cancel_le
    by (metis infinity_ne_i1)
  hence e2_\<psi>: "expr_2 \<psi> \<le> 1"
    by (simp add: Sup_le_iff \<open>\<psi> = \<Psi> j\<close> \<open>j \<in> J\<close>)
  show "TT_like (\<Psi> j) \<or> (\<exists>\<alpha> \<chi>. \<Psi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)"
  proof(cases \<psi>)
    case TT
    then show ?thesis
      by (simp add: TT_like.intros(1) \<open>\<psi> = \<Psi> j\<close>)
  next
    case (hml_pos \<alpha> \<chi>)
    have "TT_like \<chi>"
    proof(cases \<chi>)
      case TT
      then show ?thesis
        using TT_like.intros(1) by blast
    next
      case (hml_pos x21 x22)
      hence "1 \<le> expr_1 \<chi> "
        using expr_1_pos by simp
      have "expr_1 \<psi> = 1 + expr_1 \<chi>"
        using expr_1_pos \<open>\<psi> = hml_pos \<alpha> \<chi>\<close>
        by force
      hence "expr_1 \<psi> \<ge> 2"
        using add_left_mono \<open>expr_1 \<chi> \<ge> 1\<close> one_add_one
        by metis
      hence "Sup ((expr_1 \<circ> \<Psi>) ` J) \<ge> 2"
        using \<open>\<psi> = \<Psi> j\<close> \<open>j \<in> J\<close> SUP_image
        by (metis Sup_upper2 imageI)
      hence "expr_5 (hml_conj I \<Phi> J \<Psi>) \<ge> 2"
        using expr_5_conj
        by (smt (verit, del_insts) Sup_union_distrib le_sup_iff nle_le)
      with assms(2) have False       
        by (meson numeral_le_one_iff order_trans semiring_norm(69))
      then show ?thesis by simp
    next
      case (hml_conj x31 x32 x33 x34)
      hence "expr_2 \<chi> = expr_2 \<psi>"
        using hml_pos expr_2_pos
        by fastforce
      with e2_\<psi> hml_pos have "x32 ` x31 = {}" "x34 ` x33 = {}"
        using expr_2_le_1
        by (metis hml_conj)+
      then show ?thesis 
        using TT_like.simps hml_conj 
        by fastforce
    qed
    then show ?thesis
      using \<open>\<psi> = \<Psi> j\<close> hml_pos by blast
  next
    case (hml_conj x31 x32 x33 x34)
    then show ?thesis using e2_\<psi> expr_2_le_1 TT_like.simps
      by (metis \<open>\<psi> = \<Psi> j\<close>)
  qed
qed

lemma failure_left:
  fixes \<phi>
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  shows "HML_failure \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using failure_tt by simp
next
  case (hml_pos x1 \<phi>)
  with mon_pos have "HML_failure \<phi>"
    by simp
  then show ?case using failure_pos 
    by fastforce
next
  case (hml_conj I \<Phi> J \<Psi>)
  with failure_pos_tt_like have "\<forall>i \<in>I. TT_like (\<Phi> i)"
    by blast
  have "(\<forall>j \<in> J. (TT_like (\<Psi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Psi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
    using expr_2_expr_5_restrict_negations hml_conj(3) less_eq_t.simps expr.simps
    by metis
  then show ?case using \<open>\<forall>i \<in>I. TT_like (\<Phi> i)\<close> failure_conj 
    by blast
qed

lemma failure_lemma:
  shows "(HML_failure \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using failure_left failure_right by blast

lemma expr_4_read:
  fixes \<alpha>
  assumes A1: "HML_readiness \<phi>" and A2: "less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1)"
  shows "expr_4 (hml_pos \<alpha> \<phi>) \<le> 1"
proof-
  from assms have "expr_4 \<phi> \<le> 1"
    using less_eq_t.simps expr.simps
    by simp
  then show ?thesis 
    by force
qed

lemma readiness_right:
  assumes A1: "HML_readiness \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using assms
proof(induction \<phi>)
  case read_tt
  then show ?case by simp
next
  case (read_pos \<phi> \<alpha>)
  then show ?case
    by simp
next
  case (read_conj \<Phi> I \<Psi> J)
  from assms have "(\<forall>x \<in> (\<Phi> ` I) \<union> (\<Psi> ` J). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    using local.read_conj by blast
  hence "(\<forall>x \<in> (\<Phi> ` I) \<union> (\<Psi> ` J). less_eq_t (expr x) (1, 1, 0, 0, 0, 0))"
    using e1_tt e2_tt e3_tt e4_tt e5_tt e6_tt expr.simps expr_TT
    by (metis dual_order.refl i0_lb less_eq_t.simps)
  hence f1: "\<forall>x \<in> ((expr_1 \<circ> \<Phi>) ` I). x \<le> 1"
 "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<le> 1"
"\<forall>x \<in> ((expr_3 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_4 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_5 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_6 \<circ> \<Phi>) ` I). x \<le>  0"
and f2: "\<forall>x \<in> ((expr_1 \<circ> \<Psi>) ` J). x \<le> 1"
 "\<forall>x \<in> ((expr_2 \<circ> \<Psi>) ` J). x \<le> 1"
"\<forall>x \<in> ((expr_3 \<circ> \<Psi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_4 \<circ> \<Psi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_5 \<circ> \<Psi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_6 \<circ> \<Psi>) ` J). x \<le> 0"
    using expr.simps 
    by simp+

  have "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1"
and "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1"
and "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff f1
         apply (simp add: SUP_least)
    using Sup_le_iff f1
         apply (simp add: SUP_least)
    using Sup_le_iff f1
    by (metis)+

  have "Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1"
and "Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> 1"
and "Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_3 \<circ> \<Psi>) ` J) \<le> 0" 
using Sup_le_iff f2
         apply (simp add: SUP_least)
    using Sup_le_iff f2
         apply (simp add: SUP_least)
    using Sup_le_iff f2
    by (metis)+

  have e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> 1\<close> expr_2_conj one_add_one
    by (metis Sup_union_distrib add_left_mono le_sup_iff)
  have e3: "expr_3 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_3 \<circ> \<Psi>) ` J) \<le> 0\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0\<close> 
one_add_one expr_3_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  from \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) <= 1" 
    using SUP_image dual_order.trans mon_expr_1_pos_r 
    by metis 
  hence e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 1" 
    using \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0\<close>
one_add_one expr_4_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  have e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1" 
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1\<close> expr_5_conj 
    by (simp add: Sup_union_distrib)
  from \<open>Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0\<close> have "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using eSuc_def f2(6)
    by (metis eSuc_Sup image_comp image_is_empty nle_le one_eSuc zero_le) 
    hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_6_conj 
    by (simp add: Sup_union_distrib)
  from e2 e3 e4 e5 e6 show ?case using less_eq_t.simps expr.simps 
    by (metis enat_ord_code(3))
qed

lemma expr_2_expr_3_restrict_positives:
  assumes "(expr_2 (hml_conj I \<Phi> J \<Psi>)) \<le> 2" "(expr_3 (hml_conj I \<Phi> J \<Psi>)) \<le> 1"
  shows "(\<forall>x \<in> (\<Phi> ` I). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
proof
  fix x
  assume "x \<in> \<Phi> ` I"
  hence "expr_2 x \<le> Sup (expr_2 ` \<Phi> ` I)"
    by (simp add: Sup_upper)
hence "expr_2 x \<le> Sup ((expr_2 \<circ> \<Phi>) ` I)"
  by (simp add: SUP_image)
  hence "expr_2 x \<le> Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J)"
    by (simp add: Sup_union_distrib sup.coboundedI1)
  hence "expr_2 x \<le> 1" using assms(1) expr_2_conj one_add_one
    by (metis enat_add_left_cancel_le expr_2_lb le_iff_add le_sup_iff plus_1_eSuc(1) sup.orderE)
  show "TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)"
  proof(cases x)
    case TT
    then show ?thesis using TT_like.simps
      by blast
  next
    case (hml_pos \<alpha> \<psi>)
    have "TT_like \<psi>"
    proof(cases \<psi>)
      case TT
      then show ?thesis using TT_like.simps by blast
    next
      case (hml_pos x21 x22)
      hence "expr_1 x \<ge> 2" 
        using \<open>x = hml_pos \<alpha> \<psi>\<close> expr_1.simps(3) one_add_one 
        by (metis add_left_mono one_eSuc plus_1_eSuc(1) zero_le)
      hence "Sup ((expr_1 \<circ> \<Phi>) ` I) >= 2"
        using \<open>x \<in> (\<Phi> ` I)\<close> Sup_enat_def
        by (metis SUP_image SUP_lessD linorder_not_le)
      hence "(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Psi>) ` J)) \<ge> 2"
        using Sup_enat_def Sup_union_distrib
        by (metis sup.coboundedI1)
      hence "expr_3 (hml_conj I \<Phi> J \<Psi>) \<ge> 2"
        using expr_3_conj
        by force
      with assms(2) have False 
        by (meson numeral_le_one_iff order_trans semiring_norm(69))
      then show ?thesis by simp
    next
      case (hml_conj I' \<Phi>' J' \<Psi>')
      hence "expr_2 (hml_conj I' \<Phi>' J' \<Psi>') = expr_2 x"
        by (simp add: hml_pos)
      hence "expr_2 (hml_conj I' \<Phi>' J' \<Psi>') \<le> 1"
        using \<open>expr_2 x \<le> 1\<close> 
        by presburger
      hence "(\<Phi>' ` I') = {}" 
        "(\<Psi>' ` J') = {}" 
        using expr_2_le_1 
        by blast+
      thus ?thesis using hml_conj TT_like.simps
        by fastforce
    qed    
    then show ?thesis
      using hml_pos by blast
  next
    case (hml_conj x31 x32 x33 x34)
    with \<open>expr_2 x \<le> 1\<close> have "(x32 ` x31) = {}" "(x34 ` x33) = {}" 
      using expr_2_le_1 
      by blast+
    then show ?thesis 
      using TT_like.simps hml_conj
      by fastforce
  qed
qed

lemma readiness_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  shows "HML_readiness \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using read_tt by blast 
next
  case (hml_pos x1 \<phi>)
  then show ?case 
  using read_pos
  by (metis mon_pos)
next
  case (hml_conj I \<Phi> J \<Psi>)
  hence pos:"(\<forall>x \<in> (\<Phi> ` I). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    using expr.simps less_eq_t.simps expr_2_expr_3_restrict_positives
    by metis
  have neg: "(\<forall>j \<in> J. (TT_like (\<Psi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Psi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
    using hml_conj(3) expr_2_expr_5_restrict_negations expr.simps less_eq_t.simps
    by metis
  then show ?case using pos read_conj Un_iff image_iff 
    by (smt (verit))
qed

lemma readiness_lemma:
  shows "(HML_readiness \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using readiness_left readiness_right by blast

lemma impossible_futures_right:
  assumes A1: "HML_impossible_futures \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  using assms
proof(induction \<phi>)
  case if_tt
  then show ?case by simp
next
  case (if_pos \<phi> \<alpha>)
  then show ?case by simp
next
  case (if_conj \<Phi> I \<Psi> J)
  assume pos_empty: "\<Phi> ` I = {}" and neg_trace: "\<forall>x\<in>\<Psi> ` J. HML_trace x"
  hence "\<forall>x\<in>\<Psi> ` J. expr_3 x = 0"
and "\<forall>x\<in>\<Psi> ` J. expr_2 x = 1"
    using enat_0_iff(2) trace_right expr_2_lb nle_le 
    by fastforce+
  hence "Sup (expr_3 ` \<Psi> ` J) = 0"
    by (metis SUP_bot_conv(2) bot_enat_def)
  have "Sup (expr_3 ` \<Phi> ` I) \<le> 0" 
    using pos_empty Sup_empty bot_enat_def
  by force 
  hence e3: "expr_3 (hml_conj I \<Phi> J \<Psi>) = 0"
    using expr_3_conj pos_empty \<open>Sup (expr_3 ` \<Psi> ` J) = 0\<close>
    by (simp add: image_comp)
  have "Sup (expr_2 ` \<Psi> ` J) \<le> 1"
    using \<open>\<forall>x\<in>\<Psi> ` J. expr_2 x = 1\<close>
    by (simp add: Sup_le_iff)
  have "Sup (expr_2 ` \<Phi> ` I) \<le> 0"
    using pos_empty image_empty bot_enat_def
    by fastforce
  hence e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using pos_empty \<open>Sup (expr_2 ` \<Psi> ` J) \<le> 1\<close> one_add_one expr_2_conj
    by (metis (no_types, opaque_lifting) add_left_mono image_Un image_comp sup_bot_left)
  have "\<forall>x\<in>\<Psi> ` J. expr_6 x \<le> 0"
    using enat_0_iff(2) trace_right expr.simps less_eq_t.simps neg_trace
    by auto
  hence "Sup((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff one_eSuc)
  from pos_empty have "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    by (simp add: bot_enat_def)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using expr_6_conj \<open>Sup((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1\<close> pos_empty 
    by auto
  have "\<forall>x\<in>\<Psi> ` J. expr_4 x \<le> 0" 
    using neg_trace trace_right
    by auto
  hence "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
    using SUP_image SUP_least
    by metis
  from pos_empty have "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))) \<le> 0"
    by (simp add: bot_enat_def)+
  hence e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using \<open>Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0\<close> expr_4_conj pos_empty
    by auto
  from e2 e3 e4 e6 show ?case using expr.simps less_eq_t.simps
    by auto
qed

lemma e5_e6_ge_1: 
  fixes \<phi>
  assumes A1: "expr_5 \<phi> \<ge> 1"
  shows "expr_6 \<phi> \<ge> 1"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  (*Wenn e5 x1 \<ge> 1, dann nach I.V. 1 \<le> expr_6 x1a, wenn e5 x2 \<ge> 1, dann nach I.V. 1 \<le> expr_6 x2a,
dann kann man bei beiden, da dann ihre Mengen nicht leer sein können, sagen, dass e6 \<ge> 1 (mit e6_eq).
Wenn e1 x2 \<ge> 1, dann ist {1 + expr_6 y | y. y \<in> set x2} (bzw x2) nicht leer und damit
Max {1 + expr_6 y | y. y \<in> set \<Psi>} \<ge> 1.*)
  have fin_e5: "finite ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    by simp
  have max_0: "Max {0} < (1::nat)" 
    by simp
  have e5_eq: "expr_5 (HML_conj x1 x2) =
Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    by (rule expr_5_set)
  from this HML_conj have 
"Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 1"
    by simp
  from this fin_e5 max_0 have e1_ge_1: "Max({expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 1"
    by (smt (verit, best) Max.union Un_infinite less_one max_nat.comm_neutral not_one_le_zero sup_assoc sup_bot.right_neutral sup_commute)
  have e6_eq: "expr_6 (HML_conj x1 x2) =
Max({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
    by (rule HML_subsets.expr_6_union_neg)
  from HML_conj show "1 \<le> expr_6 (HML_conj x1 x2)"
  proof(cases x1)
    case Nil
    then have "{expr_5 x | x. x \<in> set x1} = {}" 
      by simp
    then have "({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) =
({0} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
      by simp
    then have e5_eq_2: "Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) =
Max({0} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
      by simp
    then show ?thesis 
    proof(cases x2)
      case Nil
      then have "({expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) = {}"
        by simp
      then have "Max({0} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) = 0" 
        by simp
      from this e5_eq HML_conj e5_eq_2 have False 
        by simp
      then show ?thesis by simp
    next
      case (Cons a list)
      then have ne_e5: "{expr_5 y | y. y \<in> set x2} \<noteq> {}"
        by auto
      from Cons have ne_e1: "{expr_1 y | y. y \<in> set x2} \<noteq> {}"
        by auto
      have fin: "finite ({0} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
        by simp
      from e5_eq HML_conj e5_eq_2 ne_e5 ne_e1 fin have "Max ({expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 1"
        by simp
      then have "(Max {expr_5 y | y. y \<in> set x2} \<ge> 1) \<or> (Max {expr_1 y | y. y \<in> set x2} \<ge> 1)"
        by (metis (no_types, lifting) Max_of_union fin_e5 finite_Un less_one linorder_le_less_linear ne_e5 sup_bot_right sup_idem)

      then show ?thesis
      proof(rule disjE)
        assume A2: "1 \<le> Max {expr_5 y |y. y \<in> set x2}"
        have fin: "finite {expr_5 y |y. y \<in> set x2}"
          by simp
        from this A2 ne_e5 have "\<exists>x2a \<in> set x2. expr_5 x2a \<ge> 1" 
          by (smt (verit, ccfv_SIG) Max_in ex_in_conv mem_Collect_eq set_empty2)
        then obtain x2a where x2a_in_x2: "x2a \<in> set x2" and e5_x2a: "expr_5 x2a \<ge> 1"
          by auto
        then have e6_x1a: "expr_6 x2a \<ge> 1"
          by (rule local.HML_conj(2))
        from x2a_in_x2 have ne:"{1 + expr_6 y | y. y \<in> set x2} \<noteq> {}"
          by auto
        have fin: "finite {1 + expr_6 y | y. y \<in> set x2}"
          by simp
        from fin ne have e6_x2: "Max {1 + expr_6 y | y. y \<in> set x2} \<ge> 1"
          by (smt (verit, ccfv_SIG) Max_in le_add1 mem_Collect_eq)
        have subs: "{1 + expr_6 y | y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
          by auto
        have fin: "finite ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
          by simp
        from this subs e6_x2 e6_eq show "expr_6 (HML_conj x1 x2) \<ge> 1"
          by (metis (no_types, lifting) Max_mono dual_order.trans ne)  
      next
        assume A4: "1 \<le> Max {expr_1 y |y. y \<in> set x2}"
        from ne_e1 have "x2 \<noteq> []" by simp
        then have ne:"{1 + expr_6 y | y. y \<in> set x2} \<noteq> {}"
          by simp
        have fin: "finite {1 + expr_6 y | y. y \<in> set x2}"
          by simp
        from fin ne have e6_x2: "Max {1 + expr_6 y | y. y \<in> set x2} \<ge> 1"
          by (smt (verit, ccfv_SIG) Max_in le_add1 mem_Collect_eq)
        have subs: "{1 + expr_6 y | y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
          by auto
        have fin: "finite ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
          by simp
        from this subs e6_x2 e6_eq show "expr_6 (HML_conj x1 x2) \<ge> 1"
          by (metis (no_types, lifting) Max_mono dual_order.trans ne)
      qed
    qed
  next
    case (Cons a list)
    then have "x1 \<noteq> []" 
      by simp
    from Cons show ?thesis 
    proof(cases x2)
      case Nil
      have fin: "finite {expr_6 x |x. x \<in> set x1}" 
        by simp
      from Nil have "({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) =
({0} \<union> {expr_5 x | x. x \<in> set x1})" 
        by simp
      then have "Max ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) =
Max ({0} \<union> {expr_5 x | x. x \<in> set x1})" 
        by simp
      from this e5_eq HML_conj(3) have "Max ({0} \<union> {expr_5 x |x. x \<in> set x1}) \<ge> 1"
        by simp
      then have "Max ({expr_5 x |x. x \<in> set x1})\<ge> 1"
        using e1_ge_1 local.Nil by auto
      from this HML_conj(1) \<open>x1 \<noteq> []\<close> have "\<exists>x1a \<in> set x1. 1 \<le> expr_6 x1a"
        by (smt (verit) Max_in all_not_in_conv fin_e5 finite_Un mem_Collect_eq set_empty)
      from this fin \<open>x1 \<noteq> []\<close> have e6_x1: "Max {expr_6 x |x. x \<in> set x1} \<ge> 1" 
        using Max_ge_iff by blast
      have subs: "{expr_6 x |x. x \<in> set x1} \<subseteq> ({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2}) "
        by auto
      have fin:"finite ({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2}) "
        by simp
      from this subs e6_x1 e6_eq show ?thesis 
        by (smt (verit, ccfv_threshold) Max_mono One_nat_def \<open>\<exists>x1a\<in>set x1. 1 \<le> expr_6 x1a\<close> 
empty_Collect_eq le_imp_less_Suc less_one linorder_not_less) 
    next
      case (Cons b list2)
      then have "x2 \<noteq> []"
        by simp
      from e1_ge_1 fin_e5 have e5_disj: 
"(Max {expr_5 x | x. x \<in> set x1} \<ge> 1) \<or> (Max {expr_5 y | y. y \<in> set x2} \<ge> 1) \<or>
(Max {expr_1 y | y. y \<in> set x2} \<ge> 1)"
    by (smt (z3) Sup_fin.union Sup_fin_Max Un_absorb1 Un_infinite bot.extremum finite_UnI nle_le sup.bounded_iff sup_commute)
  then show ?thesis 
  proof
    assume ass1: "1 \<le> Max {expr_5 x |x. x \<in> set x1}"
    have fin: "finite {expr_5 x |x. x \<in> set x1}"
      by simp
    have fin_e6: "finite {expr_6 x |x. x \<in> set x1}"
      by simp
    from ass1 fin \<open>x1 \<noteq> []\<close> have "\<exists>x \<in> set x1. expr_5 x \<ge> 1"
      by (smt (verit, best) Max_in empty_Collect_eq list.set_intros(1) mem_Collect_eq neq_Nil_conv)
    then obtain x where x_in: "x \<in> set x1" and x_e5: "expr_5 x \<ge> 1" by auto
    from this have "expr_6 x \<ge> 1" by (rule local.HML_conj(1))
    from this x_in fin_e6 have e6_x1: "Max {expr_6 x |x. x \<in> set x1} \<ge> 1"
      using Max_ge_iff by blast
    have subs: "{expr_6 x |x. x \<in> set x1} \<subseteq> 
({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
      by auto
    have fin: "finite ({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
      by simp
    from this subs e6_eq e6_x1 show ?thesis
      using HML_subsets.expr_6_conj local.Cons by blast
  next
    assume "1 \<le> Max {expr_5 y |y. y \<in> set x2} \<or> 1 \<le> Max {expr_1 y |y. y \<in> set x2}"
    then show ?thesis 
    proof(rule disjE)
      assume ass1: "1 \<le> Max {expr_5 y |y. y \<in> set x2}"
      have fin: "finite {expr_5 y |y. y \<in> set x2}"
        by simp
      have fin_e6: "finite {1 + expr_6 y |y. y \<in> set x2}"
        by simp
      from fin ass1 \<open>x2 \<noteq> []\<close> have "\<exists>y \<in> set x2. expr_5 y \<ge> 1" 
        by (smt (verit, best) Max_in empty_Collect_eq list.set_intros(1) mem_Collect_eq neq_Nil_conv)
      then obtain y where y_in: "y \<in> set x2" and e5_y: "expr_5 y \<ge> 1"
        by auto
      from this have "expr_6 y \<ge> 1" by (rule local.HML_conj(2))
      from this y_in fin_e6 have e6_x1: "Max {1 + expr_6 x |x. x \<in> set x2} \<ge> 1"
        using Max_ge_iff
        by (smt (verit, del_insts) Max_ge add_leE mem_Collect_eq)
      have subs: "{1 + expr_6 x |x. x \<in> set x2} \<subseteq>
({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
        by auto
      have fin: "finite ({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
      by simp
    from this subs e6_eq e6_x1 show ?thesis
      using HML_subsets.expr_6_conj local.Cons by blast
  next
    assume "1 \<le> Max {expr_1 y |y. y \<in> set x2}"
    have fin: "finite {1 + expr_6 y |y. y \<in> set x2}"
      by simp
    from \<open>x2 \<noteq> []\<close> have "{1 + expr_6 y |y. y \<in> set x2} \<noteq> {}"
      by auto
    from fin this have "Max {1 + expr_6 y |y. y \<in> set x2} \<ge> 1"
      by (smt (verit, ccfv_threshold) Max_in le_add1 mem_Collect_eq)
have subs: "{1 + expr_6 x |x. x \<in> set x2} \<subseteq>
({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
        by auto
      have fin: "finite ({0} \<union> {expr_6 x |x. x \<in> set x1} \<union> {1 + expr_6 y |y. y \<in> set x2})"
      by simp
    from this subs e6_eq show ?thesis
      using HML_subsets.expr_6_conj local.Cons by blast
  qed
qed
qed
qed
next
case (HML_poss x1 \<phi>)
  then show ?case by simp
qed


lemma impossible_futures_left:
  assumes A1: "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)" and A2: "conj_flattened \<phi>"
  shows "HML_impossible_futures \<phi>"
  using A1 A2
proof(induction \<phi>)
  case (HML_conj x1 x2)
  have fa_le_x1: "(\<forall>x1a \<in> set x1. less_eq_t (expr x1a) (\<infinity>, 2, 0, 0, \<infinity>, 1))"
    using HML_conj.prems mon_conj by blast
  then have fa_if_x1: "(\<forall>x1a \<in> set x1. HML_impossible_futures x1a)"
    using HML_conj.IH(1) HML_conj.prems(2) conj_flattened.simps(2) by blast
  have fa_le_x2: "(\<forall>x2a \<in> set x2. less_eq_t (expr x2a) (\<infinity>, 2, 0, 0, \<infinity>, 1))"
    using HML_conj.prems mon_conj by blast
  then have fa_if_x2: "(\<forall>x2a \<in> set x2. HML_impossible_futures x2a)"
    using HML_conj.IH(2) HML_conj.prems(2) conj_flattened.simps(2) by blast
  have x1_e: "x1 = []"
  proof(rule ccontr)
    assume "x1 \<noteq> []"
    then obtain x where "x \<in> set x1" by fastforce
    from fa_if_x1 have "HML_impossible_futures x"
      using \<open>x \<in> set x1\<close> by fastforce
    with conj_flattened_alt have "\<exists>\<alpha> \<psi>. x = HML_poss \<alpha> \<psi>"
      using HML_conj.prems(2) \<open>x \<in> set x1\<close> by blast
    then have "expr_1 x \<ge> 1" using expr_1.simps(4) by auto
    have fin: "finite {expr_1 x |x. x \<in> set x1}" by simp
    from \<open>x \<in> set x1\<close> have ne: "{expr_1 x |x. x \<in> set x1} \<noteq> {}" by auto
    from fin ne \<open>x \<in> set x1\<close> \<open>expr_1 x \<ge> 1\<close> have ge_1: "Max {expr_1 x |x. x \<in> set x1} \<ge> 1"
      using Max_ge_iff by blast
    have "expr_3 (HML_conj x1 x2) \<le> 0" using local.HML_conj(3) less_eq_t.simps
      using enat_0_iff(2) by auto
    with expr_3_set have le_0:
"Max ({0} \<union> {expr_3 x |x. x \<in> set x1} \<union> {expr_3 y |y. y \<in> set x2} \<union> {expr_1 x |x. x \<in> set x1}) \<le> 0"
      by metis
    have fin: "finite ({0} \<union> {expr_3 x |x. x \<in> set x1} \<union> {expr_3 y |y. y \<in> set x2} \<union> {expr_1 x |x. x \<in> set x1})"
      by simp
    have subs: "{expr_1 x |x. x \<in> set x1} \<subseteq> ({0} \<union> {expr_3 x |x. x \<in> set x1} \<union> {expr_3 y |y. y \<in> set x2} \<union> {expr_1 x |x. x \<in> set x1})"
      by auto
    from fin subs ge_1 Max_mono ne Nat.le_trans have "Max ({0} \<union> {expr_3 x |x. x \<in> set x1} \<union> {expr_3 y |y. y \<in> set x2} \<union> {expr_1 x |x. x \<in> set x1}) \<ge> 1"
      by blast
    with le_0 show False by simp
  qed
  have e2_eq: "expr_2 (HML_conj x1 x2) = 
Max({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})" 
    by (rule formula_prices_list.expr_2_set)
  have e2_le_2: "expr_2 (HML_conj x1 x2) \<le> 2" 
    using HML_conj(3) numeral_eq_enat by force
  have fin_e2: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})"
    by simp
  from x1_e have "{1 + expr_2 x | x. x \<in> set x1} = {}"
    by auto
  from e2_eq e2_le_2 fin_e2 have e2: "\<forall>x \<in> set x2. expr_2 x \<le> 1" 
    by force
  have e3: "\<forall>x \<in> set x2. expr_3 x \<le> 0" using expr.simps fa_le_x2 less_eq_t.simps
    by (simp add: zero_enat_def)
  have e4: "\<forall>x \<in> set x2. expr_4 x \<le> 0" using expr.simps fa_le_x2 less_eq_t.simps
    by (simp add: zero_enat_def)
  (*Wenn bei einem elem x aus x2 expr_5 x größer 0 wäre, würde es eine Konjunktion über eine nicht leere
Menge an negativen Formeln enthalten, dadurch wäre 
expr_6 HML_conj x1 x2 \<ge> 2*)
  have e5_x_form: "\<forall>x \<in> set x2. \<exists>\<alpha> \<psi>. x = (HML_poss \<alpha> \<psi>)"
    using HML_conj.prems(2) conj_flattened_alt by blast
  have e5: "\<forall>x \<in> set x2. expr_5 x \<le> 0" 
  proof(rule ccontr)
    assume "\<not> (\<forall>x\<in>set x2. expr_5 x \<le> 0)"
    then have "\<exists>x \<in> set x2. expr_5 x \<ge> 1"
      by fastforce
    then obtain x where A3: "x \<in> set x2" and A4: "expr_5 x \<ge> 1"
      by auto
    from A3 have x2_ne: "set x2 \<noteq> {}"
      by auto
    then have ne_e6: "{1 + expr_6 y | y. y \<in> set x2} \<noteq> {}"
      by simp
    from A4 e5_e6_ge_1 have e6_x: "expr_6 x \<ge> 1" 
      by auto    
    from this A3 have ex_e6: "\<exists>x \<in> set x2. expr_6 x \<ge> 1"
      by auto
    have e6_eq:"expr_6 (HML_conj x1 x2) =
Max({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by (rule HML_subsets.expr_6_union_neg)
    have fin_e6: "finite ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by simp
    have fin:"finite {expr_6 x | x. x \<in> set x1}"
      by simp
    from this ne_e6 e6_x A3 ex_e6 have e6_x2: "Max {1 + expr_6 x | x. x \<in> set x2} \<ge> 2"
      by (metis (mono_tags, lifting) Max.coboundedI fin_e6 finite_Un le_trans mem_Collect_eq nat_1_add_1 nat_add_left_cancel_le)
    have subs: "{1 + expr_6 y | y. y \<in> set x2} \<subseteq>
({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})" 
      by auto
    from this e6_eq e6_x2 fin_e6 have "expr_6 (HML_conj x1 x2) \<ge> 2"
      by (metis (no_types, lifting) Max_mono dual_order.trans ne_e6)
    then show False 
      by (smt (verit) HML_conj.prems(1) enat_numeral enat_ord_code(1) expr.simps less_eq_t.simps 
numeral_le_one_iff order.trans semiring_norm(69))
  qed
  have e6: "\<forall>x \<in> set x2. expr_6 x \<le> 0"
  proof(rule ccontr)
    assume "\<not> (\<forall>x\<in>set x2. expr_6 x \<le> 0)"
    then have "\<exists>x \<in> set x2. expr_6 x \<ge> 1"
      by fastforce
    then have x2_ge_2: "\<exists>x \<in> set x2. 1 + expr_6 x \<ge> 2"
      by simp
    then have ne_x2: "{1 + expr_6 y |y. y \<in> set x2} \<noteq> {}"
      by auto
    have fin: "finite {1 + expr_6 y |y. y \<in> set x2}"
      by simp
    from this ne_x2 x2_ge_2 have x2_ge_2: "Max {1 + expr_6 y |y. y \<in> set x2} \<ge> 2" 
      using Max_ge_iff by blast
    have e6_eq: "expr_6 (HML_conj x1 x2) =
Max({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by (rule formula_prices_list.expr_6_set)
    have subs: "{1 + expr_6 y |y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by auto
    have fin: "finite ({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by simp
    from fin subs e6_eq x2_ge_2 have "expr_6 (HML_conj x1 x2) \<ge> 2" 
      by (metis (no_types, lifting) Max_mono dual_order.trans ne_x2)
    then show False 
      by (smt (verit) HML_conj(3) expr.simps less_eq_t.simps numeral_eq_enat numeral_le_one_iff 
of_nat_eq_enat of_nat_le_iff order.trans semiring_norm(69))
  qed
  from e2 e3 e4 e5 e6 HML_trace_lemma have "\<forall>x \<in> set x2. (HML_trace x)" 
    using expr_2_lb one_enat_def verit_la_disequality zero_enat_def by fastforce
  from this x1_e show "HML_impossible_futures (HML_conj x1 x2)"
    using if_conj by blast
next
  case (HML_poss x1 \<phi>)
  then show ?case
    by (simp add: if_pos)
qed

lemma impossible_futures_lemma:
  fixes \<phi>
  assumes "conj_flattened \<phi>"
  shows "HML_impossible_futures \<phi> = less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  using assms impossible_futures_left impossible_futures_right by blast

lemma expr_4_ft_poss:
  fixes \<phi> and \<alpha>
  assumes A1: "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  shows "expr_4 (HML_poss \<alpha> \<phi>) \<le> 0"
proof(cases \<phi>)
  case (HML_conj x11 x12)
  then show ?thesis 
    by (metis assms expr.simps expr_4.simps(1) less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
next
  case (HML_poss x21 x22)
  then show ?thesis 
    by (metis assms expr.simps expr_4.simps(1) less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
qed

(*TODODODODOD*)
lemma possible_futures_right:
  assumes "HML_possible_futures \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  using assms
proof(induction \<phi> rule: HML_possible_futures.induct)
  case (pf_pos \<phi> \<alpha>)
  then show ?case by simp
next
  case (pf_conj xs ys)
  from expr_2_set have e2: "expr_2 (HML_conj xs ys) = Max ({1} \<union> {1 + expr_2 x |x. x \<in> set xs} \<union> {1 + expr_2 y |y. y \<in> set ys})"
    by blast
  from expr_6_set have e6: "expr_6 (HML_conj xs ys) = Max ({0} \<union> {expr_6 x |x. x \<in> set xs} \<union> {1 + expr_6 y |y. y \<in> set ys})"
    by blast
  from pf_conj trace_right have expr_xs: "(\<forall>x\<in>set xs. less_eq_t (expr x) (\<infinity>, 1, 0, 0, 0, 0))" by auto
  from pf_conj trace_right have expr_ys: "(\<forall>y\<in>set ys. less_eq_t (expr y) (\<infinity>, 1, 0, 0, 0, 0))" by auto
  have fin: "finite {expr_6 x |x. x \<in> set xs}" by simp
  from expr_xs have "(\<forall>x\<in>set xs. 1 + expr_2 x \<le> 2)" using less_eq_t.simps expr.simps
    by (simp add: one_enat_def)
  then have "Max {expr_6 x |x. x \<in> set xs} \<le> 2" sorry (*xs empty oder nicht fallunterscheidung *)
(*TODODOD*)
  then show ?case sorry
qed

lemma possible_futures_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)" "conj_flattened \<phi>"
  shows "HML_possible_futures \<phi>"
  using assms
proof induct
  case (HML_conj x1 x2)
  have x1_tr: "\<forall>x \<in> set x1. HML_trace x"
  proof
    fix x
    assume "x \<in> set x1"
    have "expr_2 (HML_conj x1 x2) \<le> 2" using expr.simps HML_conj(3)
      by (simp add: numeral_eq_enat)
    then have e2: "Max({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2}) \<le> 2"
      using expr_2_set 
      by metis
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})"
      by simp
    have subs: "{1 + expr_2 x | x. x \<in> set x1} \<subseteq>
({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})" by auto
    from \<open>x \<in> set x1\<close> have ne: "{1 + expr_2 x | x. x \<in> set x1} \<noteq> {}" by auto
    from ne fin e2 subs have "Max {1 + expr_2 x |x. x \<in> set x1} \<le> 2" by simp
    with \<open>x \<in> set x1\<close> fin subs have "expr_2 x \<le> 1"
      using ne by auto
    then show "HML_trace x"
      using HML_conj(3)
  proof induct
    case conj: (HML_conj l r)
    have e2: "expr_2 (HML_conj l r) = Max({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      using expr_2_set by auto
    have subs: "{1 + expr_2 x | x. x \<in> set l} \<subseteq> ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      by auto
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})" by simp
    from e2 subs fin have "\<forall>x \<in> {1 + expr_2 x | x. x \<in> set l}. x \<le> expr_2 (HML_conj l r)" by simp
    with conj(3) have "\<forall>x \<in> set l. expr_2 x \<le> 0" 
      by fastforce
    with expr_2_lb have l_e: "l = []"
      by (metis all_not_in_conv dual_order.trans not_one_le_zero set_empty2)
    have subs: "{1 + expr_2 y | y. y \<in> set r} \<subseteq> ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      by auto
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})" by simp
    from e2 subs fin have "\<forall>x \<in> {1 + expr_2 y | y. y \<in> set r}. x \<le> expr_2 (HML_conj l r)" by simp
    with conj(3) have "\<forall>x \<in> set r. expr_2 x \<le> 0" by fastforce
    with expr_2_lb have r_e: "r = []"
      by (metis all_not_in_conv dual_order.trans not_one_le_zero set_empty2)
    from l_e r_e show ?case using HML_trace.simps by auto
    next
      case (HML_poss \<alpha> \<phi>)
      then show ?case using HML_list.HML_trace.intros(2) by force
    qed
  qed
  have x2_tr: "\<forall>x \<in> set x2. HML_trace x"
  proof
    fix x
    assume "x \<in> set x2"
    have "expr_2 (HML_conj x1 x2) \<le> 2" using expr.simps HML_conj(3)
      by (simp add: numeral_eq_enat)
    then have e2: "Max({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2}) \<le> 2"
      using expr_2_set 
      by metis
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})"
      by simp
    have subs: "{1 + expr_2 x | x. x \<in> set x1} \<subseteq>
({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})" by auto
    from \<open>x \<in> set x2\<close> have ne: "{1 + expr_2 x | x. x \<in> set x2} \<noteq> {}" by auto
    from ne fin e2 subs have "Max {1 + expr_2 x |x. x \<in> set x2} \<le> 2" by simp
    with \<open>x \<in> set x2\<close> fin subs have "expr_2 x \<le> 1"
      using ne by auto
    then show "HML_trace x"
      using HML_conj(3)
    proof induct
    case conj: (HML_conj l r)
    have e2: "expr_2 (HML_conj l r) = Max({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      using expr_2_set by auto
    have subs: "{1 + expr_2 x | x. x \<in> set l} \<subseteq> ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      by auto
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})" by simp
    from e2 subs fin have "\<forall>x \<in> {1 + expr_2 x | x. x \<in> set l}. x \<le> expr_2 (HML_conj l r)" by simp
    with conj(3) have "\<forall>x \<in> set l. expr_2 x \<le> 0" 
      by fastforce
    with expr_2_lb have l_e: "l = []"
      by (metis all_not_in_conv dual_order.trans not_one_le_zero set_empty2)
    have subs: "{1 + expr_2 y | y. y \<in> set r} \<subseteq> ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})"
      by auto
    have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set l} \<union> {1 + expr_2 y | y. y \<in> set r})" by simp
    from e2 subs fin have "\<forall>x \<in> {1 + expr_2 y | y. y \<in> set r}. x \<le> expr_2 (HML_conj l r)" by simp
    with conj(3) have "\<forall>x \<in> set r. expr_2 x \<le> 0" by fastforce
    with expr_2_lb have r_e: "r = []"
      by (metis all_not_in_conv dual_order.trans not_one_le_zero set_empty2)
    from l_e r_e show ?case using HML_trace.simps by auto
    next
      case (HML_poss \<alpha> \<phi>)
      then show ?case using HML_list.HML_trace.intros(2) by force
    qed
  qed
  from this x1_tr show ?case
    by (simp add: pf_conj x1_tr)
next
  case (HML_poss \<alpha> \<phi>)
  with HML_list.HML_possible_futures.intros(1) show ?case by fastforce
qed

lemma expr_4_ft_conj:
  fixes xs and ys and x
  assumes A1: "((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y \<in> set xs. y = x)) \<and>
       (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
  shows "expr_4 (HML_conj (x#xs) ys) = 0"
proof-
  from A1 have xs_e: "(\<forall>y \<in> set xs. expr y = expr x)"
    by simp
  from A1 have fa_ys: "(\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
    by simp
  have e4_eq: "expr_4 (HML_conj (x#xs) ys) =
Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys})"
    by (rule formula_prices_list.expr_4_set)
  from xs_e have "\<forall>y \<in> set (x#xs). \<forall>z \<in> set (x#xs). expr_1 y = expr_1 z"
    by simp
  from xs_e have "\<forall>y \<in> set (x#xs). \<forall>z \<in> set (x#xs). y = z"
    by (metis A1 set_ConsD)
  from this pos_r_eq have "pos_r (x#xs) = []"
    by blast
  then have e1_0: "expr_1 (HML_conj (pos_r (x#xs))[]) = 0"
    by simp
  have ne_xs: "{expr_4 y|y. y \<in> set (x#xs)} \<noteq> {}"
    by auto
  have fin_xs: "finite {expr_4 y|y. y \<in> set (x#xs)}"
    by simp
  from A1 have e4_x: "expr_4 x = 0"
    using enat_0_iff(2) by auto
  from this xs_e have "\<forall>x \<in> set (x#xs). expr_4 x = 0" 
    by simp
  from this e4_x ne_xs fin_xs have e4_xs_e: "Max {expr_4 y|y. y \<in> set (x#xs)} = 0"
    by (smt (verit, best) Max_in mem_Collect_eq)
  from fa_ys have e4_ys_0: "\<forall>y\<in>set ys. expr_4 y = 0"
    by auto
  have "(\<exists>y. y \<in> set ys) \<or> ys = []"
    using last_in_set by blast
  then show ?thesis
  proof(rule disjE)
    assume "(\<exists>y. y \<in> set ys)"
    then have ne: "{expr_4 y|y. y \<in> set ys} \<noteq> {}"
      by auto
    have fin: "finite {expr_4 y|y. y \<in> set ys}"
      by simp
    have subs: "{expr_4 y|y. y \<in> set ys} \<subseteq> 
({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys})"
      by auto
    from fin ne e4_ys_0 have "Max {expr_4 y|y. y \<in> set ys} = 0"
      by (smt (verit, best) Max_in mem_Collect_eq)
    from this subs have "Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys})
= Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {0})"
      using e4_xs_e ne
      by (smt (verit, ccfv_SIG) Collect_cong e4_ys_0 empty_Collect_eq singleton_conv)
    also from e1_0 have "... = Max ({0} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {0})"
      by simp
    also from e4_xs_e ne_xs fin_xs have "... = Max ({0} \<union> {0})"
      by simp
    also have "... = 0"
      by simp
    finally have 
"Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys}) = 0"
      by this
    from this e4_eq show ?thesis
      by simp
  next
    assume "ys = []"
    then have e4_ys_e: "{expr_4 y|y. y \<in> set ys} = {}" 
      by simp
    from this e4_xs_e have 
"Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys})
= Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {0})"
      using ne_xs by auto
    also from e1_0 have "... = Max {0}"
      by simp
    also have "...  = 0"
      by simp
    finally have 
"Max ({expr_1 (HML_conj (pos_r (x#xs))[])} \<union> {expr_4 y|y. y \<in> set (x#xs)} \<union> {expr_4 y|y. y \<in> set ys}) = 0"
      by this
    from this e4_eq show ?thesis by simp
  qed
qed

lemma failure_trace_right:
  fixes \<phi>
  assumes A1: "(HML_failure_trace \<phi>)"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  using A1
proof(induction \<phi>)
  case (f_trace_pos \<phi> \<alpha>)
  assume A2: "HML_failure_trace \<phi>" and A3: "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  then show ?case
  proof-
    have A4: "expr_4 (HML_poss \<alpha> \<phi>) \<le> 0"
      by (meson A2 expr_4_ft_poss local.f_trace_pos(2))
    have A5: "expr_5 (HML_poss \<alpha> \<phi>) \<le> 1" 
      by (metis expr.simps formula_prices_list.expr_5_pos less_eq_t.simps local.f_trace_pos(2) of_nat_1 of_nat_eq_enat of_nat_le_iff)
    have A6: "expr_6 (HML_poss \<alpha> \<phi>) \<le> 1" 
    by (metis expr.simps formula_prices_list.expr_6_pos less_eq_t.simps local.f_trace_pos(2) of_nat_1 of_nat_eq_enat of_nat_le_iff)
  from A2 A3 A4 A5 A6 show ?thesis
    by (simp add: zero_enat_def)  
  qed
next
    case (f_trace_conj xs ys)
    have e5: "expr_5 (HML_conj xs ys) =
Max({0} \<union> {expr_5 x1 | x1. x1 \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
      by (rule formula_prices_list.expr_5_set)
    have e6: "expr_6 (HML_conj xs ys) =
Max({0} \<union> {expr_6 y | y. y \<in> set xs} \<union> {1 + expr_6 y | y. y \<in> set ys})"
      by (rule HML_subsets.expr_6_union_neg)
    show ?case
    proof(cases xs)
      case Nil
      then have max_eq: 
"({0} \<union> {expr_5 x1 | x1. x1 \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys}) =
({0} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
        by simp
      then have "Max ({0} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys}) \<le> 1" 
        using local.Nil local.f_trace_conj by fastforce
      from this e5 max_eq have e5_le: "expr_5 (HML_conj xs ys) \<le> 1"
        by simp
      from Nil have e6_le: "expr_6 (HML_conj xs ys) \<le> 1"
        using expr_6_fail local.f_trace_conj neg by blast
      from Nil have e4_le: "expr_4 (HML_conj xs ys) \<le> 0"
        using expr_4_fail_neg local.f_trace_conj neg by auto
      from e4_le e5_le e6_le show ?thesis
        by (simp add: one_enat_def zero_enat_def)
    next
      case (Cons a list)
      then have e5: "expr_5 (HML_conj xs ys) =
Max({0} \<union> {expr_5 x1 | x1. x1 \<in> set (a#list)} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
      using formula_prices_list.expr_5_set by blast
      from Cons have e6: "expr_6 (HML_conj xs ys) =
Max({0} \<union> {expr_6 y | y. y \<in> set (a#list)} \<union> {1 + expr_6 y | y. y \<in> set ys})"
        using HML_subsets.expr_6_union_neg by blast
      have e5_x: "expr_5 a \<le> 1"
        by (metis expr.simps less_eq_t.simps list.inject list.simps(3) local.Cons local.f_trace_conj of_nat_1 of_nat_eq_enat of_nat_le_iff)
      from this have e5_fa: "\<forall>y \<in> set (a#list). expr_5 y \<le> 1"
        using f_trace_conj.IH local.Cons by fastforce  
      have ne: "{expr_5 x1 | x1. x1 \<in> set (a#list)} \<noteq> {}"
      by auto
    have fin: "finite {expr_5 x1 | x1. x1 \<in> set (a#list)}"
      by simp
    from e5_x fin ne e5_fa have e5_xs: "Max {expr_5 x1 | x1. x1 \<in> set (a#list)} \<le> 1"
      by auto
    from local.f_trace_conj have fa_poss:"(\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
      by simp
    then have e5_ys: "(\<forall>y\<in>set ys. expr_5 y \<le> 1)" 
        by auto
    from fa_poss have e1_ys: "(\<forall>y\<in>set ys. expr_1 y \<le> 1)" 
      by auto
    have fin: 
"finite ({0} \<union> {expr_5 x1 | x1. x1 \<in> set (a#list)} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
      by simp
    from this e5_xs e5_ys e1_ys have e5_set:
"Max({0} \<union> {expr_5 x1 | x1. x1 \<in> set (a#list)} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})
\<le> 1"
      using ne by auto
    from this e5 have e5: "expr_5 (HML_conj xs ys) \<le> 1" by simp
have e6: "expr_6 (HML_conj (a#list) ys) =
Max({0} \<union> {expr_6 y | y. y \<in> set (a#list)} \<union> {1 + expr_6 y | y. y \<in> set ys})"
      by (rule HML_subsets.expr_6_union_neg)
    have ne_e6: "{expr_6 y | y. y \<in> set (a#list)} \<noteq> {}"
      by auto
    have fin_e6: "finite {expr_6 y | y. y \<in> set (a#list)}"
      by simp
    have "expr_6 a \<le> 1"
      by (metis expr.simps less_eq_t.simps list.inject list.simps(3) local.Cons local.f_trace_conj of_nat_1 of_nat_eq_enat of_nat_le_iff)
    then have e6_xs: "\<forall>y \<in> set (a#list). expr_6 y \<le> 1"
      using local.Cons local.f_trace_conj by fastforce
    from this ne_e6 fin_e6 have e6_xs: "Max {expr_6 y | y. y \<in> set (a#list)} \<le> 1"
      by auto
    from fa_poss have e6_ys: "(\<forall>y \<in> set ys. expr_6 y \<le> 0)"
      by auto
    have fin: 
"finite ({0} \<union> {expr_6 y | y. y \<in> set (a#list)} \<union> {1 + expr_6 y | y. y \<in> set ys}) "
      by simp
    have ne: "{expr_6 y |y. y \<in> set (a # list)} \<noteq> {}"
      by auto
      from fin e6_xs e6_ys ne have "Max({0} \<union> {expr_6 y | y. y \<in> set (a#list)} \<union> {1 + expr_6 y | y. y \<in> set ys}) \<le> 1"
        by auto
      from this e6 have e6: "expr_6 (HML_conj xs ys) \<le> 1"
        using local.Cons by presburger
      from formula_prices_list.expr_1_conj_empty insert_iff list.set(2) local.f_trace_conj pos_r_eq set_empty2 
      have e1_xs: "expr_1 (HML_conj (pos_r (a#list))[]) = 0"
        by (metis list.distinct(1) local.Cons)
have ne_e4: "{expr_4 y|y. y \<in> set (a#list)} \<noteq> {}"
      by auto
    have fin_e4: "finite {expr_4 y|y. y \<in> set (a#list)}"
      by simp
    have "expr_4 a = 0"
      using expr_4_ft_poss f_trace_conj.IH local.Cons by auto
    then have "\<forall>y \<in> set (a#list). expr_4 y = 0"
      using f_trace_conj.IH local.Cons by auto
    from this ne_e4 fin_e4 have e4_xs: "Max {expr_4 y|y. y \<in> set (a#list)} = 0"
      by (smt (verit, ccfv_threshold) Max_in mem_Collect_eq) 
    have fa_ys: "(\<forall>y\<in>set ys. expr_4 y = 0)"
      using local.f_trace_conj by fastforce
    have e4_eq: "expr_4 (HML_conj (a#list) ys) =
Max ({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})" 
      by (rule formula_prices_list.expr_4_set)
    have fin: 
"finite ({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})"
      by simp
    have ne: 
"({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys}) \<noteq> {}"
      by simp
    from e4_eq fa_ys e4_xs e1_xs fin ne local.Cons have e4: "expr_4 (HML_conj xs ys) \<le> 0"
      by (metis (no_types, lifting) bot_nat_0.extremum_unique expr_4_ft_conj list.distinct(1) local.f_trace_conj)
    from e4 e5 e6 show ?thesis
      by (simp add: one_enat_def zero_enat_def)
  qed
qed

lemma ft_conj_ys:
assumes A1: "(less_eq_t (expr (HML_conj xs ys)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" and 
A2: "conj_flattened (HML_conj xs ys)" and
A3: "(\<And>x2a. x2a \<in> set ys \<Longrightarrow> less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x2a)"
shows "(\<forall>y \<in> set ys. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] [])))"

(*Wenn die y in ys nicht diese Form hätten, wäre: 
    Fall 1:   bei Form HML_conj x2 y2: nicht möglich wegen conj_flattened
    Fall 2:   Form HML_poss \<alpha> x2 y2: x2 = y2= [] ist erlaubt, 
              wenn x2 \<noteq> [], muss das elem x HML_poss (wegen conj_flattened) sein, dann expr_5 x \<ge> 2
              wenn y2 \<noteq> [] genauso, das elem muss HML_poss sein, expr_5 x \<ge> 2
              wenn Form (HML_poss \<alpha> (HML_poss \<beta> Rest))*)
proof
  fix y
  assume "y \<in> set ys"
  have e5: "expr_5 (HML_conj xs ys) =
Max({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
    by (rule formula_prices_list.expr_5_set)
  have fin_e5: "finite ({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
    by simp
  show "\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  proof(cases y)
    case (HML_conj x11 x12)
    from HML_conj A2 have False
      using \<open>y \<in> set ys\<close> conj_flattened.simps(2) by blast
    then show ?thesis by simp
  next
    case (HML_poss x21 x22)
    then have e1_y: "expr_1 y = 1 + expr_1 x22"
      by simp
    have "x22 = HML_conj [] []"
    proof(cases x22)
      case (HML_conj x11 x12)
      then show ?thesis
        proof(cases x11)
          case Nil
          then show ?thesis
            proof (cases x12)
              case Nil
              from this \<open>x11 = []\<close> HML_conj show ?thesis by simp
            next
              case (Cons a list)
              from A2 conj_flattened_alt have "\<exists>\<alpha> \<phi>. a = (HML_poss \<alpha> \<phi>)"
                by (metis HML_conj HML_poss \<open>y \<in> set ys\<close> conj_flattened.simps(1) list.set_intros(1) local.Cons)
              then have e1_a: "expr_1 a \<ge> 1"
                by auto
              have e1_x22: "expr_1 x22 = Max({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
                using HML_conj expr_1_set_form by blast
              have fin: "finite {expr_1 y | y. y \<in> set x12}" 
                by simp
              from this e1_a Cons have e1_x12: "Max {expr_1 y | y. y \<in> set x12} \<ge> 1"
                by (metis (mono_tags, lifting) Max.coboundedI dual_order.trans list.set_intros(1) mem_Collect_eq)
              have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
                by simp
              have ne: "({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12}) \<noteq> {}" 
                by simp
              from fin ne e1_x12 e1_x22 have "expr_1 x22 \<ge> 1"
                by (metis (mono_tags, lifting) Max_ge_iff Un_iff e1_a list.set_intros(1) local.Cons mem_Collect_eq)
              from this Cons \<open>y = HML_poss x21 x22\<close> \<open>x22 = HML_conj x11 x12\<close> have e1_y: "expr_1 y\<ge> 2"
                by simp
              have fin: 
"finite ({0} \<union> {expr_5 x |x. x \<in> set xs} \<union> {expr_5 y |y. y \<in> set ys} \<union> {expr_1 y |y. y \<in> set ys})"
                by simp
              from this e5 e1_y HML_poss \<open>y \<in> set ys\<close> have "expr_5 (HML_conj xs ys) \<ge> 2"
                by (metis (mono_tags, lifting) Max.coboundedI UnCI dual_order.trans mem_Collect_eq)
              from this A1 have False
                by (simp add: one_enat_def)
              then show ?thesis by simp
            qed
        next
          case (Cons a list)
              from A2 conj_flattened_alt have "\<exists>\<alpha> \<phi>. a = (HML_poss \<alpha> \<phi>)"
                by (metis HML_conj HML_poss \<open>y \<in> set ys\<close> conj_flattened.simps(1) list.set_intros(1) local.Cons)
              then have e1_a: "expr_1 a \<ge> 1"
                by auto
              have e1_x22: "expr_1 x22 = Max({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
                using HML_conj expr_1_set_form by blast
              have fin: "finite {expr_1 y | y. y \<in> set x11}" 
                by simp
              from this e1_a Cons have e1_x12: "Max {expr_1 y | y. y \<in> set x11} \<ge> 1"
                by (metis (mono_tags, lifting) Max.coboundedI dual_order.trans list.set_intros(1) mem_Collect_eq)
              have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
                by simp
              have ne: "({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12}) \<noteq> {}" 
                by simp
              from fin ne e1_x12 e1_x22 have "expr_1 x22 \<ge> 1"
                by (metis (mono_tags, lifting) Max_ge_iff Un_iff e1_a list.set_intros(1) local.Cons mem_Collect_eq)
              from this Cons \<open>y = HML_poss x21 x22\<close> \<open>x22 = HML_conj x11 x12\<close> have e1_y: "expr_1 y\<ge> 2"
                by simp
              have fin: 
"finite ({0} \<union> {expr_5 x |x. x \<in> set xs} \<union> {expr_5 y |y. y \<in> set ys} \<union> {expr_1 y |y. y \<in> set ys})"
                by simp
              from this e5 e1_y HML_poss \<open>y \<in> set ys\<close> have "expr_5 (HML_conj xs ys) \<ge> 2"
                by (metis (mono_tags, lifting) Max.coboundedI UnCI dual_order.trans mem_Collect_eq)
              from this A1 have False
                by (simp add: one_enat_def)
          then show ?thesis by simp
        qed 
    next
      case (HML_poss x211 x221)
      have fin_ys: "finite {expr_1 y | y. y \<in> set ys}"
        by simp
      from HML_poss have "expr_1 x22 \<ge> 1"
        by simp
      from this e1_y have "expr_1 y \<ge> 2"
        by simp
      from this \<open>y \<in> set ys\<close> fin_ys have e1_ys: "Max {expr_1 y | y. y \<in> set ys} \<ge> 2"
        by (metis (mono_tags, lifting) Max.coboundedI dual_order.trans mem_Collect_eq)
      have subs: "{expr_1 y | y. y \<in> set ys} \<subseteq> 
({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
        by auto
      from this e1_ys e5 fin_e5 have "expr_5 (HML_conj xs ys) \<ge> 2" 
        by (metis (mono_tags, lifting) Max.coboundedI UnCI \<open>2 \<le> expr_1 y\<close> \<open>y \<in> set ys\<close> dual_order.trans mem_Collect_eq)
      from this A1 have False
        by (simp add: one_enat_def)
      then show ?thesis by simp
    qed
    then have "y = HML_poss x21 (HML_conj [] [])"
      using HML_poss by blast
    then show ?thesis by simp
  qed
qed

lemma failure_trace_conj:
  assumes A1: "(less_eq_t (expr (HML_conj xs ys)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" and 
A2: "conj_flattened (HML_conj xs ys)" and
A3: "\<And>x1a. x1a \<in> set xs \<Longrightarrow> less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x1a"
shows "xs = [] \<or> (\<exists>x xs2. xs = (x#xs2) \<and> (HML_failure_trace x \<and> (\<forall>y \<in> set xs2. y = x)))"
proof(cases xs)
  case Nil
  then show ?thesis by simp 
next
  case (Cons a list)
  from A2 conj_flattened_alt have "\<exists>\<alpha> \<phi>. a = (HML_poss \<alpha> \<phi>)" 
    by (metis list.set_intros(1) local.Cons)
  then have e1_x: "expr_1 a \<ge> 1" 
    by auto
  from A1 mon_conj local.Cons have "\<forall>x1a \<in> set (a#list). less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
    by blast
  from this A3 local.Cons have ft_x: "HML_failure_trace a"
    by simp
(*Wenn in xs ein Element y eine andere Form als x hätte:
würde expr_4 (HML_conj (x#xs) ys) > 0 gelten, da \<forall>x. expr_1 x \<ge> 1 gilt,
pos_r (x#xs) würde nur entweder x oder größte elemente in xs löschen,
dann Max{expr_1 y| y \<in> pos_r(x#xs)} \<ge> 1*)
  have y_eq_x: "(\<forall>y \<in> set xs. y = a)"
  proof(rule ccontr)
    assume "\<not> (\<forall>y\<in>set xs. y = a)"
    then have A3: "(\<exists>y \<in> set xs. y \<noteq> a)"
      by simp
(* Lemma benötigt: (\<exists>x \<in> set xs. \<exists>y \<in> set xs. x \<noteq> y) \<longrightarrow> pos_r (xs) \<noteq> []*)
    from this e1_x local.Cons have "pos_r (a#list) \<noteq> []" sorry
    then have "\<exists>y. y \<in> set (pos_r (a#list))"
      using list.set_sel(1) by blast
    then obtain y where A4: "y \<in> set (pos_r (a#list))"
      by auto
    have "set (pos_r (a#list)) \<subseteq> set (a#list)"
      by (metis filter_is_subset pos_r.simps(2))
    from A2 conj_flattened_alt this A4 local.Cons have "\<exists>\<alpha> \<phi>. y = (HML_poss \<alpha> \<phi>)"
      by blast
    then have e1_y: "expr_1 y \<ge> 1" 
      by auto
    from A4 have ne: "{expr_1 y|y. y \<in> set (pos_r (a#list))} \<noteq> {}" 
      by blast
    have fin: "finite {expr_1 y|y. y \<in> set (pos_r (a#list))}" 
      by simp
    from fin ne e1_y A4 have e1_pos_r: "Max {expr_1 y|y. y \<in> set (pos_r (a#list))} \<ge> 1"
      using Max_ge_iff by blast
    have e1_eq: "expr_1 (HML_conj (pos_r (a#list)) ([]::'a formula_list list)) = 
Max ({0} \<union> {expr_1 z |z. z \<in> set (pos_r (a#list))} \<union> {expr_1 y |y. y \<in> set ([]::'a formula_list list)})" 
      by (rule formula_prices_list.expr_1_set_form)
    have fin_e1: "finite ({0} \<union> {expr_1 z |z. z \<in> set (pos_r (a#list))} \<union> {expr_1 y |y. y \<in> set ([]::'a formula_list list)})"
      by simp
    have ne_e1: 
"({0} \<union> {expr_1 z |z. z \<in> set (pos_r (a#list))} \<union> {expr_1 y |y. y \<in> set ([]::'a formula_list list)}) \<noteq> {}"
      by auto
    have subs: "{expr_1 y|y. y \<in> set (pos_r (a#list))} \<subseteq>
({0} \<union> {expr_1 z |z. z \<in> set (pos_r (a#list))} \<union> {expr_1 y |y. y \<in> set ([]::'a formula_list list)})"
      by auto
    from fin_e1 ne_e1 subs e1_pos_r e1_eq have e1_ge_1:
"expr_1 (HML_conj (pos_r (a#list)) ([]::'a formula_list list)) \<ge> 1"
      by (metis (no_types, lifting) Max.subset_imp dual_order.trans ne)
    from A1 local.Cons have e4_0: "expr_4 (HML_conj (a#list) ys) = 0"
      by (metis enat_0_iff(2) expr.simps le_zero_eq less_eq_t.simps)
    have e4_eq: "expr_4 (HML_conj (a#list) ys) =
Max ({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})"
      by (rule formula_prices_list.expr_4_set)
    from this e4_0 have 
"Max ({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})
= 0" 
      by simp
    have subs: "{expr_1 (HML_conj (pos_r (a#list))[])} \<subseteq>
({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})"
      by simp
    have fin: "finite ({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys})"
      by simp
    have ne: "({expr_1 (HML_conj (pos_r (a#list))[])} \<union> {expr_4 y|y. y \<in> set (a#list)} \<union> {expr_4 y|y. y \<in> set ys}) \<noteq> {}"
      by auto
    from subs e1_ge_1 fin ne e4_eq have "expr_4 (HML_conj (a#list) ys) \<ge> 1"
      by (metis (no_types, lifting) Max_ge_iff insert_subset)
    from this e4_0 show False by simp
  qed
  from this ft_x have "HML_failure_trace a \<and> (\<forall>y\<in>set xs. y = a)"
    by simp
  then show ?thesis
    by (metis list.set_intros(2) local.Cons)
qed

lemma failure_trace_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" and A2: "conj_flattened \<phi>"
  shows "(HML_failure_trace \<phi>)"
  using A1 A2
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from this ft_conj_ys have x2: "\<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    by (smt (verit, best) conj_flattened.simps(2))
  from HML_conj failure_trace_conj have x1:
"x1 = [] \<or> (\<exists>x xs2. x1 = x # xs2 \<and> HML_failure_trace x \<and> (\<forall>y\<in>set xs2. y = x))" 
    by auto
  from x1 x2 show ?case 
    by (simp add: f_trace_conj)
next
  case (HML_poss \<alpha> \<psi>)
  then show ?case
    by (simp add: f_trace_pos)
qed

lemma ft_lemma: 
  assumes"conj_flattened \<phi>"
  shows "(HML_failure_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" 
  using assms failure_trace_left failure_trace_right by blast

lemma ready_trace_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1)" "conj_flattened \<phi>"
  shows "HML_ready_trace \<phi>"
  using assms
proof induct
  case (HML_conj x1 x2)
  have e5: "expr_5 (HML_conj x1 x2) =
Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    using expr_5_set by blast
  from HML_conj(3) have "expr_5 (HML_conj x1 x2) \<le> 1" using expr.simps
    by (simp add: one_enat_def)
  have neg_part: "(\<forall>y \<in> set x2. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] [])))"
(*Wegen Flattened: y hat pos Form, wenn bei (HML_poss \<alpha> \<phi>) \<phi> die eine andere Form als HML_conj [] [] hat, 
dann expr_1 y \<ge> 2 und dann expr_5 (HML_conj x1 x2) \<ge> 2 WIDERSPR*)
(*Reicht es hier zu sagen, direkt hinter Knojunktionen dürfen keine leeren Konjunktionen kommen?
Dann muss irgendwo in der Konjunktion ein nicht poss-operator sein (Vorher können Konjnktionen bel.geschachtelt werden.).*)
  proof
    fix y
    assume "y \<in> set x2"
    with HML_conj(4) obtain \<alpha> \<phi> where "(y = HML_poss \<alpha> \<phi>)" using conj_flattened_alt
      by metis
    have "\<phi> = (HML_conj [] [])"
    proof(cases \<phi>)
      case conj: (HML_conj x11 x12)
      from HML_conj(4) have "conj_flattened \<phi>" using conj_flattened.simps
        by (metis \<open>y = HML_poss \<alpha> \<phi>\<close> \<open>y \<in> set x2\<close>)
      have "(x11 = [] \<and> x12 = []) \<or> (\<exists>x. x \<in> set x11 \<or> x \<in> set x12)"
        using last_in_set by blast   
      then show ?thesis 
      proof
        assume "x11 = [] \<and> x12 = []"
        with conj show ?thesis by simp
      next
        assume "\<exists>x. x \<in> set x11 \<or> x \<in> set x12"
        then obtain x where "x \<in> set x11 \<or> x \<in> set x12" by auto
        then show ?thesis
        proof
          assume "x \<in> set x11"
          with conj \<open>conj_flattened \<phi>\<close> have "\<exists>\<gamma> \<chi>. x = HML_poss \<gamma> \<chi>" using conj_flattened_alt by blast
          then have "expr_1 x \<ge> 1" by auto
          have fin: "finite {expr_1 x |x. x \<in> set x11}" by simp
          with \<open>expr_1 x \<ge> 1\<close> \<open>x \<in> set x11\<close> have "Max {expr_1 x |x. x \<in> set x11} \<ge> 1" using Max_ge_iff
            by blast
          from conj have "expr_1 \<phi> =
Max({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})" using expr_1_set_form
            by blast
          have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
            by simp
          have subs: "{expr_1 x | x. x \<in> set x11} \<subseteq>
({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
            by auto
          from fin subs \<open>Max {expr_1 x |x. x \<in> set x11} \<ge> 1\<close> have 
"Max ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12}) \<ge> 1" using Max_mono \<open>x \<in> set x11\<close> dual_order.trans 
            by blast
          with conj expr_1_set_form have "expr_1 \<phi> \<ge> 1"
            by metis
          with \<open>(y = HML_poss \<alpha> \<phi>)\<close> have "expr_1 y \<ge> 2" by simp
          have fin: "finite {expr_1 y | y. y \<in> set x2}" by simp
          with \<open>y \<in> set x2\<close> \<open>expr_1 y \<ge> 2\<close> have "Max {expr_1 y | y. y \<in> set x2} \<ge> 2"
            using Max_ge_iff by blast
          have subs: "{expr_1 y | y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
            by auto
          have fin: "finite ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
            by simp
          from fin subs \<open>Max {expr_1 y | y. y \<in> set x2} \<ge> 2\<close> have 
"Max ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 2"
            using Max_mono \<open>y \<in> set x2\<close> dual_order.trans by blast
          with e5 have "expr_5 (HML_conj x1 x2) \<ge> 2" by simp
          with \<open>expr_5 (HML_conj x1 x2) \<le> 1\<close> have False by simp
          then show ?thesis by simp
        next
          assume "x \<in> set x12"
          with conj \<open>conj_flattened \<phi>\<close> have "\<exists>\<gamma> \<chi>. x = HML_poss \<gamma> \<chi>" using conj_flattened_alt by blast
          then have "expr_1 x \<ge> 1" by auto
          have fin: "finite {expr_1 y | y. y \<in> set x12}" by simp
with \<open>expr_1 x \<ge> 1\<close> \<open>x \<in> set x12\<close> have "Max {expr_1 x |x. x \<in> set x12} \<ge> 1" using Max_ge_iff
            by blast
          from conj have "expr_1 \<phi> =
Max({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})" using expr_1_set_form
            by blast
          have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
            by simp
          have subs: "{expr_1 x | x. x \<in> set x12} \<subseteq>
({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
            by auto
          from fin subs \<open>Max {expr_1 x |x. x \<in> set x12} \<ge> 1\<close> have 
"Max ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12}) \<ge> 1" using Max_mono \<open>x \<in> set x12\<close> dual_order.trans 
            by blast
          with conj expr_1_set_form have "expr_1 \<phi> \<ge> 1"
            by metis
          with \<open>(y = HML_poss \<alpha> \<phi>)\<close> have "expr_1 y \<ge> 2" by simp
have fin: "finite {expr_1 y | y. y \<in> set x2}" by simp
          with \<open>y \<in> set x2\<close> \<open>expr_1 y \<ge> 2\<close> have "Max {expr_1 y | y. y \<in> set x2} \<ge> 2"
            using Max_ge_iff by blast
          have subs: "{expr_1 y | y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
            by auto
          have fin: "finite ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
            by simp
          from fin subs \<open>Max {expr_1 y | y. y \<in> set x2} \<ge> 2\<close> have 
"Max ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 2"
            using Max_mono \<open>y \<in> set x2\<close> dual_order.trans by blast
          with e5 have "expr_5 (HML_conj x1 x2) \<ge> 2" by simp
          with \<open>expr_5 (HML_conj x1 x2) \<le> 1\<close> have False by simp
          then show ?thesis by simp
        qed
      qed
    next
      case (HML_poss \<beta> \<psi>)
      then have "expr_1 \<phi> \<ge> 1" by simp
      with \<open>(y = HML_poss \<alpha> \<phi>)\<close>  have "expr_1 y \<ge> 2" by simp
      have fin: "finite {expr_1 y | y. y \<in> set x2}" by simp
      with \<open>y \<in> set x2\<close> \<open>expr_1 y \<ge> 2\<close> have "Max {expr_1 y | y. y \<in> set x2} \<ge> 2"
        using Max_ge_iff by blast
      have subs: "{expr_1 y | y. y \<in> set x2} \<subseteq> ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
        by auto
      have fin: "finite ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
        by simp
      from fin subs \<open>Max {expr_1 y | y. y \<in> set x2} \<ge> 2\<close> have 
"Max ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<ge> 2"
        using Max_mono \<open>y \<in> set x2\<close> dual_order.trans by blast
      with e5 have "expr_5 (HML_conj x1 x2) \<ge> 2" by simp
      with \<open>expr_5 (HML_conj x1 x2) \<le> 1\<close> have False by simp
      then show ?thesis by simp
    qed
    with \<open>(y = HML_poss \<alpha> \<phi>)\<close> show "\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])" by simp
  qed
    (*TODO*)
(* x = y: wenn x \<noteq> y, dann expr_1 x \<ge> 2, expr_1 y \<ge> 2, deshalb Max {expr_1 (HML_conj (pos_r \<Phi>)[])} \<ge> 2
\<longrightarrow> expr_4 (HML_conj xs ys) \<ge> 2
(x, y haben die Form \<langle>\<alpha>\<rangle>\<psi>, wenn \<psi>'s nicht die Form \<And>[] [] haben, dann expr_1 \<psi> \<ge> 1)*)
(*HML_ready_trace x: Durch induktion*)

  have "(\<forall>x \<in> set x1. \<forall>y \<in> set x1. 
(\<forall>\<alpha> \<beta>. x \<noteq> HML_poss \<alpha> (HML_conj [] []) \<and> y \<noteq> HML_poss \<beta> (HML_conj [] [])) \<longrightarrow> (x = y \<and> HML_ready_trace x))"
  proof safe
    fix x y
    assume x_in: "x \<in> set x1" and y_in: "y \<in> set x1" and 
precon: "\<forall>\<alpha> \<beta>. x \<noteq> HML_poss \<alpha> (HML_conj [] []) \<and> y \<noteq> HML_poss \<beta> (HML_conj [] [])"
    then show "x = y"
    proof-
      from x_in HML_conj(4) obtain \<alpha> \<psi> where x_eq: "x = HML_poss \<alpha> \<psi>" using conj_flattened_alt by metis
      from y_in HML_conj(4) obtain \<beta> \<chi> where y_eq: "y = HML_poss \<beta> \<chi>" using conj_flattened_alt by metis
      show ?thesis 
      proof(cases \<psi>)
        case conj_\<psi>: (HML_conj x11 x12)
        with precon x_eq have "x11 \<noteq> [] \<or> x12 \<noteq> []"
          by blast
        then obtain z where z_in: "z \<in> (set x11) \<union> (set x12)"
          using list.set_sel(1) by auto
        with x_eq HML_conj(4) x_in have "\<exists>\<alpha> \<phi>. z = HML_poss \<alpha> \<phi>" using conj_flattened.simps
          by (metis Un_iff conj_\<psi> conj_flattened_alt)
        then have "expr_1 z \<ge> 1" using expr_1.simps by auto
        with z_in conj_\<psi> have "expr_5 \<psi> \<ge> 1" using expr_5_set sorry
        then show ?thesis sorry
      next
        case poss_\<psi>: (HML_poss x21 x22)
        then show ?thesis sorry
      qed
    qed
    from x_in HML_conj show "HML_ready_trace x"
      by (meson conj_flattened.simps(2) mon_conj)
  qed
  with neg_part show ?case using HML_ready_trace.simps
    by fastforce
next
  case (HML_poss \<alpha> \<phi>)
  then show ?case using HML_list.HML_ready_trace.intros(1) by force
qed

lemma expr_1_implies_true: 
  assumes "expr_1 \<phi> = 0" "conj_flattened \<phi>"
  shows "\<phi> = HML_conj [] []"
  using assms
proof(cases \<phi>)
  case (HML_conj x11 x12)
  have e1: "expr_1 (HML_conj x11 x12) =
Max({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
    using expr_1_set_form by simp
  with HML_conj assms(1) have e1_0: "... = 0" by simp
  have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x11} \<union> {expr_1 y | y. y \<in> set x12})"
    by simp
  with e1_0 have fa_le_0:"\<forall>x \<in> set x11. expr_1 x \<le> 0"
    by (metis (mono_tags, lifting) Max_ge UnCI mem_Collect_eq)
  from HML_conj have "\<forall>x \<in> set x11. \<exists>\<alpha> \<psi>. x = HML_poss \<alpha> \<psi>" using conj_flattened_alt
    using assms(2) by blast
  then have "\<forall>x \<in> set x11. expr_1 x \<ge> 1" 
    by fastforce
  with fa_le_0 have "x11 = []" by simp
  from HML_conj have "\<forall>x \<in> set x12. \<exists>\<alpha> \<psi>. x = HML_poss \<alpha> \<psi>" using conj_flattened_alt
    using assms(2) by blast 
  then have fa_ge_1: "\<forall>x \<in> set x12. expr_1 x \<ge> 1" 
    by fastforce
  from fin e1_0 have "\<forall>x \<in> set x12. expr_1 x \<le> 0"
    by (metis (mono_tags, lifting) Max_ge UnCI mem_Collect_eq)
  with fa_ge_1 have "x12 = []" by simp
  with \<open>x11 = []\<close> show ?thesis 
    using HML_conj by blast
next
  case (HML_poss x21 x22)
  then have False
    using assms(1) by force
  then show ?thesis by simp
qed

lemma ready_sim_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)" "conj_flattened \<phi>"
  shows "HML_ready_sim \<phi>"
  using assms
proof induct
  case (HML_conj x1 x2)
  from HML_conj mon_conj have fa_x1: "\<forall>x \<in> set x1. HML_ready_sim x"
    using conj_flattened.simps(2) by blast
  have e5_eq: "expr_5 (HML_conj x1 x2) =
Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    using expr_5_set by simp
  have fin: "finite ({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    by simp
  have subs: "{expr_1 y | y. y \<in> set x2} \<subseteq>
({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
    by auto
  have "\<forall>x \<in> set x2. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])"
  proof
    fix x
    assume "x \<in> set x2"
    with subs fin e5_eq have "expr_5 (HML_conj x1 x2) \<ge> expr_1 x"
      by (metis (mono_tags, lifting) Max_ge UnCI mem_Collect_eq)
    with HML_conj(3) have e1_x: "expr_1 x \<le> 1" using mon_conj
      by (simp add: one_enat_def)
    from \<open>x \<in> set x2\<close>  HML_conj(4) obtain \<alpha> \<psi> where "x = HML_poss \<alpha> \<psi>"
      by (meson conj_flattened_alt)
    with e1_x have "expr_1 \<psi> \<le> 0"
      by simp
    with HML_conj(4) have "\<psi> = HML_conj [] []" using expr_1_implies_true conj_flattened.simps
      using \<open>x = HML_poss \<alpha> \<psi>\<close> \<open>x \<in> set x2\<close> by force
    then show "\<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])" using \<open>x = HML_poss \<alpha> \<psi>\<close> by simp
  qed
  then show "HML_ready_sim (HML_conj x1 x2)"
    using HML_ready_sim.intros(2) fa_x1 by blast
next
  case (HML_poss x1 x2)
  then show ?case
    by (simp add: HML_ready_sim.intros(1))
qed

lemma nested_sim_right:
  assumes "HML_2_nested_sim \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
using assms
proof(induction \<phi> rule: HML_2_nested_sim.induct)
  case (1 \<phi> \<alpha>)
  then show ?case sorry
next
  case (2 xs ys)
  then show ?case sorry
qed

lemma nested_sim_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, \<infinity>, 1)" "conj_flattened \<phi>"
  shows "HML_2_nested_sim \<phi>"
using assms
proof induct
  case (HML_conj x1 x2)
  have "\<forall>x \<in> set x2. HML_simulation x"
  proof
    fix x
    assume "x \<in> set x2"
    have e6_eq: "expr_6 (HML_conj x1 x2) =
Max({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      using expr_6_set by simp
    have fin: "finite({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})"
      by simp
    from \<open>x \<in> set x2\<close> have ne: "({0} \<union> {expr_6 x | x. x \<in> set x1} \<union> {1 + expr_6 y | y. y \<in> set x2})
\<noteq> {}" by simp
    from \<open>x \<in> set x2\<close> e6_eq ne fin have "expr_6 (HML_conj x1 x2) \<ge> 1 + expr_6 x"
      by (metis (mono_tags, lifting) Max_ge UnCI mem_Collect_eq)
    with HML_conj(3) have "expr_6 x \<le> 0"
      by (simp add: one_enat_def)
    then show "HML_simulation x"
    proof induct
      case (HML_conj x12 x22)
      have e6_conj: "expr_6 (HML_conj x12 x22) = 
Max({0} \<union> {expr_6 x | x. x \<in> set x12} \<union> {1 + expr_6 y | y. y \<in> set x22})"
        using expr_6_set by auto
      with HML_conj(3) have fin: "finite({0} \<union> {expr_6 x | x. x \<in> set x12} \<union> {1 + expr_6 y | y. y \<in> set x22})"
        by simp
      with e6_conj HML_conj(3) have "\<forall>y \<in> set x22. (1 + expr_6 y) \<le> 0"
        by (metis HML_subsets.expr_6_conj bot_nat_0.extremum_uniqueI list.set_cases not_one_le_zero)
      then have "x22 = []"
        by auto
      from fin e6_conj HML_conj(3) have "\<forall>x \<in> set x12. expr_6 x \<le> 0"
        by (metis (mono_tags, lifting) Max_ge UnCI bot_nat_0.extremum_uniqueI mem_Collect_eq)
      with HML_conj(1) \<open>x22 = []\<close> show ?case using HML_simulation.intros(2) by blast
    next
      case (HML_poss x1 \<chi>)
      from this(2) have "expr_6 \<chi> \<le> 0" by simp
      with HML_poss(1) have "HML_simulation \<chi>" by simp
      then show ?case using HML_simulation.intros(1) by metis
    qed
  qed
  with HML_conj(1, 3, 4) show "HML_2_nested_sim (HML_conj x1 x2)" 
    using HML_2_nested_sim.intros(2) conj_flattened.simps(2)
    by (metis (no_types, lifting) mon_conj)
next
  case (HML_poss x1 x2)
  then show ?case
    by (simp add: HML_2_nested_sim.intros(1))
qed

end
