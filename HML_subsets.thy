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

lemma expr_nested_empty_pos_conj:
  assumes "nested_empty_pos_conj \<phi>"
  shows "less_eq_t (expr \<phi>) (0, \<infinity>, 0, 0, 0, 0)"
  using assms
proof(induction \<phi> rule: nested_empty_pos_conj.induct)
  case 1
  then show ?case 
    using expr.simps less_eq_t.simps
    by auto
next
  case (2 \<Phi> I \<Psi> J)
  have pos: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
    using 2(1) less_eq_t.simps expr.simps Sup_enat_def
    by (metis SUP_image SUP_least)+
  from this(1) have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using mon_expr_1_pos_r ile0_eq 
    by (metis SUP_image)
  hence "expr_1 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
and"expr_3 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
and "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
and "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
and "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using 2 expr_4_conj prefer 3 apply (simp add: Sup_union_distrib)
    using 2 expr_6_conj expr_5_conj pos expr_4_conj
    by simp+
  thus "less_eq_t (expr (hml_conj I \<Phi> J \<Psi>)) (0, \<infinity>, 0, 0, 0, 0)"
    by (metis enat_ord_code(3) expr.simps less_eq_t.simps)
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
  assume pos_tt_like: "\<forall>x \<in> (\<Phi> ` I). TT_like x" and neg_trace: "\<forall>x\<in>\<Psi> ` J. HML_trace x"
  hence "\<forall>x\<in>\<Psi> ` J. expr_3 x = 0"
and "\<forall>x\<in>\<Psi> ` J. expr_2 x = 1"
    using enat_0_iff(2) trace_right expr_2_lb nle_le 
    by fastforce+
  hence "Sup (expr_3 ` \<Psi> ` J) = 0"
    by (metis SUP_bot_conv(2) bot_enat_def)
  have "Sup (expr_3 ` \<Phi> ` I) \<le> 0" 
and "Sup (expr_1 ` \<Phi> ` I) \<le> 0"
    using pos_tt_like bot_enat_def SUP_least e3_tt expr_3_pos le_numeral_extra(3)
     apply metis
    using pos_tt_like bot_enat_def SUP_least e1_tt expr_1_pos le_numeral_extra(3) 
    by (metis add.commute add_0 eSuc_ile_mono eSuc_plus_1)
  hence e3: "expr_3 (hml_conj I \<Phi> J \<Psi>) = 0"
    using expr_3_conj pos_tt_like \<open>Sup (expr_3 ` \<Psi> ` J) = 0\<close> image_comp
    by (metis Sup_union_distrib bot.extremum_uniqueI bot_enat_def sup.orderE)
  have "Sup (expr_2 ` \<Psi> ` J) \<le> 1"
    using \<open>\<forall>x\<in>\<Psi> ` J. expr_2 x = 1\<close>
    by (simp add: Sup_le_iff)
  have "Sup (expr_2 ` \<Phi> ` I) \<le> 1"
    using pos_tt_like bot_enat_def 
    by (metis SUP_least e2_tt expr_2_pos le_numeral_extra(4)) 
  hence e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using pos_tt_like \<open>Sup (expr_2 ` \<Psi> ` J) \<le> 1\<close> one_add_one expr_2_conj
add_left_mono image_Un image_comp
    by (metis (no_types, lifting) Sup_union_distrib sup.bounded_iff)
  have "\<forall>x\<in>\<Psi> ` J. expr_6 x \<le> 0"
    using enat_0_iff(2) trace_right expr.simps less_eq_t.simps neg_trace
    by auto
  hence "Sup((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff one_eSuc)
  have "\<forall>x \<in> (\<Phi> ` I). expr_6 x \<le> 0"
    using expr_TT pos_tt_like expr.simps
    by fastforce
  hence "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    by (metis SUP_image SUP_least)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using expr_6_conj \<open>Sup((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1\<close> pos_tt_like 
    by (simp add: Sup_union_distrib)
  have "\<forall>x\<in>\<Psi> ` J. expr_4 x \<le> 0" 
    using neg_trace trace_right
    by auto
  hence "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
    using SUP_image SUP_least
    by metis
  have "\<forall>x \<in> (\<Phi> ` I). expr_4 x \<le> 0"
and "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))) \<le> 0"
    using pos_tt_like expr_TT
     apply fastforce
    using \<open>Sup (expr_1 ` \<Phi> ` I) \<le> 0\<close> mon_expr_1_pos_r order_trans 
    by blast
  hence "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))) \<le> 0"
    using SUP_image SUP_least
    by metis+ 
  hence e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using \<open>Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0\<close> expr_4_conj
    by (simp add: Sup_union_distrib sup.orderE)
  from e2 e3 e4 e6 show ?case using expr.simps less_eq_t.simps
    by auto
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
  case (hml_conj x1 x2 x3 x4)
  have "expr_5 (hml_conj x1 x2 x3 x4) = (Sup ((expr_5 \<circ> x2) ` x1 \<union> (expr_5 \<circ> x4) ` x3 \<union> (expr_1 \<circ> x4) ` x3))"
    using expr_5_conj by blast
  hence "1 \<le> (Sup ((expr_5 \<circ> x2) ` x1 \<union> (expr_5 \<circ> x4) ` x3 \<union> (expr_1 \<circ> x4) ` x3))"
    using hml_conj(3) dual_order.trans 
    by simp
  have e6_eq: "expr_6 (hml_conj x1 x2 x3 x4) = (Sup ((expr_6 \<circ> x2) ` x1 \<union> ((eSuc \<circ> expr_6 \<circ> x4) ` x3)))"
    using expr_6_conj
    by force
  have "(x4 ` x3 \<noteq> {}) \<longrightarrow> Sup(((eSuc \<circ> expr_6 \<circ> x4) ` x3)) \<ge> 1"
    using eSuc_def 
    by (metis eSuc_Sup eSuc_ile_mono empty_iff equals0I i0_lb imageI image_comp one_eSuc)
  hence "(x4 ` x3 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3 x4) \<ge> 1)"
    by (meson HML_subsets.expr_6_conj)
  have "(x4 ` x3 = {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3 x4) \<ge> 1)"
  proof
    assume "x4 ` x3 = {}"
    hence "1 \<le> (Sup ((expr_5 \<circ> x2) ` x1))" 
      using \<open>1 \<le> (Sup ((expr_5 \<circ> x2) ` x1 \<union> (expr_5 \<circ> x4) ` x3 \<union> (expr_1 \<circ> x4) ` x3))\<close>
      using bot_enat_def by force
    then obtain x where "x \<in> (x2 ` x1)" "1 \<le> expr_5 x"
      using bot_enat_def comp_apply
      by (metis (no_types, lifting) SUP_bot_conv(2) iless_eSuc0 image_eqI linorder_not_le one_eSuc)
    hence "1 \<le> expr_6 x"
      using hml_conj
      by blast
    hence "Sup ((expr_6 \<circ> x2) ` x1) \<ge> 1"
      using \<open>x \<in> (x2 ` x1)\<close> SUP_image SUP_lessD linorder_not_le 
      by metis
    then show "1 \<le> expr_6 (hml_conj x1 x2 x3 x4)" 
      using expr_6_conj e6_eq
      by (metis Un_empty_right image_is_empty)
  qed
  with \<open>(x4 ` x3 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3 x4) \<ge> 1)\<close> 
  show "1 \<le> expr_6 (hml_conj x1 x2 x3 x4)"
    by blast
qed

lemma expr_2_le_2_is_trace: 
  assumes "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
  shows "\<forall>x \<in> (\<Phi> ` I \<union> \<Psi> ` J). (HML_trace x)"
proof
  fix x
  assume "x \<in> (\<Phi> ` I \<union> \<Psi> ` J)"
  from assms have "\<forall>x \<in> ((expr_2 \<circ> \<Psi>) ` J). x <= 1"
and "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x <= 1"
    using expr_2_conj
    using Sup_union_distrib Sup_upper dual_order.order_iff_strict one_eSuc plus_1_eSuc(1) one_add_one
    by (smt (verit) eSuc_ile_mono le_sup_iff order_trans)+
  hence e2: "expr_2 x \<le> 1"
    using \<open>x \<in> (\<Phi> ` I \<union> \<Psi> ` J)\<close>
    by fastforce
  show " HML_trace x"
    using e2
  proof(induction x)
    case TT
    then show ?case 
      using HML_trace.simps
      by blast
  next
    case (hml_pos x21 x22)
    then show ?case 
      using HML_trace.simps
      by fastforce 
  next
    case (hml_conj x31 x32 x33 x34)
    from \<open>expr_2 (hml_conj x31 x32 x33 x34) \<le> 1\<close> expr_2_le_1
    show ?case using HML_trace.simps
      by blast
  qed
qed

lemma impossible_futures_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  shows "HML_impossible_futures \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using if_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case
    by (simp add: if_pos)
next
  case (hml_conj I \<Phi> J \<Psi>)
  have "\<forall>x \<in> (\<Psi> ` J). (HML_trace x)"
    using expr_2_le_2_is_trace expr.simps hml_conj.prems less_eq_t.simps
    by (metis Un_iff)
  from hml_conj have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Psi>) ` J) \<le> 2"
    using expr.simps less_eq_t.simps expr_2_conj 
    by metis
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1"
    using one_add_one
    by (metis Sup_union_distrib enat_add_left_cancel_le i1_ne_infinity le_sup_iff)
  have "\<forall>x \<in> \<Phi> ` I. TT_like x"
  proof
    fix x
    assume "x \<in> \<Phi> ` I"
    show "TT_like x"
    proof(cases x)
      case TT
      then show ?thesis 
        using TT_like.simps 
        by blast
    next
      case (hml_pos x21 x22)
      hence "expr_1 x \<ge> 1"
        by simp
      hence "Sup ((expr_1 \<circ> \<Phi>) ` I) \<ge> 1"
        by (metis SUP_image SUP_lessD \<open>x \<in> \<Phi> ` I\<close> linorder_not_le)
      hence "expr_3 (hml_conj I \<Phi> J \<Psi>) \<ge> 1"
        using expr_3_conj 
        by (metis Sup_union_distrib bot_enat_def iless_eSuc0 linorder_not_le one_eSuc sup_eq_bot_iff)
      with hml_conj(3) have False
        by auto
      then show ?thesis by blast
    next
      case (hml_conj x31 x32 x33 x34)
      have "\<forall>x \<in> (x32 ` x31 \<union> x34 ` x33). expr_2 x \<ge> 1"
        using expr_2_lb
        by blast
      hence "(x32 ` x31 \<union> x34 ` x33) \<noteq> {} \<longrightarrow> expr_2 x \<ge> 2"
        using hml_conj expr_2_lb expr_2_le_1
        by (metis dual_order.order_iff_strict ileI1 one_add_one plus_1_eSuc(1) sup_eq_bot_iff) 
      hence "(x32 ` x31 \<union> x34 ` x33) \<noteq> {} \<longrightarrow> Sup ((expr_2 \<circ> \<Phi>) ` I) \<ge> 2"
        using SUP_image SUP_lessD \<open>x \<in> \<Phi> ` I\<close> linorder_not_le
        by metis
      hence "(x32 ` x31 \<union> x34 ` x33) \<noteq> {} \<longrightarrow> expr_2 (hml_conj I \<Phi> J \<Psi>) \<ge> 3"
        using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close>
        by (metis  dual_order.trans numeral_le_one_iff semiring_norm(69))
      hence "(x32 ` x31 \<union> x34 ` x33) \<noteq> {} \<longrightarrow> False" 
        using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> 
\<open>x32 ` x31 \<union> x34 ` x33 \<noteq> {} \<longrightarrow> 2 \<le> Sup ((expr_2 \<circ> \<Phi>) ` I)\<close>
        by (meson  numeral_le_one_iff order_trans semiring_norm(69))
      hence "x32 ` x31 = {}" "x34 ` x33 = {}"
        by blast+
      then show ?thesis
        by (simp add: TT_like.intros(2) hml_conj)
    qed
  qed
  then show ?case using \<open>\<forall>x \<in> (\<Psi> ` J). (HML_trace x)\<close>
    by (simp add: if_conj)
qed

lemma impossible_futures_lemma:
  shows "HML_impossible_futures \<phi> = less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  using impossible_futures_left impossible_futures_right by blast

lemma expr_4_ft_poss:
  fixes \<phi> and \<alpha>
  assumes A1: "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  shows "expr_4 (hml_pos \<alpha> \<phi>) \<le> 0"
proof-
  from assms have "expr_4 \<phi> \<le> 0"
    using expr.simps less_eq_t.simps
    by simp
  then show ?thesis
  using expr_4_pos
  by auto
qed

lemma possible_futures_right:
  assumes "HML_possible_futures \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  using assms
proof(induction \<phi> rule: HML_possible_futures.induct)
  case pf_tt
  then show ?case
    by simp
next
  case (pf_pos \<phi> \<alpha>)
  then show ?case 
    by simp 
next
  case (pf_conj \<Phi> I \<Psi> J)
  hence fa_le: "\<forall>x\<in>\<Phi> ` I \<union> \<Psi> ` J. less_eq_t (expr x) (\<infinity>, 1, 0, 0, 0, 0)"
    using trace_right 
    by blast
  hence "\<forall>x \<in> \<Phi> ` I \<union> \<Psi> ` J. expr_6 x <= 0"
and "\<forall>x \<in> \<Phi> ` I \<union> \<Psi> ` J. expr_2 x \<le> 1"
    using expr.simps less_eq_t.simps
    by auto
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1" and
"Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> 1"
    using SUP_image SUP_least
    by (metis UnCI)+
  hence e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using expr_2_conj one_add_one
    by (metis Sup_union_distrib add_mono_thms_linordered_semiring(2) sup.bounded_iff)
  have "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using \<open>\<forall>x \<in> \<Phi> ` I \<union> \<Psi> ` J. expr_6 x <= 0\<close> SUP_image SUP_least
    by (metis Un_iff)+
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using eSuc_def 
    by (metis (no_types, opaque_lifting) SUP_image eSuc_Sup image_empty le_zero_eq nle_le one_eSuc)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> Sup_union_distrib expr_6.expr_6_conj
    by (smt (verit) le_sup_iff le_zero_eq linordered_nonzero_semiring_class.zero_le_one)
  then show ?case using e2
    by auto
qed

lemma possible_futures_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  shows "HML_possible_futures \<phi>"
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
  case (hml_conj I \<Phi> J \<Psi>)
  hence "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using expr.simps less_eq_t.simps
    by metis
  then show ?case using expr_2_le_2_is_trace
    by (metis pf_conj)
qed

lemma possible_futures_lemma:
  shows "HML_possible_futures \<phi> = less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1)"
  using possible_futures_right possible_futures_left by blast

(*
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
*)

lemma pos_r_bounded: 
  assumes "xa \<in> I" and "\<forall>y\<in>\<Phi> ` I. \<Phi> xa \<noteq> y \<longrightarrow> expr_1 y \<le> z"
  shows "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> z"
proof(cases "\<forall>x \<in> (\<Phi> ` I) - {\<Phi> xa}. expr_1 x < expr_1 (\<Phi> xa)")
  case True
  then have "(pos_r (\<Phi> ` I)) = (\<Phi> ` I) - {\<Phi> xa}"
    using pos_r_del_max assms(1) Un_insert_right image_insert
    by (metis (no_types, opaque_lifting)  insert_Diff_single insert_absorb sup_bot_right)
  have "\<forall>y \<in> (\<Phi> ` I) - {\<Phi> xa}. expr_1 y \<le> z"
    using assms(2) expr_TT expr.simps
    by fastforce
  hence "Sup (expr_1 ` ((\<Phi> ` I) - {\<Phi> xa})) \<le> z"
    by (metis SUP_least)
  then show ?thesis using \<open>(pos_r (\<Phi> ` I)) = (\<Phi> ` I) - {\<Phi> xa}\<close>
    by presburger
next
  case False
  then obtain x where "x \<in> \<Phi> ` I - {\<Phi> xa}" "expr_1 x \<ge> expr_1 (\<Phi> xa)"
    using linorder_not_le by blast
  from assms have "expr_1 x \<le> z" 
    using \<open>x \<in> \<Phi> ` I - {\<Phi> xa}\<close>
    by (metis Diff_iff  insertCI)
  hence "expr_1 (\<Phi> xa) \<le> z" using \<open>expr_1 x \<ge> expr_1 (\<Phi> xa)\<close>
    by force
  hence "\<forall>x \<in> (\<Phi> ` I). expr_1 x \<le> z"
    using \<open>x \<in> \<Phi> ` I - {\<Phi> xa}\<close> \<open>expr_1 x <= z\<close> assms(2)
    by metis
  hence "Sup (expr_1 ` \<Phi> ` I) \<le> z"
    by (meson SUP_least)
  then show ?thesis
    using mon_expr_1_pos_r order.trans by blast
qed

lemma failure_trace_right:
  assumes "(HML_failure_trace \<phi>)"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  using assms
proof(induction \<phi>)
  case f_trace_tt
  then show ?case by simp
next
  case (f_trace_pos \<phi> \<alpha>)
  then show ?case 
    by simp
next
  case (f_trace_conj \<Phi> I \<Psi> J)
  then show ?case
  proof(safe)
  assume " \<forall>y\<in>\<Phi> ` I. nested_empty_pos_conj y" 
and "\<forall>y\<in>\<Psi> ` J. nested_empty_pos_conj y \<or> (\<exists>\<alpha> \<chi>. y = hml_pos \<alpha> \<chi> \<and> nested_empty_pos_conj \<chi>)"
  hence fa_pos: "\<forall>y\<in>\<Phi> ` I. expr_1 y = 0"
 "\<forall>y\<in>\<Phi> ` I. expr_2 y \<le> \<infinity>"
 "\<forall>y\<in>\<Phi> ` I. expr_3 y = 0"
 "\<forall>y\<in>\<Phi> ` I. expr_4 y = 0"
 "\<forall>y\<in>\<Phi> ` I. expr_5 y = 0"
 "\<forall>y\<in>\<Phi> ` I. expr_6 y = 0"
    using expr_nested_empty_pos_conj expr.simps
    by auto
  hence "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> \<infinity>"
and "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
         prefer 2 apply (simp add: SUP_least)
    using fa_pos
    by (metis SUP_image SUP_least le_zero_eq)+
  have fa_neg: "\<forall>y\<in>\<Psi> ` J. expr_1 y \<le> 1" 
 "\<forall>y\<in>\<Psi> ` J. expr_2 y \<le> \<infinity>" 
 "\<forall>y\<in>\<Psi> ` J. expr_3 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_4 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_5 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_6 y \<le> 0" 
    using expr_nested_empty_pos_conj expr.simps 
\<open>\<forall>y\<in>\<Psi> ` J. nested_empty_pos_conj y \<or> (\<exists>\<alpha> \<chi>. y = hml_pos \<alpha> \<chi> \<and> nested_empty_pos_conj \<chi>)\<close>
    by fastforce+
  hence "Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1"
and "Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> \<infinity>"
and "Sup ((expr_3 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
         apply (simp add: SUP_least)
    using fa_neg apply (simp add: SUP_least)
    using fa_neg
    by (metis SUP_image SUP_least)+

  
  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0\<close> sorry
    by (metis SUP_image le_zero_eq mon_expr_1_pos_r)
  hence e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using \<open>Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_4_conj
    by (simp add: Sup_union_distrib)
  have "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0\<close> eSuc_def  SUP_image
    by (metis (no_types, opaque_lifting) dual_order.refl eSuc_Sup i0_lb image_empty le_zero_eq one_eSuc)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> Sup_union_distrib expr_6.expr_6_conj 
    by (smt (verit, best) ile0_eq le_sup_iff linordered_nonzero_semiring_class.zero_le_one)
  have e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1\<close> \<open>Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0\<close>
expr_5_conj 
    by (simp add: Sup_union_distrib complete_linorder_sup_max max_def)
  show ?case using e4 e5 e6 expr.simps less_eq_t.simps
    by fastforce
next
  fix x xa
  assume "xa \<in> I"
and "\<forall>y\<in>\<Psi> ` J. nested_empty_pos_conj y \<or> (\<exists>\<alpha> \<chi>. y = hml_pos \<alpha> \<chi> \<and> nested_empty_pos_conj \<chi>)"
and "\<forall>y\<in>\<Phi> ` I. \<Phi> xa \<noteq> y \<longrightarrow> nested_empty_pos_conj y"
and "HML_failure_trace (\<Phi> xa)"
and "less_eq_t (expr (\<Phi> xa)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"

  have fa_pos: "\<forall>x \<in> \<Phi> ` I. expr_4 x \<le> 0"
 "\<forall>x \<in> \<Phi> ` I. expr_5 x \<le> 1"
 "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 1"
    using \<open>xa \<in> I\<close> \<open>\<forall>y\<in>\<Phi> ` I. \<Phi> xa \<noteq> y \<longrightarrow> nested_empty_pos_conj y\<close> \<open>less_eq_t (expr (\<Phi> xa)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)\<close>
expr_nested_empty_pos_conj expr.simps
    by force+

  hence "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
    by (metis SUP_image SUP_least)+

  have "\<forall>y\<in>\<Phi> ` I. \<Phi> xa \<noteq> y \<longrightarrow> expr_1 y \<le> 0"
    using expr_nested_empty_pos_conj expr.simps \<open>\<forall>y\<in>\<Phi> ` I. \<Phi> xa \<noteq> y \<longrightarrow> nested_empty_pos_conj y\<close>
    by fastforce
  hence "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using \<open>xa \<in> I\<close> pos_r_bounded
    by metis

have fa_neg: "\<forall>y\<in>\<Psi> ` J. expr_1 y \<le> 1" 
 "\<forall>y\<in>\<Psi> ` J. expr_2 y \<le> \<infinity>" 
 "\<forall>y\<in>\<Psi> ` J. expr_3 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_4 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_5 y \<le> 0" 
 "\<forall>y\<in>\<Psi> ` J. expr_6 y \<le> 0" 
  using expr_nested_empty_pos_conj expr.simps 
\<open>\<forall>y\<in>\<Psi> ` J. nested_empty_pos_conj y \<or> (\<exists>\<alpha> \<chi>. y = hml_pos \<alpha> \<chi> \<and> nested_empty_pos_conj \<chi>)\<close>
    by fastforce+
  hence "Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1"
and "Sup ((expr_2 \<circ> \<Psi>) ` J) \<le> \<infinity>"
and "Sup ((expr_3 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
         apply (simp add: SUP_least)
    using fa_neg apply (simp add: SUP_least)
    using fa_neg
    by (metis SUP_image SUP_least le_zero_eq)+

  have e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using \<open>Sup ((expr_4 \<circ> \<Psi>) ` J) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_4_conj 
\<open>Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0\<close>
    by (simp add: Sup_union_distrib)
have e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1\<close> \<open>Sup ((expr_5 \<circ> \<Psi>) ` J) \<le> 0\<close>
expr_5_conj 
    by (simp add: Sup_union_distrib complete_linorder_sup_max max_def)
have "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0\<close> eSuc_def  SUP_image
    by (metis (no_types, opaque_lifting) dual_order.refl eSuc_Sup i0_lb image_empty le_zero_eq one_eSuc)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1\<close> Sup_union_distrib expr_6.expr_6_conj
    by (simp add: Sup_union_distrib complete_linorder_sup_max max_def)
  show ?case using e4 e5 e6 expr.simps less_eq_t.simps
    by fastforce
qed
qed

(*
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
*)

(*

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
*)
  oops

lemma expr_1_expr_6_le_0_is_nested_empty_pos_conj:
  assumes "expr_1 \<phi> \<le> 0" "expr_6 \<phi> \<le> 0"
  shows "nested_empty_pos_conj \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case using nested_empty_pos_conj.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  from this(2) have False 
    by simp
  then show ?case by blast
next
  case (hml_conj x1 x2 x3 x4)
  hence "x4` x3 = {}"
    by (metis HML_subsets.expr_6_conj ile0_eq not_one_le_zero)
  have sup_le: "Sup ((expr_1 \<circ> x2) ` x1) \<le> 0"
"Sup ((expr_1 \<circ> x4) ` x3) \<le> 0"
"Sup ((expr_6 \<circ> x2) ` x1) \<le> 0" 
"Sup ((eSuc \<circ> expr_6 \<circ> x4) ` x3) \<le> 0" 
    using expr_1_conj expr_6.expr_6_conj hml_conj(3, 4)
    by (metis Sup_union_distrib le_sup_iff)+
  hence "Sup ((expr_6 \<circ> x4) ` x3) \<le> 0" 
    using eSuc_def 
    by (metis HML_subsets.expr_6_conj SUP_image hml_conj.prems(2) image_empty le_zero_eq not_one_le_zero)
  hence "\<forall>x \<in> x2 ` x1. expr_1 x \<le> 0 \<and> expr_6 x \<le> 0"
"\<forall>x \<in> x4 ` x3. expr_1 x \<le> 0 \<and> expr_6 x \<le> 0"
    using sup_le
    by (metis SUP_image SUP_upper le_zero_eq)+
  hence "\<forall>x \<in> x2 ` x1. nested_empty_pos_conj x"
"\<forall>x \<in> x4 ` x3. nested_empty_pos_conj x"
    using hml_conj(1, 2)
    by blast+
  then show ?case using \<open>x4` x3 = {}\<close>
    by (simp add: nested_empty_pos_conj.intros(2))
qed

lemma expr_5_restict_negations: 
  assumes "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1" "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1" 
  shows "(\<forall>y \<in> (\<Psi> ` J). stacked_pos_conj_pos y)"
proof                                
  fix y 
  assume "y \<in>\<Psi> ` J"
  from assms have "Sup ((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
"Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1"
    by (simp add: Sup_union_distrib)+
  hence "Sup ((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
    using eSuc_def
    by (metis Sup_enat_def eSuc_Sup eSuc_ile_mono image_comp le_zero_eq one_eSuc)
  hence "expr_6 y \<le> 0"
"expr_1 y \<le> 1"
    using \<open>y \<in> \<Psi> ` J\<close> Sup_le_iff \<open>Sup ((expr_1 \<circ> \<Psi>) ` J) \<le> 1\<close>
    by (metis comp_apply image_iff)+
  then show "stacked_pos_conj_pos y"
  proof(induction y)
    case TT
    then show ?case
      using stacked_pos_conj_pos.intros(1) by blast
  next
    case (hml_pos \<alpha> \<psi>)
    from this(2, 3) have "expr_1 \<psi> \<le> 0"
"expr_6 \<psi> \<le> 0"
      using expr_1.simps
      by simp+
    hence "nested_empty_pos_conj \<psi>"
      using expr_1_expr_6_le_0_is_nested_empty_pos_conj
      by blast
    then show ?case 
      by (simp add: stacked_pos_conj_pos.intros(2))
  next
    case (hml_conj x31 x32 x33 x34)
    have "(Sup ((expr_1 \<circ> x32) ` x31) \<le> 1)"
"(Sup ((expr_6 \<circ> x32) ` x31) \<le> 0)"
      using hml_conj(3, 4) Sup_union_distrib expr_1_conj expr_6.expr_6_conj
      by (metis le_supE)+
    hence "\<forall>x \<in> (x32 ` x31). expr_1 x \<le> 1 \<and> expr_6 x \<le> 0"
      by (metis SUP_image SUP_upper dual_order.trans)
    hence "\<forall>x \<in> (x32 ` x31). stacked_pos_conj_pos x"
      using hml_conj(1) 
      by blast
    from hml_conj(3) have "x34 ` x33 = {}"
      using expr_6_conj eSuc_def
      by (metis not_one_le_zero order.trans)
    then show ?case 
      using \<open>\<forall>x \<in> (x32 ` x31). stacked_pos_conj_pos x\<close> stacked_pos_conj_pos.simps 
      by fastforce
  qed
qed


lemma
  assumes "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0" "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
"\<forall>x \<in> (\<Phi> ` I). HML_failure_trace x"
  shows "((\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_pos_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_pos_conj y))"
proof(cases "(\<exists>\<psi> \<in> (\<Phi> ` I). expr_1 \<psi> \<ge> 1)")
  case True
  then obtain \<psi> where "\<psi> \<in> \<Phi> ` I" "expr_1 \<psi> \<ge> 1"
    by blast
  with assms(1) have "HML_failure_trace \<psi>"
    using assms(3) by blast 
  from assms(2) have "(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 0)"
    using expr_6.expr_6_conj 
    by (smt (verit, ccfv_threshold) Sup_le_iff Un_iff comp_apply image_iff)
  have "(\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> expr_1 y \<le> 0)"
  proof(rule+)
    fix y
    assume "y \<in> \<Phi> ` I" "\<psi> \<noteq> y"
    show "expr_1 y \<le> 0"
    proof(rule ccontr, simp)
      assume "expr_1 y \<noteq> 0"
      then have "expr_1 y \<ge> 1"
        using iless_eSuc0 one_eSuc 
        by fastforce
      hence "(Sup (expr_1 ` (\<Phi> ` I))) \<ge> 1"
        using \<open>y \<in> \<Phi> ` I\<close>
        by (meson Sup_upper2 imageI)
      define max_elem where "max_elem \<equiv> (SOME \<psi>. \<psi> \<in> (\<Phi> ` I) \<and> expr_1 \<psi> = (Sup (expr_1 ` (\<Phi> ` I))))"
      from \<open>expr_1 y \<ge> 1\<close> \<open>expr_1 \<psi> \<ge> 1\<close> \<open>\<psi> \<in> \<Phi> ` I\<close> \<open>y \<in> \<Phi> ` I\<close> have
"Sup (expr_1 ` ((\<Phi> ` I) - {max_elem})) >= 1"
        unfolding max_elem_def 
        by (smt (verit) DiffI SUP_upper2 \<open>\<psi> \<noteq> y\<close> emptyE insertE)
      hence "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<ge> 1"
        using pos_r.simps
        unfolding max_elem_def 
        by metis
      hence "expr_4 (hml_conj I \<Phi> J \<Psi>) \<ge> 1"
        using Sup_union_distrib assms(1) bot_enat_def expr_4_conj
        by (metis  ile0_eq sup_bot.neutr_eq_iff)
      then show False 
        using assms(2) assms(1) not_one_le_zero order_trans by blast
    qed
  qed
  hence "(\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_pos_conj y)"
    using \<open>(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 0)\<close> expr_1_expr_6_le_0_is_nested_empty_pos_conj
    by blast
  with \<open>HML_failure_trace \<psi>\<close> \<open>\<psi> \<in> \<Phi> ` I\<close> show ?thesis 
    by blast
next
  assume "\<not> (\<exists>\<psi>\<in>\<Phi> ` I. 1 \<le> expr_1 \<psi>)"
  hence "\<forall>\<psi>\<in>\<Phi> ` I. expr_1 \<psi> \<le> 0"
    
    by (simp add: linorder_not_le one_eSuc)
      from assms(2) have "(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 0)"
    using expr_6.expr_6_conj 
    by (smt (verit, ccfv_threshold) Sup_le_iff Un_iff comp_apply image_iff)
  hence "(\<forall>y \<in> (\<Phi> ` I). nested_empty_pos_conj y)"
    using \<open>(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 0)\<close> expr_1_expr_6_le_0_is_nested_empty_pos_conj \<open>\<forall>\<psi>\<in>\<Phi> ` I. expr_1 \<psi> \<le> 0\<close>
    by blast
  then show ?thesis by blast
qed

lemma failure_trace_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  shows "(HML_failure_trace \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using f_trace_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case
    by (simp add: f_trace_pos)
next
  case (hml_conj I \<Phi> J \<Psi>)
  have fa: "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0" "Sup((expr_4 \<circ> \<Psi>) ` J) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1" "Sup((expr_5 \<circ> \<Psi>) ` J) \<le> 1" "Sup((expr_1 \<circ> \<Psi>) ` J) \<le> 1"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1" "Sup((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    using hml_conj(3) Sup_union_distrib expr.simps
          apply (smt (verit, del_insts) expr_4_conj le_sup_iff le_zero_eq less_eq_t.simps)
    using hml_conj(3) expr.simps Sup_union_distrib expr_5.simps(3) expr_6.simps(3) expr_4.simps
    by (metis le_sup_iff less_eq_t.simps)+

  hence "Sup((expr_6 \<circ> \<Psi>) ` J) \<le> 1"
    by (metis (no_types, lifting) SUP_image Sup_bot_conv(2) bot.extremum_uniqueI 
dual_order.strict_trans eSuc_Sup empty_iff ile_eSuc leD leI order.strict_trans2)
  hence "\<forall>x \<in> (\<Phi> ` I). HML_failure_trace x"
"\<forall>x \<in> (\<Psi> ` J). HML_failure_trace x"
    using hml_conj fa
    by (metis (no_types, opaque_lifting) image_iff mon_conj rangeI)+
    
  hence "((\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_pos_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_pos_conj y))"
  proof-
  hence "(\<forall>y \<in> (\<Psi> ` J). nested_empty_pos_conj y \<or> (\<exists>\<alpha> \<chi>. (y = hml_pos \<alpha> \<chi>) \<and> nested_empty_pos_conj \<chi>))"
  proof-
    using expr_5
  then show ?case sorry
qed
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
