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
  assumes A1: "HML_failure \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using A1
proof(induction \<phi> rule:HML_failure.induct)
  case failure_tt
  then show ?case by force
next
  case (failure_pos \<phi> \<alpha>)
  then show ?case by force
next
  case (failure_conj \<Phi> I J \<Psi>)
  hence e2_eq: "expr_2 (hml_conj I \<Phi> J \<Psi>) = 1 + Sup ((expr_2 \<circ> \<Psi>) ` J)"
and e3_eq: "expr_3 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_3 \<circ> \<Psi>) ` J))"
and e4_eq: "expr_4 (hml_conj I \<Phi> J \<Psi>) = Sup ((expr_4 \<circ> \<Psi>) ` J)"
and e5_eq: "expr_5 (hml_conj I \<Phi> J \<Psi>) = (Sup ((expr_5 \<circ> \<Psi>) ` J \<union> (expr_1 \<circ> \<Psi>) ` J))"
and e6_eq: "expr_6 (hml_conj I \<Phi> J \<Psi>) = (Sup (((eSuc \<circ> expr_6 \<circ> \<Psi>) ` J)))"
    by simp+

  have e2_tt: "\<forall>\<alpha>. expr_2 (hml_pos \<alpha> TT) = 1"
and e3_tt: "\<forall>\<alpha>. expr_3 (hml_pos \<alpha> TT) = 0"
and e4_tt: "\<forall>\<alpha>. expr_4 (hml_pos \<alpha> TT) = 0"
and e5_tt: "\<forall>\<alpha>. expr_5 (hml_pos \<alpha> TT) = 0"
and e6_tt: "\<forall>\<alpha>. expr_6 (hml_pos \<alpha> TT) = 0"
    by simp+

  have e2_tt_2: "\<forall>\<alpha> K \<chi>s L n\<chi>s. (\<chi>s ` K = {} \<and> n\<chi>s ` L = {}) \<longrightarrow> expr_2 (hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s)) = 1"
and e3_tt_2: "\<forall>\<alpha> K \<chi>s L n\<chi>s. (\<chi>s ` K = {} \<and> n\<chi>s ` L = {}) \<longrightarrow> expr_3 (hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s)) = 0"
and e4_tt_2: "\<forall>\<alpha> K \<chi>s L n\<chi>s. (\<chi>s ` K = {} \<and> n\<chi>s ` L = {}) \<longrightarrow> expr_4 (hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s)) = 0"
and e5_tt_2: "\<forall>\<alpha> K \<chi>s L n\<chi>s. (\<chi>s ` K = {} \<and> n\<chi>s ` L = {}) \<longrightarrow> expr_5 (hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s)) = 0"
and e6_tt_2: "\<forall>\<alpha> K \<chi>s L n\<chi>s. (\<chi>s ` K = {} \<and> n\<chi>s ` L = {}) \<longrightarrow> expr_6 (hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s)) = 0"
    by (simp add: bot_enat_def)+

  from e2_eq e2_tt e2_tt_2 have e2: "expr_2 (hml_conj I \<Phi> J \<Psi>) \<le> 2"
    using Sup_le_iff local.failure_conj one_add_one 
    by (smt (verit) add_left_mono image_iff linorder_not_le o_apply order_less_imp_le)
  from e3_eq e3_tt e3_tt_2 have e3: "expr_3 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using Sup_le_iff local.failure_conj
    by (smt (verit, ccfv_SIG) SUP_bot_conv(2) bot_enat_def comp_apply le_zero_eq)
  from e4_eq e4_tt e4_tt_2 have e4: "expr_4 (hml_conj I \<Phi> J \<Psi>) \<le> 0"
    using Sup_le_iff local.failure_conj
    by (smt (verit) SUP_bot_conv(2) bot_enat_def comp_apply le_zero_eq)
  from e5_eq e5_tt e5_tt_2 have e5: "expr_5 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using Sup_le_iff local.failure_conj by fastforce
  from e6_eq e6_tt e6_tt_2 have "Sup((expr_6 \<circ> \<Psi>) ` J) \<le> 0"
    using Sup_le_iff local.failure_conj
    by (smt (verit, best) comp_apply image_iff le_zero_eq)
  hence e6: "expr_6 (hml_conj I \<Phi> J \<Psi>) \<le> 1"
    using eSuc_def e6_eq
    by (metis eSuc_Sup image_comp image_is_empty le_zero_eq nle_le one_eSuc)
  from e2 e3 e4 e5 e6 show ?case
    using less_eq_t.simps expr.simps 
    by fastforce
qed

fun conj_flattened :: "'a formula_list \<Rightarrow> bool"
  where
"conj_flattened (HML_poss \<alpha> \<psi>) = conj_flattened \<psi>" |
"conj_flattened (HML_conj x1 x2) = 
((\<forall>x \<in> set x1. (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x2. (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x))"

find_theorems conj_flattened

lemma conj_flattened_alt: "conj_flattened (HML_conj x1 x2) =
((\<forall>x \<in> set x1. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x2. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x))"
proof(induction x1)
  case Nil
  then show ?case 
    proof(induction x2)
      case Nil
      then show ?case by simp
    next
      case (Cons a x2)
      have A1: "conj_flattened (HML_conj [] (a # x2)) = 
((\<forall>x \<in> set []. (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set (a#x2). (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x))" 
        by simp
      have A2: "((\<forall>x \<in> set []. (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set (a#x2). (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x)) = 
(((\<nexists>x21 x22. a = HML_conj x21 x22) \<and> conj_flattened a) \<and> 
(\<forall>x \<in> set x2. (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x))"
        using local.Cons by auto
      show ?case
        by (metis (no_types, opaque_lifting) A1 conj_flattened.elims(1) formula_list.distinct(1))
    qed
next
  case (Cons a x1)
  have "conj_flattened (HML_conj (a # x1) x2) =
((\<forall>x \<in> set (a#x1). (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x2. (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x))" 
    by simp
  also have "... = 
(((\<nexists>x11 x12. a = HML_conj x11 x12) \<and> conj_flattened a) \<and> (\<forall>x \<in> set x1. (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x2. (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x))" 
    by simp
  also have "... = 
(((\<nexists>x11 x12. a = HML_conj x11 x12) \<and> conj_flattened a) \<and> 
((\<forall>x \<in> set x1. (\<nexists>x11 x12. x = HML_conj x11 x12) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x2. (\<nexists>x21 x22. x = HML_conj x21 x22) \<and> conj_flattened x)))"
    by simp
  also have "... = 
(((\<nexists>x11 x12. a = HML_conj x11 x12) \<and> conj_flattened a) \<and> 
conj_flattened (HML_conj x1 x2))" 
    by simp

  have conj_form: "conj_flattened (HML_conj (a#x1) x2) =
(((\<nexists>x11 x12. a = HML_conj x11 x12) \<and> conj_flattened a) \<and> 
conj_flattened (HML_conj x1 x2))" 
    by simp
  have "(\<nexists>x11 x12. a = HML_conj x11 x12) = (\<exists>\<alpha> \<phi>. a = HML_poss \<alpha> \<phi>)"
    by (metis expr_4.cases formula_list.distinct(1))
  from this conj_form have conj_form: "conj_flattened (HML_conj (a#x1) x2) =
(((\<exists>\<alpha> \<phi>. a = HML_poss \<alpha> \<phi>) \<and> conj_flattened a) \<and> 
conj_flattened (HML_conj x1 x2))" 
    by simp
  then have "conj_flattened (HML_conj (a#x1) x2) =
(((\<exists>\<alpha> \<phi>. a = HML_poss \<alpha> \<phi>) \<and> conj_flattened a) \<and>
((\<forall>x\<in>set x1. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x) \<and>
        (\<forall>x\<in>set x2. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x)))"
    using local.Cons by presburger
  then show ?case by simp
qed

fun flatten_\<phi> ::"'a formula_list \<Rightarrow> 'a formula_list" and
  flatten_\<phi>_conj :: "'a formula_list \<Rightarrow> (('a formula_list list) \<times> ('a formula_list list))" where
"flatten_\<phi> (HML_poss \<alpha> \<psi>) = (HML_poss \<alpha> (flatten_\<phi> \<psi>))" |
"flatten_\<phi> (HML_conj x1 x2) = (
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

context lts
begin

(*TODO*)
lemma flatten_\<phi>_flattens:
  shows "conj_flattened (flatten_\<phi> \<phi>)"
  using conj_flattened.simps flatten_\<phi>.simps
  oops

lemma flattened_equivalent:
  shows "(p \<Turnstile> \<phi>) = (p \<Turnstile> (flatten_\<phi> \<phi>))"
proof
  oops

end

lemma failure_x1_empty:
  fixes x1 x2
  assumes A1: "conj_flattened (HML_conj x1 x2)" and A2: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, 2, 0, 0, 1, 1)"
shows "x1 = []"
proof(rule ccontr)
  assume A3: "x1 \<noteq> []"
  then obtain x where "x \<in> set x1"
    using ex_in_conv 
    by fastforce    
  hence "\<exists>\<alpha> \<psi>. x = HML_poss \<alpha> \<psi>"
    using assms(1) conj_flattened_alt
    by blast
  hence "expr_1 x \<ge> 1"
    using expr_1.simps
    by force
  have subs: "(expr_1 ` (set x1)) \<subseteq> ((expr_1 ` (set x1)) \<union> (expr_3 ` (set x1)) \<union> (expr_3 ` (set x2)))"
    by blast
  from A2 have e3_eq_0: "expr_3 (HML_conj x1 x2) \<le> 0"
    using expr.simps less_eq_t.simps
    by metis
  hence "(Sup ((expr_1 ` (set x1)) \<union> (expr_3 ` (set x1)) \<union> (expr_3 ` (set x2)))) \<le> 0"
    using expr_1.simps 
    by simp
  hence "Sup (expr_1 ` (set x1)) \<le> 0"
    using Sup_enat_def Sup_subset_mono subs
    by (metis le_zero_eq)
  from \<open>x \<in> set x1\<close> \<open>expr_1 x \<ge> 1\<close> have "Sup (expr_1 ` (set x1)) \<ge> 1"
    using Sup_enat_def
    by (metis Sup_upper2 imageI)
  with \<open>Sup (expr_1 ` (set x1)) \<le> 0\<close> show False by simp
qed

lemma failure_left:
  fixes \<phi>
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))" and "conj_flattened \<phi>"
  shows "HML_failure \<phi>"
  using assms
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from assms(2) have x1_e: "x1 = []"
    using HML_conj(3) HML_conj.prems(2) failure_x1_empty 
    by blast
  have "\<forall>y \<in> (set x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  proof
    fix y
    assume "y \<in> set x2"
    with HML_conj(4) have "conj_flattened y" 
      using conj_flattened.simps
      by blast
    then obtain \<alpha> \<psi> where "y = HML_poss \<alpha> \<psi>"
      using conj_flattened_alt
      by (metis HML_conj.prems(2) \<open>y \<in> set x2\<close>)
    have e5_eq: "expr_5 (HML_conj x1 x2) = (Sup ((expr_5 ` (set x1)) \<union> (expr_5 ` (set x2)) \<union> (expr_1 ` (set x2))))"
      using expr_5.simps
      by blast
    hence "(Sup ((expr_5 ` (set x1)) \<union> (expr_5 ` (set x2)) \<union> (expr_1 ` (set x2)))) \<le> 1"
      using HML_conj(3) less_eq_t.simps expr.simps
      by fastforce
    hence "expr_1 y \<le> 1"
      using Sup_enat_def \<open>y \<in> set x2\<close>
      by (meson Sup_le_iff UnCI image_eqI)
    hence "expr_1 \<psi> \<le> 0"
      using expr_1.simps \<open>y = HML_poss \<alpha> \<psi>\<close>
      by simp
    have "conj_flattened \<psi>"
      using \<open>conj_flattened y\<close> \<open>y = HML_poss \<alpha> \<psi>\<close> conj_flattened.simps(1)
      by simp
    hence "\<psi> = HML_conj [] []" 
    proof(cases \<psi>)
      case (HML_conj x11 x12)
      hence "expr_1 \<psi> = (Sup ((expr_1 ` (set x11)) \<union> (expr_1 ` (set x12))))"
        using expr_1.simps
        by blast
      hence "(Sup ((expr_1 ` (set x11)) \<union> (expr_1 ` (set x12)))) \<le> 0" 
        using \<open>expr_1 \<psi> \<le> 0\<close> Sup_enat_def
        by fastforce
      hence "Sup (expr_1 ` (set x11)) \<le> 0" "Sup (expr_1 ` (set x12)) \<le> 0"
        using Sup_enat_def 
        by (metis Sup_union_distrib le_supE)+
      from HML_conj \<open>conj_flattened \<psi>\<close> have "\<forall>x \<in> set x11. \<exists>\<alpha> \<psi>. (x = HML_poss \<alpha> \<psi>)"
and "\<forall>x \<in> set x12. \<exists>\<alpha> \<psi>. (x = HML_poss \<alpha> \<psi>)"
        using conj_flattened_alt 
        by blast+
      hence "\<forall>x \<in> set x11. expr_1 x \<ge> 1"
and "\<forall>x \<in> set x12. expr_1 x \<ge> 1"
        using expr_1.simps
        by fastforce+
      hence "x11 = []"
        using \<open>Sup (expr_1 ` (set x11)) \<le> 0\<close>
        by (metis SUP_bot_conv(2) bot_enat_def le_zero_eq list.set_sel(1) zero_neq_one)
      from \<open>\<forall>x \<in> set x12. expr_1 x \<ge> 1\<close> have "x12 = []"
        using \<open>Sup (expr_1 ` (set x12)) \<le> 0\<close>
        by (metis SUP_bot_conv(2) bot_enat_def le_zero_eq list.set_sel(1) zero_neq_one)
      with \<open>x11 = []\<close> show ?thesis using HML_conj by blast
    next
      case (HML_poss x21 x22)
      then have False
        using expr_1.simps \<open>y = HML_poss \<alpha> \<psi>\<close> \<open>expr_1 \<psi> \<le> 0\<close>
        by force
      then show ?thesis 
        by blast
    qed
    then show "\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
      using \<open>y = HML_poss \<alpha> \<psi>\<close> 
      by blast
  qed
  with x1_e show ?case
    using HML_failure.simps
    by fastforce
next
  show "\<And>x1 \<phi>.
       (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1) \<Longrightarrow> conj_flattened \<phi> \<Longrightarrow> HML_failure \<phi>) \<Longrightarrow>
       less_eq_t (expr (HML_poss x1 \<phi>)) (\<infinity>, 2, 0, 0, 1, 1) \<Longrightarrow>
       conj_flattened (HML_poss x1 \<phi>) \<Longrightarrow> HML_failure (HML_poss x1 \<phi>) "
    by (simp add: trace)
qed

lemma failure_lemma:
  assumes "conj_flattened \<phi>"
  shows "(HML_failure \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using assms failure_left failure_right by blast

lemma expr_4_read:
  fixes \<alpha>
  assumes A1: "HML_readiness \<phi>" and A2: "less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1)"
  shows "expr_4 (HML_poss \<alpha> \<phi>) \<le> 1"
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
  case (read_pos \<phi> \<alpha>)
  then show ?case
    by simp
next
  case (read_conj xs ys)
  have e1: "\<forall>\<alpha>. expr_1 (HML_poss \<alpha> (HML_conj [] [])) = 1"
    using expr_1.simps Sup_enat_def 
    by force 
  have "Sup (expr_1 ` set xs) \<le> 1"
    using e1 read_conj Sup_le_iff 
    by fastforce
  hence "Sup (expr_1 ` set (pos_r xs)) \<le> 1"
    using mon_expr_1_pos_r order.trans 
    by blast
  have "Sup (expr_1 ` set ys) \<le> 1"
    using e1 read_conj Sup_le_iff 
    by fastforce

  have e2: "\<forall>\<alpha>. expr_2 (HML_poss \<alpha> (HML_conj [] [])) = 1"
    using expr_2.simps Sup_enat_def 
    by force 
  hence "Sup (expr_2 ` (set xs)) \<le> 1" "Sup (expr_2 ` (set ys)) \<le> 1"
    using read_conj Sup_enat_def image_eqI
    by auto+
  have "expr_2 (HML_conj xs ys) = 1 + Sup ((expr_2 ` (set xs)) \<union> (expr_2 ` (set ys)))"
    using expr_2_conj by blast
  with \<open>Sup (expr_2 ` (set xs)) \<le> 1\<close> \<open>Sup (expr_2 ` (set ys)) \<le> 1\<close>
  have "expr_2 (HML_conj xs ys) \<le> 2"
    using one_add_one Sup_enat_def
    by (metis Sup_union_distrib add_left_mono sup_least)

  have e3: "\<forall>\<alpha>. expr_3 (HML_poss \<alpha> (HML_conj [] [])) \<le> 0"
    using expr_3.simps Sup_enat_def 
    by force 
  have "Sup (expr_1 ` (set xs)) \<le> 1" 
    using e1 read_conj Sup_enat_def
    by auto
  have "Sup (expr_3 ` (set xs)) \<le> 0" "Sup (expr_3 ` (set ys)) \<le> 0"
    using e3 read_conj Sup_enat_def
    by (metis SUP_bot_conv(2) bot_enat_def order_antisym zero_le)+
  have "expr_3 (HML_conj xs ys) = 
(Sup ((expr_1 ` (set xs)) \<union> (expr_3 ` (set xs)) \<union> (expr_3 ` (set ys))))"
    using expr_3.simps 
    by blast
  hence "expr_3 (HML_conj xs ys) \<le> 1"
    using read_conj Sup_enat_def 
\<open>Sup (expr_1 ` (set xs)) \<le> 1\<close> \<open>Sup (expr_3 ` (set xs)) \<le> 0\<close> \<open>Sup (expr_3 ` (set ys)) \<le> 0\<close>
    by (metis Sup_union_distrib Un_empty_right ile0_eq)

  have e4: "\<forall>\<alpha>. expr_4 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_4.simps Sup_enat_def 
    by force
  hence "Sup (expr_4 ` (set xs)) \<le> 0" "Sup (expr_4 ` (set ys)) \<le> 0"
    using Sup_enat_def 
    by (metis SUP_bot_conv(2) bot.extremum_unique bot_enat_def local.read_conj)+
  have e4_eq: "expr_4 (HML_conj xs ys) = 
Sup ({expr_1 (HML_conj (pos_r xs) [])} \<union> (expr_4 ` (set xs)) \<union> (expr_4 ` (set ys)))"
    using expr_4.simps
    by force
  have "expr_1 (HML_conj (pos_r xs) []) = (Sup ((expr_1 ` (set (pos_r xs))) \<union> (expr_1 ` (set []))))"
    using expr_1.simps
    by simp
  with \<open>Sup (expr_1 ` set (pos_r xs)) \<le> 1\<close> have "expr_1 (HML_conj (pos_r xs) []) \<le> 1"
    by fastforce
  with e4_eq \<open>Sup (expr_4 ` (set xs)) \<le> 0\<close> \<open>Sup (expr_4 ` (set ys)) \<le> 0\<close> 
  have "expr_4 (HML_conj xs ys) \<le> 1" 
    by (metis Sup_insert Sup_union_distrib bot_enat_def le_zero_eq sup_bot.right_neutral)

  have e5: "\<forall>\<alpha>. expr_5 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_5.simps Sup_enat_def 
    by force 

  have e6: "\<forall>\<alpha>. expr_6 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_6.simps Sup_enat_def 
    by force 
  
  then show ?case sorry
qed

lemma readiness_conj_xs:
  assumes A1: "(less_eq_t (expr (HML_conj xs ys)) (\<infinity>, 2, 1, 1, 1, 1))" and 
A2: "conj_flattened (HML_conj xs ys)"
shows "(\<forall>x \<in> set xs. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))"
proof
  have e3: "expr_3 (HML_conj xs ys) = 
Max({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> {expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs})"
    by (rule formula_prices_list.expr_3_set)
  have e2: "expr_2 (HML_conj xs ys) = 
Max({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})"
    by (rule formula_prices_list.expr_2_set)
  fix x
  assume A3: "x \<in> set xs"
  then have ne_xs: "{1 + expr_2 x | x. x \<in> set xs} \<noteq> {}" 
    by auto
  have fin_xs: "finite {1 + expr_2 x | x. x \<in> set xs}"
    by simp
  have subs_xs: "{1 + expr_2 x | x. x \<in> set xs} \<subseteq>
({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})" 
    by auto
  from A3 ne_xs fin_xs have xs_ge_x: "Max {1 + expr_2 x | x. x \<in> set xs} \<ge> 1 + expr_2 x"
    using Max_ge by blast
  have fin_xs: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})" 
    by simp
  from ne_xs subs_xs fin_xs xs_ge_x have e2_ge_x: "Max ({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})
 \<ge> 1 + expr_2 x"
    by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
  from this e2 have e2_ge_x: "expr_2 (HML_conj xs ys) \<ge> 1 + expr_2 x" 
    by simp
  from A3 have le_x: "less_eq_t (expr x) (\<infinity>, 2, 1, 1, 1, 1)"
    using A1 mon_conj by blast
  then show "\<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])"
  proof(cases x)
    case (HML_conj x11 x12)
    then have False
      using A2 A3 conj_flattened.simps(2) by blast
    then show ?thesis by simp
  next
    case x_poss: (HML_poss \<beta> x22)
    then have "less_eq_t (expr x22) (\<infinity>, 2, 1, 1, 1, 1)"
      using \<open>less_eq_t (expr x) (\<infinity>, 2, 1, 1, 1, 1)\<close> by auto
    from x_poss have "expr (HML_poss \<beta> x22) = 
(expr_1 x22 +1, expr_2 x22, expr_3 x22, expr_4 x22, expr_5 x22, expr_6 x22)" 
      by simp
    show ?thesis 
    proof(cases x22)
      case (HML_conj x3 x4)
      from HML_conj x_poss have x_eq: "x = (HML_poss \<beta> (HML_conj x3 x4))" 
        by simp
      then show ?thesis
proof(cases x3)
  case x3_nil: Nil
  then show ?thesis 
  proof(cases x4)
    case Nil
    from this x_eq x3_nil show ?thesis by simp
  next
    case x4_ne: (Cons a list)
    from this x_eq have "x = HML_poss \<beta> (HML_conj x3 (a # list))" 
      by simp
    then have "expr_2 x = expr_2 ((HML_conj x3 (a # list)))" 
      by simp
    also from formula_prices_list.expr_2_set have "... =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})"
      by blast
    finally have e2_x: "expr_2 x =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})"
      by this
    have ne: "{1 + expr_2 y |y. y \<in> set (a # list)} \<noteq> {}" 
      by auto
    have fin: "finite {1 + expr_2 y |y. y \<in> set (a # list)}"
      by simp
    have "expr_2 a \<ge> 1" 
      by (rule HML_subsets.expr_2_lb)
    then have a_ge_2: "1 + expr_2 a \<ge> 2" 
      by simp
    have elem: "1 + expr_2 a \<in> {1 + expr_2 y |y. y \<in> set (a # list)}" 
      by auto
    from this ne fin a_ge_2 have max_conj_a: "Max {1 + expr_2 y |y. y \<in> set (a # list)} \<ge> 2"
      by (meson Max_ge_iff)
        have fin: 
"finite ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})" 
          by simp
        have subs: "{1 + expr_2 y |y. y \<in> set (a # list)} \<subseteq> 
({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})" 
          by auto
        from ne fin subs max_conj_a have 
"Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)}) \<ge> 2"
          by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
        from this e2_x have "expr_2 x \<ge> 2" 
          by simp
        from this e2_ge_x have "expr_2 (HML_conj xs ys) \<ge> 3" 
          by simp
        from this A1 have False
          by (simp add: numeral_eq_enat)
        then show ?thesis by simp
      qed
next
  case x3_ne: (Cons a list)
  from this x_eq have "x = HML_poss \<beta> (HML_conj (a # list) x4)" 
      by simp
    then have "expr_2 x = expr_2 ((HML_conj (a # list) x4))" 
      by simp
    also from formula_prices_list.expr_2_set have "... =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})"
      by blast
    finally have e2_x: "expr_2 x =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})"
      by this
    have ne: "{1 + expr_2 y |y. y \<in> set (a # list)} \<noteq> {}" 
      by auto
    have fin: "finite {1 + expr_2 y |y. y \<in> set (a # list)}"
      by simp
    have "expr_2 a \<ge> 1" 
      by (rule HML_subsets.expr_2_lb)
    then have a_ge_2: "1 + expr_2 a \<ge> 2" 
      by simp
    have elem: "1 + expr_2 a \<in> {1 + expr_2 y |y. y \<in> set (a # list)}" 
      by auto
    from this ne fin a_ge_2 have max_conj_a: "Max {1 + expr_2 y |y. y \<in> set (a # list)} \<ge> 2"
      by (meson Max_ge_iff)
    have fin: 
"finite ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})" 
      by simp
    have subs: "{1 + expr_2 y |y. y \<in> set (a # list)} \<subseteq> 
({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})" 
      by auto
    from ne fin subs max_conj_a have 
"Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4}) \<ge> 2"
      by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
    from this e2_x have "expr_2 x \<ge> 2"
      by simp
    from this e2_ge_x have "expr_2 (HML_conj xs ys) \<ge> 3" 
      by simp
    from this A1 have False
      by (simp add: numeral_eq_enat)
    then show ?thesis by simp
  qed
next
  case x22_poss: (HML_poss \<gamma> x3)
  from this x_poss have "x = HML_poss \<beta> (HML_poss \<gamma> x3)" 
    by simp
  then have e1_ge_2: "expr_1 x  \<ge> 2" 
    by simp
  from A3 have ne:"{expr_1 x | x. x \<in> set xs} \<noteq> {}" 
    by auto
  have fin: "finite {expr_1 x | x. x \<in> set xs}" 
    by simp
  have subs: "{expr_1 x | x. x \<in> set xs} \<subseteq> 
({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> {expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs})" 
    by auto
  from fin ne e1_ge_2 A3 have x_ge_2: "Max {expr_1 x | x. x \<in> set xs} \<ge> 2"
    using Max_ge_iff by blast
  have fin:
"finite ({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> {expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs})"
    by auto
  from x_ge_2 subs this have e3_g_2: "Max ({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> 
{expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs}) \<ge> 2" 
    using Max_mono dual_order.trans ne 
    by blast
  from this e3 have "expr_3 (HML_conj xs ys) \<ge> 2" 
    by simp
  from this A1 have False
    by (simp add: one_enat_def)
  then show ?thesis 
    by simp
 qed
qed
qed

lemma readiness_conj_ys:
  assumes A1: "(less_eq_t (expr (HML_conj xs ys)) (\<infinity>, 2, 1, 1, 1, 1))" and 
A2: "conj_flattened (HML_conj xs ys)"
shows "(\<forall>x \<in> set ys. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))"
proof
  have e3: "expr_3 (HML_conj xs ys) = 
Max({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> {expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs})"
    by (rule formula_prices_list.expr_3_set)
  have e2: "expr_2 (HML_conj xs ys) = 
Max({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})"
    by (rule formula_prices_list.expr_2_set)
  have e5: "expr_5 (HML_conj xs ys) = 
Max({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
    by (rule formula_prices_list.expr_5_set)
  fix x
  assume A3: "x \<in> set ys"
  then have ne_xs: "{1 + expr_2 x | x. x \<in> set ys} \<noteq> {}" 
    by auto
  have fin_xs: "finite {1 + expr_2 x | x. x \<in> set ys}"
    by simp
  have subs_xs: "{1 + expr_2 x | x. x \<in> set ys} \<subseteq>
({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})" 
    by auto
  from A3 ne_xs fin_xs have xs_ge_x: "Max {1 + expr_2 x | x. x \<in> set ys} \<ge> 1 + expr_2 x"
    using Max_ge by blast
  have fin_xs: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})" 
    by simp
  from ne_xs subs_xs fin_xs xs_ge_x have e2_ge_x: "Max ({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})
 \<ge> 1 + expr_2 x"
    by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
  from this e2 have e2_ge_x: "expr_2 (HML_conj xs ys) \<ge> 1 + expr_2 x" 
    by simp
  from A3 have le_x: "less_eq_t (expr x) (\<infinity>, 2, 1, 1, 1, 1)"
    using A1 mon_conj by blast
  then show "\<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])"
  proof(cases x)
    case (HML_conj x11 x12)
    then have False
      using A2 A3 conj_flattened.simps(2) by blast
    then show ?thesis by simp
  next
    case x_poss: (HML_poss \<beta> x22)
then have "less_eq_t (expr x22) (\<infinity>, 2, 1, 1, 1, 1)"
      using \<open>less_eq_t (expr x) (\<infinity>, 2, 1, 1, 1, 1)\<close> by auto
    from x_poss have "expr (HML_poss \<beta> x22) = 
(expr_1 x22 +1, expr_2 x22, expr_3 x22, expr_4 x22, expr_5 x22, expr_6 x22)" 
      by simp
    show ?thesis 
    proof(cases x22)
      case (HML_conj x3 x4)
      from HML_conj x_poss have x_eq: "x = (HML_poss \<beta> (HML_conj x3 x4))" 
        by simp
      then show ?thesis
proof(cases x3)
  case x3_nil: Nil
  then show ?thesis 
  proof(cases x4)
    case Nil
    from this x_eq x3_nil show ?thesis by simp
  next
    case x4_ne: (Cons a list)
    from this x_eq have "x = HML_poss \<beta> (HML_conj x3 (a # list))" 
      by simp
    then have "expr_2 x = expr_2 ((HML_conj x3 (a # list)))" 
      by simp
    also from formula_prices_list.expr_2_set have "... =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})"
      by blast
    finally have e2_x: "expr_2 x =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})"
      by this
    have ne: "{1 + expr_2 y |y. y \<in> set (a # list)} \<noteq> {}" 
      by auto
    have fin: "finite {1 + expr_2 y |y. y \<in> set (a # list)}"
      by simp
    have "expr_2 a \<ge> 1" 
      by (rule HML_subsets.expr_2_lb)
    then have a_ge_2: "1 + expr_2 a \<ge> 2" 
      by simp
    have elem: "1 + expr_2 a \<in> {1 + expr_2 y |y. y \<in> set (a # list)}" 
      by auto
    from this ne fin a_ge_2 have max_conj_a: "Max {1 + expr_2 y |y. y \<in> set (a # list)} \<ge> 2"
      by (meson Max_ge_iff)
        have fin: 
"finite ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})" 
          by simp
        have subs: "{1 + expr_2 y |y. y \<in> set (a # list)} \<subseteq> 
({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)})" 
          by auto
        from ne fin subs max_conj_a have 
"Max ({1} \<union> {1 + expr_2 x |x. x \<in> set x3} \<union> {1 + expr_2 y |y. y \<in> set (a # list)}) \<ge> 2"
          by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
        from this e2_x have "expr_2 x \<ge> 2" 
          by simp
        from this e2_ge_x have "expr_2 (HML_conj xs ys) \<ge> 3" 
          by simp
        from this A1 have False
          by (simp add: numeral_eq_enat)
        then show ?thesis by simp
      qed
next
  case x3_ne: (Cons a list)
  from this x_eq have "x = HML_poss \<beta> (HML_conj (a # list) x4)" 
      by simp
    then have "expr_2 x = expr_2 ((HML_conj (a # list) x4))" 
      by simp
    also from formula_prices_list.expr_2_set have "... =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})"
      by blast
    finally have e2_x: "expr_2 x =
Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})"
      by this
    have ne: "{1 + expr_2 y |y. y \<in> set (a # list)} \<noteq> {}" 
      by auto
    have fin: "finite {1 + expr_2 y |y. y \<in> set (a # list)}"
      by simp
    have "expr_2 a \<ge> 1" 
      by (rule HML_subsets.expr_2_lb)
    then have a_ge_2: "1 + expr_2 a \<ge> 2" 
      by simp
    have elem: "1 + expr_2 a \<in> {1 + expr_2 y |y. y \<in> set (a # list)}" 
      by auto
    from this ne fin a_ge_2 have max_conj_a: "Max {1 + expr_2 y |y. y \<in> set (a # list)} \<ge> 2"
      by (meson Max_ge_iff)
    have fin: 
"finite ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})" 
      by simp
    have subs: "{1 + expr_2 y |y. y \<in> set (a # list)} \<subseteq> 
({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4})" 
      by auto
    from ne fin subs max_conj_a have 
"Max ({1} \<union> {1 + expr_2 x |x. x \<in> set (a # list)} \<union> {1 + expr_2 y |y. y \<in> set x4}) \<ge> 2"
      by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset)
    from this e2_x have "expr_2 x \<ge> 2"
      by simp
    from this e2_ge_x have "expr_2 (HML_conj xs ys) \<ge> 3" 
      by simp
    from this A1 have False
      by (simp add: numeral_eq_enat)
    then show ?thesis by simp
  qed
next
  case x22_poss: (HML_poss \<gamma> x3)
  from this x_poss have "x = HML_poss \<beta> (HML_poss \<gamma> x3)" 
    by simp
  then have e1_ge_2: "expr_1 x \<ge> 2" 
    by simp
  from A3 have ne:"{expr_1 x | x. x \<in> set ys} \<noteq> {}" 
    by auto
  have fin: "finite {expr_1 x | x. x \<in> set ys}" 
    by simp
  have subs: "{expr_1 x | x. x \<in> set ys} \<subseteq> 
({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
    by auto
  from fin ne e1_ge_2 A3 have x_ge_2: "Max {expr_1 x | x. x \<in> set ys} \<ge> 2"
    using Max_ge_iff by blast
  have fin:
"finite({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
    by auto
  from x_ge_2 subs this have e3_g_2: 
"Max({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys}) \<ge> 2" 
    using Max_mono dual_order.trans ne 
    by blast
  from this e5 have "expr_5 (HML_conj xs ys) \<ge> 2" 
    by simp
  from this A1 have False
    by (simp add: one_enat_def)
  then show ?thesis 
    by simp
    qed
  qed
qed

lemma readiness_left:
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))" and A2: "conj_flattened \<phi>"
  shows "HML_readiness \<phi>"
  using A1 A2
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from HML_subsets.readiness_conj_xs this have x1_poss: "(\<forall>x \<in> set x1. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))" 
    by auto
  from HML_conj HML_subsets.readiness_conj_ys have x2_poss:"(\<forall>x \<in> set x2. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))"
    by blast
  from this x1_poss have 
"(\<forall>x \<in> set x1. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])) \<and> (\<forall> y \<in> set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))" 
    by simp
  from this show ?case 
    by (rule HML_list.HML_readiness.intros(2))
next
  case (HML_poss x1 \<phi>)
  then show ?case
    by (simp add: read_pos)
qed

lemma readiness_lemma:
  assumes "conj_flattened \<phi> "
  shows "(HML_readiness \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using assms readiness_left readiness_right by blast

lemma impossible_futures_right:
  assumes A1: "HML_impossible_futures \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  using A1
proof(induction \<phi>)
  case (if_pos \<phi> \<alpha>)
  then show ?case by simp
next
  case (if_conj ys)
  assume A2: "\<forall>x\<in>set ys. HML_trace x"
  then have fa_e3: "\<forall>x\<in>set ys. expr_3 x = 0"
    using enat_0_iff(2) trace_right by auto
  have e3_eq: "expr_3 (HML_conj ([]::'a formula_list list) ys) =
Max({0} \<union> {expr_3 x | x. x \<in> set ([]::'a formula_list list)} \<union> {expr_3 y | y. y \<in> set ys} \<union> 
{expr_1 x | x. x \<in> set ([]::'a formula_list list)})"
    by (rule formula_prices_list.expr_3_set)
  have e3_xs_e: "{expr_3 x | x. x \<in> set ([]::'a formula_list list)} = {}"
    by simp
  have e3_xs_e_2: "{expr_1 x | x. x \<in> set ([]::'a formula_list list)} = {}"
    by simp
  from A2 trace_right have fa_ys: "\<forall>x\<in>set ys.(less_eq_t (expr x) (\<infinity>, 1, 0, 0, 0, 0))"
    by auto
  then have fa_ys_e2: "\<forall>x \<in> set ys. expr_2 x \<le> 1"
    by (simp add: one_enat_def)
  have e2_eq: "expr_2 (HML_conj ([]:: 'a formula_list list) ys) =
Max({1} \<union> {1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} \<union> {1 + expr_2 y | y. y \<in> set ys})"
    by (rule formula_prices_list.expr_2_set)
  have xs_e: "{1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} = {}"
    by simp
    have ys_cases: "ys = [] \<or> ys \<noteq> []"
    by simp
  then have e2: "expr_2 (HML_conj ([]:: 'a formula_list list) ys) \<le> 2"
  proof
    assume "ys = []"
    then have ys_e: "{1 + expr_2 y | y. y \<in> set ys} = {}"
      by simp
    from this xs_e have 
"Max({1} \<union> {1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} \<union> {1 + expr_2 y | y. y \<in> set ys}) = 1"
      by auto
    from this e2_eq show ?thesis
      by simp
  next
    assume ne: "ys \<noteq> []"
    have fin: "finite {1 + expr_2 y | y. y \<in> set ys}"
      by simp
    have fin_all: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} \<union> {1 + expr_2 y | y. y \<in> set ys})"
      by simp
    have subs: "{1 + expr_2 y | y. y \<in> set ys} \<subseteq> 
({1} \<union> {1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} \<union> {1 + expr_2 y | y. y \<in> set ys})"
      by auto
    from fin ne fa_ys_e2 have "Max {1 + expr_2 y | y. y \<in> set ys} <= 2"
      by auto
    from this xs_e fin_all subs have 
"Max({1} \<union> {1 + expr_2 x | x. x \<in> set ([]:: 'a formula_list list)} \<union> {1 + expr_2 y | y. y \<in> set ys}) \<le> 2"
      by (smt (verit, del_insts) Sup_fin.singleton Sup_fin.union Sup_fin_Max Un_infinite Un_singleton_iff empty_not_insert fin le_add2 nat_1_add_1 sup.bounded_iff)
    from this e2_eq show ?thesis
      by simp
  qed
  from ys_cases have e3: "expr_3 (HML_conj [] ys) \<le> 0"
  proof
    assume "ys = []"
    then have ys_e: "{expr_3 y | y. y \<in> set ys} = {}"
      by auto
    from this e3_eq e3_xs_e e3_xs_e_2 show ?thesis by simp
  next
    assume A4: "ys \<noteq> []"
    have fin: "finite {expr_3 y | y. y \<in> set ys}"
      by simp
    from this A4 fa_e3 have "Max {expr_3 y | y. y \<in> set ys} \<le> 0"
      by (smt (verit) Max_in bot_nat_0.extremum empty_Collect_eq last_in_set mem_Collect_eq)
    from this e3_eq e3_xs_e e3_xs_e_2 show ?thesis 
      by (metis (no_types, lifting) Max_singleton Sup_fin.union Sup_fin_Max dual_order.eq_iff fin 
finite.emptyI finite.insertI insert_not_empty sup.orderE sup_bot.right_neutral)
  qed
  have e4_eq: "expr_4 (HML_conj ([]::'a formula_list list) ys) =
Max ({expr_1 (HML_conj (pos_r ([]::'a formula_list list))[])} \<union> 
{expr_4 x|x. x \<in> set ([]::'a formula_list list)} \<union> {expr_4 y|y. y \<in> set ys})"
    by (rule formula_prices_list.expr_4_set)
  have e4_e1: "expr_1 (HML_conj (pos_r ([]::'a formula_list list))[]) = 0"
    by simp
  have e4_xs: "{expr_4 x|x. x \<in> set ([]::'a formula_list list)} = {}"
    by simp
  from ys_cases have e4: "expr_4 (HML_conj ([]::'a formula_list list) ys) = 0"
  proof
    assume "ys = []"
    then have "{expr_4 y|y. y \<in> set ys} = {}" 
      by auto
    from this e4_eq e4_e1 e4_xs show ?thesis by simp
  next
    assume A4: "ys \<noteq> []"
    then have ne_e4: "{expr_4 y|y. y \<in> set ys} \<noteq> {}" by auto
    have fin_e4: "finite {expr_4 y|y. y \<in> set ys}" by simp
    have "\<forall>x \<in> set ys. expr_4 x \<le> 0"
      by (metis expr.simps fa_ys less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
    from this ne_e4 fin_e4 have e4_ys: "Max {expr_4 y|y. y \<in> set ys} \<le> 0"
      by (smt (verit, ccfv_threshold) Max_in mem_Collect_eq)
    have subs: "{expr_4 y|y. y \<in> set ys} \<subseteq>
({expr_1 (HML_conj (pos_r ([]::'a formula_list list))[])} \<union> 
{expr_4 x|x. x \<in> set ([]::'a formula_list list)} \<union> {expr_4 y|y. y \<in> set ys})" 
      by auto
    from this A4 e4_eq e4_e1 e4_xs e4_ys show ?thesis by simp
  qed
  have e6_eq: "expr_6 (HML_conj ([]::'a formula_list list) ys) =
Max({0} \<union> {expr_6 x | x. x \<in> set ([]::'a formula_list list)} \<union> {1 + expr_6 y | y. y \<in> set ys})"
    by (rule HML_subsets.expr_6_union_neg)
  have e6_xs: "{expr_6 x | x. x \<in> set ([]::'a formula_list list)} = {}"
    by simp
  from ys_cases have e6: "expr_6 (HML_conj ([]::'a formula_list list) ys) \<le> 1"
  proof
    assume "ys = []"
    then have "{1 + expr_6 y | y. y \<in> set ys} = {}"
      by simp
    from this e6_eq e6_xs show ?thesis by simp
  next
    assume A4: "ys \<noteq> []"
    then have ne: "{1 + expr_6 y | y. y \<in> set ys} \<noteq> {}" 
      by simp
    have fin: "finite {1 + expr_6 y | y. y \<in> set ys}" 
      by simp
    from fa_ys have "\<forall>x\<in>set ys. expr_6 x \<le> 0"
      by (metis expr.simps less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
    from this fin ne fa_ys have "Max {1 + expr_6 y | y. y \<in> set ys} \<le> 1"
      by auto
    from this e6_eq e6_xs show ?thesis 
      by (metis (no_types, lifting) Sup_fin.singleton Sup_fin.union Sup_fin_Max fin finite.emptyI 
finite.insertI insert_def insert_not_empty le_numeral_extra(3) linordered_nonzero_semiring_class.zero_le_one singleton_conv sup.absorb_iff2 sup_mono)
qed
  from e2 e3 e4 e6 show "less_eq_t (expr (HML_conj [] ys)) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
    by (simp add: numeral_eq_enat one_enat_def zero_enat_def)
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
