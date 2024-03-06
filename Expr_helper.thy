theory Expr_helper
  imports
    HML_list
    formula_prices_list
    Failures
begin

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

lemma expr_1_mon_wrt_pos_r: 
  assumes "xs \<noteq> {}"
  shows "Sup (expr_1 ` (pos_r xs)) \<le> Sup (expr_1 ` (pos_r (xs \<union> {a})))"
proof-
  define max_val where "max_val \<equiv> (Sup (expr_1 ` xs))"
  define max_val_a where "max_val_a = (Sup (expr_1 ` (xs \<union> {a})))"
  define max_elem where "max_elem = (SOME \<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val)"
  define max_elem_a where "max_elem_a = (SOME \<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val_a)"
  define xs_new where "xs_new = xs - {max_elem}"
  define xs_new_a where "xs_new_a = (xs \<union> {a}) - {max_elem_a}"
  have "max_val \<le> max_val_a"
    unfolding max_val_def max_val_a_def
    by force
  consider "\<exists>\<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val \<and> (\<exists>\<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val_a)" |
"(\<nexists>\<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val) \<and> (\<exists>\<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val_a)" |
"\<exists>\<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val \<and> (\<nexists>\<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val_a)" |
"(\<nexists>\<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val) \<and> (\<nexists>\<psi>. \<psi> \<in> (xs \<union> {a}) \<and> expr_1 \<psi> = max_val_a)"
    unfolding max_val_def max_val_a_def by blast
  then show ?thesis proof(cases)
    case 1
    consider "max_elem_a \<in> xs \<and> max_elem_a = max_elem" |
        "max_elem_a \<in> xs \<and> max_elem_a \<noteq> max_elem" |
        "max_elem_a \<notin> xs \<and> max_elem_a = max_elem" |
        "max_elem_a \<notin> xs \<and> max_elem_a \<noteq> max_elem"
      by blast
    then show ?thesis proof(cases)
      case 1
      hence "xs_new \<subseteq> xs_new_a"
        unfolding xs_new_def xs_new_a_def by blast
      then show ?thesis
        unfolding xs_new_def xs_new_a_def max_elem_def max_elem_a_def max_val_a_def max_val_def 
        by (simp add: Sup_subset_mono image_mono)
    next
      case 2
      hence "\<exists>\<phi> \<in> xs. \<exists>\<psi> \<in> xs. \<phi> \<noteq> \<psi> \<and> expr_1 \<phi> = expr_1 \<psi> \<and> expr_1 \<psi> = expr_1 max_elem"
        using "1" unfolding max_elem_def max_elem_a_def 
        by (smt (verit, ccfv_threshold) SUP_upper \<open>max_val \<le> max_val_a\<close> antisym max_val_def verit_sko_ex')
      hence "\<exists>\<phi> \<in> xs. \<exists>\<psi> \<in> xs. \<phi> \<noteq> \<psi> \<and> expr_1 \<phi> = expr_1 \<psi> \<and> expr_1 \<psi> = expr_1 max_elem_a"
        using "1" 
        by (metis (mono_tags, lifting) "2" Sup_upper \<open>max_val \<le> max_val_a\<close> imageI leD max_elem_a_def max_elem_def max_val_def order_less_le someI_ex)
      have "Sup (expr_1 ` xs_new) = Sup (expr_1 ` xs)"
        unfolding xs_new_def 
        using \<open>\<exists>\<phi> \<in> xs. \<exists>\<psi> \<in> xs. \<phi> \<noteq> \<psi> \<and> expr_1 \<phi> = expr_1 \<psi> \<and> expr_1 \<psi> = expr_1 max_elem\<close>
        by (metis image_insert insert_Diff_single insert_absorb insert_iff xs_new_def)
      have "Sup (expr_1 ` xs_new_a) = Sup (expr_1 ` (xs \<union> {a}))"
        using 2 "1" \<open>\<exists>\<phi> \<in> xs. \<exists>\<psi> \<in> xs. \<phi> \<noteq> \<psi> \<and> expr_1 \<phi> = expr_1 \<psi> \<and> expr_1 \<psi> = expr_1 max_elem_a\<close>
        unfolding xs_new_a_def max_elem_def max_elem_a_def max_val_def max_val_a_def
        using "2" Sup_insert Sup_union_distrib Un_insert_left image_Un image_insert insert_Diff_single insert_iff mk_disjoint_insert sup.orderE sup_commute sup_ge1 xs_new_a_def
        by (smt (verit, best) "1" Diff_empty SUP_absorb SUP_union Un_iff insert_absorb max_val_a_def max_val_def)
      have "Sup (expr_1 ` xs) \<le> Sup (expr_1 ` (xs \<union> {a}))" 
        using \<open>max_val \<le> max_val_a\<close> max_val_a_def max_val_def by blast
      then show ?thesis 
        using \<open>Sup (expr_1 ` xs_new) = Sup (expr_1 ` xs)\<close> \<open>Sup (expr_1 ` xs_new_a) = Sup (expr_1 ` (xs \<union> {a}))\<close>
        unfolding xs_new_def max_elem_def max_elem_a_def max_val_def max_val_a_def
        by (simp add: max_elem_a_def max_val_a_def xs_new_a_def)
    next
      case 3
      have "max_elem \<in> xs"
        unfolding max_elem_def max_val_def 
        by (metis (mono_tags, lifting) "1" max_val_def someI)
      hence False using 3 
        by blast
      then show ?thesis by blast
    next
      case 4
      hence "max_elem_a = a"
        unfolding max_elem_a_def
        by (smt (verit, ccfv_threshold) "1" UnE singletonD someI_ex)
      hence "\<exists>\<phi> \<in> (xs \<union> {a}). \<exists>\<psi> \<in> (xs \<union> {a}). \<phi> \<noteq> \<psi> \<and> expr_1 \<phi> \<ge> expr_1 max_elem \<and> expr_1 \<psi> \<ge> expr_1 max_elem"
        using "1" \<open>max_val \<le> max_val_a\<close> 4
        unfolding max_elem_def max_elem_a_def max_val_def max_val_a_def
        by (smt (verit, best) dual_order.order_iff_strict insert_iff insert_is_Un someI sup.commute)
      hence "Sup (expr_1 ` xs_new_a) \<ge> Sup (expr_1 ` xs)"
        unfolding xs_new_a_def max_elem_def max_elem_a_def
        using "4" \<open>max_elem_a = a\<close> max_elem_a_def by auto
      have "Sup (expr_1 ` xs) \<ge> Sup (expr_1 ` (pos_r xs))"
        by (simp add: Sup_subset_mono image_mono)
      then show ?thesis using \<open>Sup (expr_1 ` xs_new_a) \<ge> Sup (expr_1 ` xs)\<close>
        unfolding xs_new_a_def max_val_a_def max_val_a_def 
        using "4" \<open>max_elem_a = a\<close> max_elem_a_def max_val_a_def by force
    qed
  next
    case 2
    hence "Sup (expr_1 ` xs) = \<infinity>"
      unfolding max_val_def max_elem_def
      by (smt (z3) Diff_insert_absorb Max_in SUP_insert Sup_enat_def Un_insert_right assms image_iff image_is_empty insert_Diff_single insert_absorb max_def max_val_a_def sup_bot_right sup_enat_def)
    hence "\<forall>x \<in> xs. expr_1 x < \<infinity>" using 2 
      using \<open>max_val \<le> max_val_a\<close> max_val_def by auto
    have "Sup (expr_1 ` (xs \<union> {a})) = \<infinity>"
      using \<open>Sup (expr_1 ` xs) = \<infinity>\<close> 
      by (metis \<open>max_val \<le> max_val_a\<close> enat_ord_simps(5) max_val_a_def max_val_def)
    from 2 have "(\<exists>\<psi>. \<psi> \<in> xs \<union> {a} \<and> expr_1 \<psi> = max_val_a)"
      unfolding max_val_a_def 
      by blast
    with 2 have "\<exists>x \<in> (xs \<union> {a}). expr_1 x = \<infinity>" 
      unfolding max_val_a_def 
      using \<open>Sup (expr_1 ` xs) = \<infinity>\<close> 
      by (metis \<open>Sup (expr_1 ` (xs \<union> {a})) = \<infinity>\<close>)
    hence "max_elem_a = a"
      using 2 \<open>\<forall>x \<in> xs. expr_1 x < \<infinity>\<close>
      unfolding max_elem_a_def max_val_def max_val_a_def 
      using \<open>Sup (expr_1 ` xs) = \<infinity>\<close> 
      by force
    hence "expr_1 a = \<infinity>"
      unfolding max_elem_a_def 
      using \<open>\<exists>x\<in>xs \<union> {a}. expr_1 x = \<infinity>\<close> \<open>\<forall>x\<in>xs. expr_1 x < \<infinity>\<close> by auto 
    hence "xs_new_a = xs"
      unfolding xs_new_a_def
      using \<open>\<forall>x \<in> xs. expr_1 x < \<infinity>\<close> \<open>max_elem_a = a\<close> 
      by auto
    hence "pos_r (xs \<union> {a}) = xs"
      unfolding xs_new_a_def max_elem_a_def max_val_a_def
      by simp
    hence "pos_r xs \<subseteq> pos_r (xs \<union> {a})" 
      by simp 
    then show ?thesis 
      using \<open>Sup (expr_1 ` xs) = \<infinity>\<close> \<open>pos_r (xs \<union> {a}) = xs\<close> enat_ord_simps(3) by presburger
  next
    case 3
    hence False 
      using \<open>max_val \<le> max_val_a\<close>
      unfolding max_elem_a_def max_elem_def max_val_def max_val_a_def
      by (metis SUP_insert Un_insert_right insertCI max_def sup_bot_right sup_enat_def)
    then show ?thesis by simp
  next
    case 4
    hence "Sup (expr_1 ` xs) = \<infinity>"
      unfolding max_val_def
      by (metis (mono_tags, lifting) Max_in Sup_enat_def assms image_iff image_is_empty)
    with 4 have "\<forall>x \<in> xs. expr_1 x < \<infinity>" 
      by (simp add: max_val_def)
    hence "\<not>(finite xs)" using 4 \<open>Sup (expr_1 ` xs) = \<infinity>\<close> 
      by (metis (mono_tags, lifting) Max_in Sup_enat_def assms enat_ord_simps(4) finite_imageI image_iff image_is_empty)
    hence "\<not>(finite xs_new)" 
      unfolding xs_new_def
      by fastforce
    hence "Sup (expr_1 ` (pos_r xs)) \<ge> \<infinity>"
      unfolding xs_new_def max_val_def max_elem_def
      using pos_r.simps
      by (smt (verit, best) "4" Diff_empty Diff_insert0 SUP_insert SUP_le_iff \<open>Sup (expr_1 ` xs) = \<infinity>\<close> insert_Diff max_def max_val_def sup_enat_def)
    from 4 have "Sup (expr_1 ` (xs \<union> {a})) = \<infinity>"
      unfolding max_val_a_def
      by (simp add: \<open>Sup (expr_1 ` xs) = \<infinity>\<close> sup_enat_def)
    with 4 have "\<forall>x \<in> (xs \<union> {a}). expr_1 x < \<infinity>" 
      using max_val_a_def
      by auto
    hence "\<not>(finite (xs \<union> {a}))" using 4 \<open>Sup (expr_1 ` (xs \<union> {a})) = \<infinity>\<close>
      using \<open>infinite xs\<close> by blast 
    hence "\<not>(finite xs_new_a)" 
      unfolding xs_new_a_def
      by fastforce
    hence "Sup (expr_1 ` (pos_r (xs \<union> {a}))) \<ge> \<infinity>"
      unfolding xs_new_a_def max_val_a_def max_elem_a_def
      using pos_r.simps
      by (smt (verit, best) "4" Diff_empty Diff_insert0 SUP_insert SUP_least \<open>Sup (expr_1 ` (xs \<union> {a})) = \<infinity>\<close> insert_Diff max_def max_val_a_def sup_enat_def)
    then show ?thesis using \<open>Sup (expr_1 ` (pos_r xs)) \<ge> \<infinity>\<close>
      by (metis enat_ord_simps(5))
  qed
qed

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

(*
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
     using sup_i sup_j Sup_union_distrib expr_6_conj sup_esuc
     by (metis le_sup_iff)
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
    using 3 
    by (metis SUP_image SUP_least expr.simps expr_6_conj image_is_empty less_eq_t.simps sup_bot_right)
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

lemma expr_stacked_pos_conj_J_empty:
  assumes "stacked_pos_conj_J_empty \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
  using assms
proof(induction \<phi> rule: stacked_pos_conj_J_empty.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 \<psi> \<alpha>)
have "less_eq_t (expr \<psi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
    using expr_nested_empty_pos_conj 2
    by blast
  then show ?case 
    by simp
next
  case (3 \<Phi> I J)
  hence "\<forall>\<phi>\<in>\<Phi> ` I. expr_5 \<phi> \<le> 0"
"\<forall>\<phi>\<in>\<Phi> ` I. expr_6 \<phi> \<le> 0"
    by simp+
  hence "expr_5 (hml_conj I J \<Phi>) \<le> 0"
"expr_6 (hml_conj I J \<Phi>) \<le> 0"
    using 3 expr_5_conj expr_6.expr_6_conj image_is_empty sup_bot_right  
    by (metis SUP_image SUP_least)+
  then show ?case 
    by simp
qed

lemma expr_6_conj:
  assumes "(\<Phi> ` J) \<noteq> {}"
  shows "expr_6 (hml_conj I J \<Phi>) \<ge> 1"
proof-
  have e6: "expr_6 (hml_conj I J \<Phi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J)))"
    using expr.simps
    by simp
  have "\<forall>A::enat set. Sup A \<ge> 0" 
    by simp
  from assms have "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<ge> 1"
    using eSuc_def Sup_enat_def SUP_image eSuc_Sup bot_enat_def
    by (metis iless_eSuc0 image_is_empty linorder_not_le one_eSuc zero_ne_eSuc)
  hence "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<ge> 1"
    by (simp add: Sup_union_distrib sup.coboundedI2)
  with e6 show ?thesis by simp
qed

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
  case (hml_conj x1 x2 x3)
  hence "x3` x2 = {}"
    by (metis expr_6_conj ile0_eq not_one_le_zero)
  have sup_le: "Sup ((expr_1 \<circ> x3) ` x1) \<le> 0"
"Sup ((expr_1 \<circ> x3) ` x2) \<le> 0"
"Sup ((expr_6 \<circ> x3) ` x1) \<le> 0" 
"Sup ((eSuc \<circ> expr_6 \<circ> x3) ` x2) \<le> 0" 
    using expr_1_conj expr_6.expr_6_conj hml_conj(2, 3)
    by (metis Sup_union_distrib le_sup_iff)+
  hence "Sup ((expr_6 \<circ> x3) ` x2) \<le> 0" 
    using eSuc_def 
    by (metis expr_6_conj SUP_image hml_conj.prems(2) image_empty le_zero_eq not_one_le_zero)
  hence "\<forall>x \<in> x3 ` x1. expr_1 x \<le> 0 \<and> expr_6 x \<le> 0"
"\<forall>x \<in> x3 ` x2. expr_1 x \<le> 0 \<and> expr_6 x \<le> 0"
    using sup_le
    by (metis SUP_image SUP_upper le_zero_eq)+
  hence "\<forall>x \<in> x3 ` x1. nested_empty_pos_conj x"
"\<forall>x \<in> x3 ` x2. nested_empty_pos_conj x"
    using hml_conj(1, 2)
    by blast+
  then show ?case using \<open>x3` x2 = {}\<close>
    by (simp add: nested_empty_pos_conj.intros(2))
qed

lemma expr_5_restrict_negations: 
  assumes "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 1"
"expr_4 (hml_conj I J \<Phi>) \<le> 0"
  shows "(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_pos y)"
proof                                
  fix y 
  assume "y \<in>\<Phi> ` J"
  from assms have "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
  "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
  "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
      apply (simp add: Sup_union_distrib)
    using assms Sup_union_distrib
     apply (simp add: Sup_union_distrib)
    using assms Sup_union_distrib
    by (metis expr_4_conj le_sup_iff)
  hence "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using eSuc_def
    by (metis Sup_enat_def eSuc_Sup eSuc_ile_mono image_comp le_zero_eq one_eSuc)
  hence "expr_6 y \<le> 0"
"expr_1 y \<le> 1"
"expr_4 y \<le> 0"
    using \<open>y \<in> \<Phi> ` J\<close> Sup_le_iff \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close>
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
    case (hml_conj x31 x32 x33)
    have "(Sup ((expr_1 \<circ> x33) ` x31) \<le> 1)"
"(Sup ((expr_6 \<circ> x33) ` x31) \<le> 0)"
"(Sup ((expr_4 \<circ> x33) ` x31) \<le> 0)"
      using hml_conj Sup_union_distrib expr_1_conj expr_6.expr_6_conj expr_4_conj
      by (metis le_supE)+
    hence "\<forall>x \<in> (x33 ` x31). expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x \<le> 0"
      by (metis SUP_image SUP_upper dual_order.trans)
    hence "\<forall>x \<in> (x33 ` x31). stacked_pos_conj_pos x"
      using hml_conj
      by blast
    have "((\<exists>\<phi> \<in> (x33 ` x31). ((stacked_pos_conj_pos \<phi>) \<and> 
                     (\<forall>\<psi> \<in> (x33 ` x31). \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>))) \<or>
   (\<forall>\<psi> \<in> (x33 ` x31). nested_empty_pos_conj \<psi>))"
    proof(cases "\<exists>\<phi> \<in> (x33 ` x31). expr_1 \<phi> \<ge> 1")
      case True
      then obtain \<phi> where "\<phi> \<in> (x33 ` x31)" "expr_1 \<phi> \<ge> 1"
        by blast
      hence "expr_1 \<phi> = 1"
        using \<open>\<forall>x\<in>x33 ` x31. expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x <= 0\<close> antisym by blast
      have "stacked_pos_conj_pos \<phi>"
        using \<open>\<forall>x\<in>x33 ` x31. stacked_pos_conj_pos x\<close> \<open>\<phi> \<in> x33 ` x31\<close> by blast
      have "\<forall>\<psi> \<in> (x33 ` x31). \<psi> \<noteq> \<phi> \<longrightarrow> expr_1 \<psi> \<le> 0"
      proof(rule ccontr)
        assume "\<not> (\<forall>\<psi>\<in>x33 ` x31. \<psi> \<noteq> \<phi> \<longrightarrow> expr_1 \<psi> \<le> 0)"
        then obtain \<psi> where "\<psi> \<in> x33 ` x31" "\<psi> \<noteq> \<phi>" "expr_1 \<psi> \<ge> 1"
          by (metis ileI1 not_le_imp_less one_eSuc)
        hence "Sup (expr_1 ` (pos_r (x33 ` x31))) >= 1"
          using \<open>expr_1 \<phi> = 1\<close>
          using \<open>\<forall>x\<in>x33 ` x31. expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x \<le> 0\<close> \<open>\<phi> \<in> x33 ` x31\<close> antisym
          by (smt (verit) Diff_iff Diff_insert_absorb SUP_upper insertE mk_disjoint_insert pos_r.simps)
        hence "expr_4 (hml_conj x31 x32 x33) \<ge> 1"
          using expr_4_conj expr_6_conj Sup_union_distrib 
\<open>Sup ((expr_4 \<circ> x33) ` x31) \<le> 0\<close> bot_enat_def
          by (metis hml_conj.prems(1) image_is_empty le_iff_sup not_one_le_zero sup_bot_right)
        then show False using hml_conj(4) 
          using dual_order.trans not_one_le_zero by blast
      qed
      hence "\<forall>\<psi>\<in>x33 ` x31. \<psi> \<noteq> \<phi> \<longrightarrow> expr_1 \<psi> \<le> 0 \<and> expr_6 \<psi> \<le> 0"
        using \<open>\<forall>x\<in>x33 ` x31. expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x \<le> 0\<close> by blast
      hence "\<forall>\<psi>\<in>x33 ` x31. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>"
        using expr_1_expr_6_le_0_is_nested_empty_pos_conj
        by blast
      then show ?thesis using \<open>stacked_pos_conj_pos \<phi>\<close> \<open>\<phi> \<in> (x33 ` x31)\<close>
        by blast
    next
      case False
      then have "\<forall>x \<in> (x33 ` x31). expr_1 x \<le> 0"
        using iless_eSuc0 one_eSuc by fastforce
      have "\<forall>x \<in> (x33 ` x31). expr_6 x \<le> 0"
        using \<open>\<forall>x\<in>x33 ` x31. expr_1 x \<le> 1 \<and> expr_6 x \<le> 0 \<and> expr_4 x \<le> 0\<close> by blast
      with \<open>\<forall>x \<in> (x33 ` x31). expr_1 x \<le> 0\<close> have "(\<forall>\<psi> \<in> (x33 ` x31). nested_empty_pos_conj \<psi>)"
        using expr_1_expr_6_le_0_is_nested_empty_pos_conj
        by blast
      then show ?thesis by blast
    qed
    then show ?case 
      using expr_6_conj hml_conj.prems(1)
      by (metis le_zero_eq not_one_le_zero stacked_pos_conj_pos.intros(3))
  qed
qed

lemma expr_1_0_expr_6_1_nested_empty_conj: 
assumes "expr_1 \<phi> \<le> 0" "expr_6 \<phi> \<le> 1"
shows "nested_empty_conj \<phi>"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using nested_empty_conj.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  hence False 
    by force
  then show ?case by blast
next
  case (hml_conj x1 x2 x3)
  hence "Sup ((eSuc \<circ> expr_6 \<circ> x3) ` x2) \<le> 1"
    by (simp add: Sup_union_distrib)
  hence "Sup ((expr_6 \<circ> x3) ` x2) \<le> 0"
    using Sup_enat_def eSuc_Sup
    by (metis (no_types, opaque_lifting) SUP_image  eSuc_ile_mono nle_le one_eSuc)
  hence "\<forall>x \<in> x3 ` x2. expr_6 x \<le> 0"
    by (metis SUP_image Sup_le_iff image_eqI) 
  from hml_conj have "Sup ((expr_1 \<circ> x3) ` x2) \<le> 0"
    by (metis Sup_union_distrib expr_1_conj le_sup_iff)
  hence "\<forall>x \<in> x3 ` x2. expr_1 x \<le> 0"
    by (metis SUP_image Sup_le_iff image_eqI) 
  hence "\<forall>x \<in> x3 ` x2. nested_empty_pos_conj x"
    using expr_1_expr_6_le_0_is_nested_empty_pos_conj 
    using \<open>\<forall>x\<in>x3 ` x2. expr_6 x \<le> 0\<close> by blast
  from hml_conj have "\<forall>x \<in> x3 ` x1. expr_1 x \<le> 0"
    using Sup_le_iff Sup_union_distrib expr_1_conj le_sup_iff SUP_image image_eqI
    by (metis (no_types, lifting))
  from hml_conj have "\<forall>x \<in> x3 ` x1. expr_6 x \<le> 1"
    using Sup_le_iff Sup_union_distrib le_sup_iff SUP_image image_eqI
    by (metis (no_types, lifting) expr_6.expr_6_conj)
  hence "\<forall>x \<in> x3 ` x1. nested_empty_conj x"
    using \<open>\<forall>x \<in> x3 ` x1. expr_1 x \<le> 0\<close> hml_conj
    by blast
  then show ?case using \<open>\<forall>x \<in> x3 ` x2. nested_empty_pos_conj x\<close> 
    by (smt (verit, ccfv_SIG) \<open>\<forall>x\<in>x3 ` x2. expr_1 x \<le> 0\<close> \<open>\<forall>x\<in>x3 ` x2. expr_6 x \<le> 0\<close> hml_conj.IH(1) 
i0_lb imageE le_zero_eq nested_empty_conj.intros(2) rangeI)
qed

lemma expr_4_expr_6_ft_to_recursive_ft: 
  assumes "expr_4 (hml_conj I J \<Phi>) \<le> 0" "expr_5 (hml_conj I J \<Phi>) \<le> 1" 
"expr_6 (hml_conj I J \<Phi>) \<le> 1" "\<forall>\<phi> \<in> (\<Phi> ` I). HML_failure_trace \<phi>"
  shows "(\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_conj y)"
proof(cases "(\<exists>\<psi> \<in> (\<Phi> ` I). expr_1 \<psi> \<ge> 1)")
  case True
  then obtain \<psi> where "\<psi> \<in> \<Phi> ` I" "expr_1 \<psi> \<ge> 1"
    by blast
  hence "HML_failure_trace \<psi>"
    using assms(4) by blast 
  from assms(3) have "(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 1)"
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
      from \<open>expr_1 y \<ge> 1\<close> \<open>expr_1 \<psi> \<ge> 1\<close> \<open>\<psi> \<in> \<Phi> ` I\<close> \<open>y \<in> \<Phi> ` I\<close> have "Sup (expr_1 ` ((\<Phi> ` I) - {max_elem})) >= 1"
        unfolding max_elem_def 
        by (smt (verit) DiffI SUP_upper2 \<open>\<psi> \<noteq> y\<close> emptyE insertE)
      hence "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<ge> 1"
        using pos_r.simps
        unfolding max_elem_def 
        by metis
      hence "expr_4 (hml_conj I J \<Phi>) \<ge> 1"
        using Sup_union_distrib assms(1) bot_enat_def expr_4_conj
        by (metis  ile0_eq sup_bot.neutr_eq_iff)
      then show False 
        using assms(2) assms(1) not_one_le_zero order_trans by blast
    qed
  qed
  hence "(\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> expr_1 y \<le> 0)"
    by blast

  hence "(\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
    using \<open>(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 1)\<close> expr_1_0_expr_6_1_nested_empty_conj
    by blast 
  with \<open>HML_failure_trace \<psi>\<close> \<open>\<psi> \<in> \<Phi> ` I\<close> show ?thesis 
    by blast
next
  assume "\<not> (\<exists>\<psi>\<in>\<Phi> ` I. 1 \<le> expr_1 \<psi>)"
  hence "\<forall>\<psi>\<in>\<Phi> ` I. expr_1 \<psi> \<le> 0"
    
    by (simp add: linorder_not_le one_eSuc)
      from assms(2) have "(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 1)"
        using expr_6.expr_6_conj Sup_le_iff Un_iff comp_apply image_iff
        by (smt (verit, del_insts) assms(3))
  hence "(\<forall>y \<in> (\<Phi> ` I). nested_empty_conj y)"
    using \<open>(\<forall>y \<in> (\<Phi> ` I). expr_6 y \<le> 1)\<close> expr_1_0_expr_6_1_nested_empty_conj 
\<open>\<forall>\<psi>\<in>\<Phi> ` I. expr_1 \<psi> \<le> 0\<close>
    by blast
  then show ?thesis by blast
qed
*)
end