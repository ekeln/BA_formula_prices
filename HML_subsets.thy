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
  assumes A1: "less_eq_t (expr (HML_poss \<alpha> \<phi>)) (n1, n2, n3, n4, n5, n6)"
  shows "less_eq_t (expr \<phi>) (n1, n2, n3, n4, n5, n6)" 
proof-
  from A1 have E_rest: 
"expr_2 \<phi> \<le> n2 \<and> expr_3 \<phi> \<le> n3 \<and> expr_4 \<phi> \<le> n4 \<and> expr_5 \<phi> \<le> n5 \<and>expr_6 \<phi> \<le> n6" 
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

lemma "less_eq_t (e_sup (expr ` (set (pos_r (xs))))) (e_sup (expr ` (set xs)))"
proof-
  have "set (pos_r xs) \<subseteq> set xs" 
    using pos_r.simps filter_is_subset
    by metis
  thus ?thesis
    using less_eq_t.simps expr.simps e_sup_def
    oops

lemma expr_mon_wrt_pos_r: 
"less_eq_t (e_sup (expr ` (set (pos_r xs)))) (e_sup (expr ` (set (pos_r (a#xs)))))"
  sorry

lemma expr_1_mon_wrt_pos_r: 
"Sup (expr_1 ` (set (pos_r xs))) \<le> Sup (expr_1 ` (set (pos_r (a#xs))))"
proof-
  from expr_mon_wrt_pos_r have 1: "(Sup (fst ` (expr ` (set (pos_r xs))))) \<le> (Sup (fst ` (expr ` (set (pos_r (a#xs))))))"
    using less_eq_t.simps
    unfolding e_sup_def
    by blast
  fix \<phi>:: "('a)formula_list"
  have "\<forall>S. (fst ` expr ` S) = {fst(expr s)|s. s \<in> S}" 
    by blast
  hence "\<forall>S. (fst ` expr ` S) = expr_1 ` S"
    by auto
  hence "(fst ` (expr ` (set (pos_r xs)))) = expr_1 ` (set (pos_r xs))" 
"(fst ` (expr ` (set (pos_r (a#xs))))) = expr_1 ` (set (pos_r (a#xs)))"
    by blast+
  with 1 show ?thesis 
    by simp
qed

lemma mon_pos_r: 
  "Sup (expr_1 ` (set (pos_r xs))) \<le> Sup (expr_1 ` (set xs))"
  sorry

lemma pos_r_del_max:
  assumes "\<forall>x\<in>set xs. expr_1 x < expr_1 a" "\<forall>x\<in>set ys. expr_1 x < expr_1 a"
  shows "pos_r (xs @ [a] @ ys) = (xs @ ys)"
proof-
  define max_val where "max_val \<equiv> (Sup (expr_1 ` (set (xs @ [a] @ ys))))"
  define max_elem where "max_elem \<equiv> hd(filter (\<lambda>y. expr_1 y = max_val) (xs @ [a] @ ys))"
  define xs_new where "xs_new = filter (\<lambda>y. y \<noteq> max_elem) (xs @ [a] @ ys)"
  have ne: "(set (xs @ [a] @ ys)) \<noteq> {}" 
    by blast
  have fin: "finite (set (xs @ [a] @ ys))"
    by blast
  with ne have "max_val = Max (expr_1 ` (set (xs @ [a] @ ys)))"
    unfolding max_val_def
    using Sup_enat_def
    by simp
  have "a \<in> set (xs @ [a] @ ys)"
    by simp
  from assms have "(\<And>y. y \<in> expr_1 ` (set (xs @ [a] @ ys)) \<Longrightarrow> y \<le> expr_1 a)" 
    by auto
  with fin \<open>max_val = Max (expr_1 ` (set (xs @ [a] @ ys)))\<close> \<open>a \<in> set (xs @ [a] @ ys) \<close>
  have "max_val = expr_1 a"
    using Max_eqI
    by blast
  hence "max_elem = a"
    unfolding max_elem_def
    using assms
    by (smt (verit, ccfv_threshold) empty_filter_conv filter.simps(2) filter_append hd_append 
list.sel(1) order_less_irrefl)
  from \<open>max_val = expr_1 a\<close> have "\<forall>x \<in>set xs. max_elem \<noteq> x" "\<forall>x\<in>set ys. max_elem \<noteq> x"
    using assms
    unfolding max_elem_def
    using \<open>max_elem = a\<close> max_elem_def 
    by auto[2]
  with \<open>max_elem = a\<close> have "xs_new = (xs @ ys)"
    unfolding xs_new_def
    using append_Nil filter.simps(2) filter_True filter_append
    by (smt (verit, ccfv_threshold))
  thus ?thesis
    unfolding max_val_def max_elem_def xs_new_def
    using pos_r.elims
    by metis
qed

lemma pos_r_2:
  assumes A1: "(\<exists>x\<in>set xs. expr_1 a < expr_1 x)"
  shows "set (pos_r (a#xs)) = set (pos_r (xs)) \<union> {a}"
proof(cases xs)
  case Nil
  with assms have False 
    by auto
  then show ?thesis by simp
next
  case (Cons b list)
  hence ne:"set xs \<noteq> {}"
    by blast
  have fin: "finite (set xs)"
    by blast
  define max_val where "max_val \<equiv> (Sup (expr_1 ` (set (a#xs))))"
  define max_elem where "max_elem \<equiv> hd(filter (\<lambda>y. expr_1 y = max_val) (a#xs))"
  define xs_new where "xs_new \<equiv> filter(\<lambda>y. y \<noteq> max_elem) (a#xs)"
  from Cons assms have "max_val > expr_1 a" 
    unfolding max_val_def 
    by (meson less_SUP_iff list.set_intros(2))
  hence "(Sup (expr_1 ` (set (a#xs)))) = (Sup (expr_1 ` (set xs)))"
    using Sup_enat_def assms image_insert Sup_insert ne fin Max_gr_iff
    unfolding max_val_def 
    by (smt (verit) insert_absorb linorder_neq_iff list.simps(15) sup.absorb4 sup_commute)
  hence "max_val = (Sup (expr_1 ` (set xs)))"
    unfolding max_val_def
    by blast
  with \<open>max_val > expr_1 a\<close> Cons have "max_elem \<noteq> a" 
    using Max_in Sup_enat_def ne fin 
    unfolding max_elem_def max_val_def
    by (smt (verit, best) List.finite_set empty_filter_conv finite_imageI imageE image_is_empty linorder_neq_iff list.distinct(1) list.set_sel(1) mem_Collect_eq set_empty set_filter)
  hence "xs_new = (a# (filter(\<lambda>y. y \<noteq> max_elem) xs))"
    unfolding xs_new_def
    by simp
  then show ?thesis 
    using pos_r.simps \<open>max_elem \<noteq> a\<close> \<open>max_val = Sup (expr_1 ` set xs)\<close> list.sel(1) list.simps(15) filter.simps(2) insert_is_Un
    unfolding max_val_def xs_new_def max_elem_def
    by (metis sup_commute)
qed


\<comment> \<open>pos_r xs where all xs are the same returns the empty list.\<close>
lemma pos_r_eq:
  assumes A1: "(\<forall>x \<in> set xs. \<forall>y \<in> set xs. x = y)"
  shows "set (pos_r xs) = {}"
proof(cases xs)
  case Nil
  then show ?thesis 
    using pos_r.simps 
    by auto
next
  case (Cons a list)
  hence ne: "set xs \<noteq> {}"
    by blast
  have fin: "finite (set xs)"
    by blast
  with assms ne have "\<forall>x \<in>set xs. expr_1 x = (Sup (expr_1 ` (set xs)))"
    using Sup_enat_def SUP_eq_const
    by (metis (no_types, lifting))
  with assms Cons have "hd(filter (\<lambda>y. expr_1 y = (Sup (expr_1 ` (set xs)))) xs) = a"
    by (metis (mono_tags, lifting) filter.simps(2) list.sel(1) list.set_intros(1))
  with assms Cons show ?thesis using pos_r.simps
    by (metis (full_types) empty_filter_conv list.set(1) list.set_intros(1))
qed


(*TODO*)
lemma pos_r_3:
  shows "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)}) \<le> Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))})"
  oops
    
(*TODO: zeigen, wenn xs nicht leer ist, das pos_r (a#xs) größer als pos_r(xs) ist.*)
  

(*Done*)
lemma expr_1_pos_r:
  assumes A1: "expr_1 (HML_conj (pos_r (a#xs)) ys) \<le> n4"
  defines "A \<equiv> {0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}"
  defines "B \<equiv> ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)})"
  shows "expr_1 (HML_conj (pos_r xs) ys) \<le> n4"
  oops

subsection \<open>monotonicity of subformulas of \<And>\<Phi>\<close>

(*Done*)
lemma expr_1_conj_pos_r:
  assumes A1: "\<forall>x1a \<in> set x1. expr_1 x1a \<le> n4"
and fa_x2: "\<forall>x2a \<in> set x2. expr_1 x2a \<le> n4"
shows "expr_1 (HML_conj (pos_r x1) x2) \<le> n4"
proof-
  from assms(1) mon_pos_r have pos_r_le_n4: "\<forall>x1a \<in> set (pos_r x1). expr_1 x1a \<le> n4" 
    by simp
  have fin: "finite (expr_1 ` set (pos_r x1) \<union> expr_1 ` set x2)"
    by blast
  with assms pos_r_le_n4 have "Sup (expr_1 ` set (pos_r x1) \<union> expr_1 ` set x2) \<le> n4"
    using Sup_enat_def
    by auto
  thus ?thesis
    using expr_1.simps(1) 
    by metis
qed

lemma expr_4_conj_le:
  fixes n4 and xs and ys and a
  assumes A2: "expr_4 (HML_conj xs ys) \<le> n4 \<Longrightarrow> 
\<forall>x\<in>set xs.(expr_4 x \<le> n4)" and
A3: "expr_4 (HML_conj (a # xs) ys) \<le> n4"
shows "expr_4 (HML_conj xs ys) \<le> n4"
proof-
  have e4_eq: "expr_4 (HML_conj (a # xs) ys) = 
Sup ({expr_1 (HML_conj (pos_r (a # xs)) [])} \<union> (expr_4 ` (set (a # xs))) \<union> (expr_4 ` (set ys)))"
    using expr_4.simps 
    by blast
  with assms(2) have "Sup (expr_4 ` (set ys)) \<le> n4"
    by (simp add: Sup_le_iff)
  from e4_eq assms(2) have "Sup (expr_4 ` set (a # xs)) \<le> n4"
    by (simp add: Sup_le_iff)
  hence "Sup (expr_4 ` set xs) \<le> n4"
    by auto
  from assms(2) e4_eq have "expr_1 (HML_conj (pos_r (a # xs)) []) \<le> n4"
    by auto
  hence "Sup (expr_1 ` (set (pos_r (a#xs)))) \<le> n4"
    using expr_1.simps Sup_le_iff Un_iff 
    by auto
  hence "Sup (expr_1 ` (set (pos_r xs))) \<le> n4"
    using expr_1_mon_wrt_pos_r
    using order_trans by blast
  hence "expr_1 (HML_conj (pos_r xs) []) \<le> n4"
    using expr_1.simps(1) Sup_enat_def
    by (metis append_Nil2 image_Un set_append)
  with \<open>Sup (expr_4 ` set xs) \<le> n4\<close> \<open>Sup (expr_4 ` (set ys)) \<le> n4\<close> have 
"Sup ({expr_1 (HML_conj (pos_r xs) [])} \<union> (expr_4 ` (set xs)) \<union> (expr_4 ` (set ys))) \<le> n4"
    by (simp add: Sup_union_distrib)
  thus ?thesis
    using expr_4.simps(2) by simp
qed

lemma expr_4_is:
  fixes n4 and xs and ys and a
  assumes A2: "expr_4 (HML_conj xs ys) \<le> n4 \<Longrightarrow> 
\<forall>x\<in>set xs.(expr_4 x \<le> n4)" and
A3: "expr_4 (HML_conj (a # xs) ys) \<le> n4"
shows "\<forall>x\<in>set (a # xs). expr_4 x \<le> n4"
proof-
  have e4: "expr_4 (HML_conj (a#xs) ys) =
Max ({expr_1 (HML_conj (pos_r (a#xs))[])} \<union> {expr_4 x|x. x \<in> set (a#xs)} \<union> {expr_4 y|y. y \<in> set ys})"
    using expr_4_set by blast
  have fin: "finite ({expr_1 (HML_conj (pos_r (a#xs))[])} \<union> {expr_4 x|x. x \<in> set (a#xs)} \<union> {expr_4 y|y. y \<in> set ys})"
    by simp
  have ne: "({expr_1 (HML_conj (pos_r (a#xs))[])} \<union> {expr_4 x|x. x \<in> set (a#xs)} \<union> {expr_4 y|y. y \<in> set ys}) \<noteq> {}"
    by simp
  with A3 e4 fin have "\<forall>x \<in> ({expr_1 (HML_conj (pos_r (a#xs))[])} \<union> {expr_4 x|x. x \<in> set (a#xs)} \<union> {expr_4 y|y. y \<in> set ys}). x \<le> n4"
    using Max_le_iff 
    by (metis (no_types, lifting))
  then have "\<forall>x \<in> {expr_4 x|x. x \<in> set (a#xs)}. x \<le> n4" by simp
  then show ?thesis by auto
qed

lemma mon_conj:
  fixes n1 and n2 and n3 and n4 and n5 and n6 and xs and ys
  assumes A1: "less_eq_t (expr (HML_conj xs ys)) (n1, n2, n3, n4, n5, n6)"
  shows "(\<forall>x \<in> set xs. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6)) \<and> (\<forall>y \<in> set ys. less_eq_t (expr y) (n1, n2, n3, n4, n5, n6))"
proof(rule conjI)
  show "(\<forall>x \<in> set xs. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6))"
    using A1
  proof(induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    assume A2: "less_eq_t (expr (HML_conj xs ys)) (n1, n2, n3, n4, n5, n6) \<Longrightarrow> 
\<forall>x\<in>set xs.(less_eq_t (expr x) (n1, n2, n3, n4, n5, n6))" and
A3: "less_eq_t (expr (HML_conj (a # xs) ys)) (n1, n2, n3, n4, n5, n6)"
    then show ?case
    proof-
      from A3 have E1_a: "expr_1 a \<le> n1" 
        using dual_order.trans by fastforce
      from A3 have E1_xs: "expr_1 (HML_conj xs ys) \<le> n1"
        using dual_order.trans by fastforce
      from A3 have "1 + Sup ((expr_2 ` (set (a#xs))) \<union> (expr_2 ` (set ys))) \<le> n2"
        using expr_2.simps(1) less_eq_t.simps 
        by simp
      hence "Sup ((expr_2 ` (set (a#xs))) \<union> (expr_2 ` (set ys))) \<le> n2"
        by (metis dual_order.trans ile_eSuc plus_1_eSuc(1))
      hence E2_a: "expr_2 a \<le> n2"
        by simp
      have subs: "(expr_2 ` (set xs)) \<union> (expr_2 ` (set ys)) \<subseteq> 
(expr_2 ` (set (a#xs))) \<union> (expr_2 ` (set ys))"
        by auto
      hence "Sup ((expr_2 ` (set xs)) \<union> (expr_2 ` (set ys))) \<le> Sup ((expr_2 ` (set (a#xs))) \<union> (expr_2 ` (set ys)))"
        using Sup_nat_def by simp
      with \<open>1 + Sup ((expr_2 ` (set (a#xs))) \<union> (expr_2 ` (set ys))) \<le> n2\<close> have
"1 + Sup ((expr_2 ` (set xs)) \<union> (expr_2 ` (set ys))) \<le> n2" 
        by (meson dual_order.trans enat_add_left_cancel_le)
      hence E2_xs: "expr_2 (HML_conj xs ys) \<le> n2"
        using expr_2.simps(1) by force
      from A3 have E3_a: "expr_3 a \<le> n3"
        using dual_order.trans by fastforce
      from A3 have E3_xs: "expr_3 (HML_conj xs ys) \<le> n3"
        using dual_order.trans by fastforce
      from A3 have E5_a: "expr_5 a \<le> n5"
        using dual_order.trans by fastforce
      from A3 have E5_xs: "expr_5 (HML_conj xs ys) \<le> n5" 
        using dual_order.trans by fastforce
      from A3 have E6_a: "expr_6 a \<le> n6"
        using dual_order.trans by fastforce
      from A3 have E6_xs: "expr_6 (HML_conj xs ys) \<le> n6" 
        using dual_order.trans by fastforce
      from A2 E1_xs E2_xs E3_xs E5_xs E6_xs have 
"expr_4 (HML_conj xs ys) \<le> n4 \<Longrightarrow> \<forall>x\<in>set xs. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6)" 
        by simp
      then have dim_4: "expr_4 (HML_conj xs ys) \<le> n4 \<Longrightarrow> \<forall>x\<in>set xs. expr_4 x \<le> n4"
        by simp
      from A3 have E4_a_le:"expr_4 (HML_conj (a#xs) ys) \<le> n4"
        by simp
      with expr_4_conj_le have E4_xs: "expr_4 (HML_conj xs ys) \<le> n4"
        by blast
      from E4_a_le expr_4_is have E4_a: "expr_4 a \<le> n4"
        by (metis dim_4 list.set_intros(1))
      from E4_xs A2 E1_xs E2_xs E3_xs E5_xs E6_xs have "\<forall>x\<in>set xs. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6)"
        by simp
      with E1_a E2_a E3_a E4_a E5_a E6_a show ?thesis by simp
    qed
  qed
next
  show "(\<forall>y \<in> set ys. less_eq_t (expr y) (n1, n2, n3, n4, n5, n6))"
    using A1
  proof(induction ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a ys)
    assume A2: "less_eq_t (expr (HML_conj xs ys)) (n1, n2, n3, n4, n5, n6) \<Longrightarrow> 
\<forall>x\<in>set ys.(less_eq_t (expr x) (n1, n2, n3, n4, n5, n6))" and
A3: "less_eq_t (expr (HML_conj xs (a#ys))) (n1, n2, n3, n4, n5, n6)"
    from A3 have e1_conj: 
"expr_1 (HML_conj xs ys) \<le> n1" 
and e3_conj: "expr_3 (HML_conj xs ys) \<le> n3" 
and e4_conj: "expr_4 (HML_conj xs ys) \<le> n4" 
and e5_conj: "expr_5 (HML_conj xs ys) \<le> n5" 
and e6_conj: "expr_6 (HML_conj xs ys) \<le> n6"
      by simp+
    from A3 have 
e1_a: "expr_1 a \<le> n1"
      and e3_a: "expr_3 a \<le> n3"
      and e4_a: "expr_4 a \<le> n4"
      by simp+
    have "expr_2 (HML_conj xs (a#ys)) = 1 + Sup (expr_2 ` set xs \<union> expr_2 ` set (a#ys))"
      using expr_2.simps
      by simp
    with A3 have le_e2: "... \<le> n2"
      by simp
    hence "Sup (expr_2 ` set xs \<union> expr_2 ` set (a#ys)) \<le> n2"
      by (metis dual_order.trans ile_eSuc plus_1_eSuc(1))
    hence e2_a: "expr_2 a \<le> n2"
      by auto
    have subs: "(expr_2 ` set xs \<union> expr_2 ` set ys) \<subseteq>
(expr_2 ` set xs \<union> expr_2 ` set (a#ys))"
      by auto
    hence "Sup (expr_2 ` set xs \<union> expr_2 ` set ys) \<le> Sup (expr_2 ` set xs \<union> expr_2 ` set (a#ys))"
      using Sup_nat_def by auto
    with le_e2 have "1 + Sup (expr_2 ` set xs \<union> expr_2 ` set ys) \<le> n2"
      using dual_order.trans 
      by force
    hence e2_conj: "expr_2 (HML_conj xs ys) \<le> n2"
      using expr_2.simps(1)
      by simp
    
    from A3 have e5_a: "expr_5 a \<le> n5"
      using expr_5.simps dual_order.trans ile_eSuc 
      by force
    from A3 have e6_a: "expr_6 a \<le> n6"
      using expr_6.simps dual_order.trans ile_eSuc 
      by force
    show ?case 
      using A2 e1_conj e2_conj e3_conj e4_conj e5_conj e6_conj e1_a e2_a e3_a e4_a e5_a e6_a
expr.simps
less_eq_t.simps
      by fastforce
  qed
qed

lemma expr_2_lb: "expr_2 f \<ge> 1"
proof(induction f)
  case (HML_conj x1 x2)
  have subs: "{1} \<subseteq> {1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2}" by simp
  have fin: "finite ({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})" by simp
  have "expr_2 (HML_conj x1 x2) =
Max({1} \<union> {1 + expr_2 x | x. x \<in> set x1} \<union> {1 + expr_2 y | y. y \<in> set x2})"
    by (rule expr_2_set)
  also from subs fin have "... \<ge> Max {1}"
    using Max_mono by blast
  also have "Max {1} = 1" using Lattices_Big.linorder_class.Max_singleton
    by blast
  finally show "expr_2 (HML_conj x1 x2) \<ge> 1" by this
next
  case (HML_poss x1 f)
  then show ?case by simp
qed

subsection \<open>The set of formulas with prices less then or equal to 
(\<infinity>, 1, 0, 0, 0, 0) is a subset of the HML trace subset\<close>

lemma trace_right: 
  assumes "HML_trace \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using assms
proof(induct \<phi> rule:HML_trace.induct)
  case trace_conj
  then show ?case 
    using Sup_enat_def one_enat_def zero_enat_def 
    by auto
next
  case IV: (trace_pos \<phi> \<alpha>)
  then show ?case using HML_trace.cases by fastforce
qed

subsection \<open>The HML trace set is a subset of the set of formulas with prices less then or equal to 
(\<infinity>, 1, 0, 0, 0, 0)\<close>

\<comment> \<open>The set induced by the coordinates (\<infinity>, 1, 0, 0, 0, 0) only includes empty conjunctions\<close>
lemma HML_trace_conj_empty:
  fixes x1 x2
  assumes A1: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, 1, 0, 0, 0, 0)" 
  shows "x1 = [] \<and> x2 = []"
proof-
  have "expr_2 (HML_conj x1 x2) = 1 + Sup ((expr_2 ` (set x1)) \<union> (expr_2 ` (set x2)))"
    using formula_prices_list.expr_2_conj by blast
  with assms have "1 + Sup ((expr_2 ` (set x1)) \<union> (expr_2 ` (set x2))) \<le> 1"
    using expr.simps less_eq_t.simps
    by simp
  hence le_0: "Sup ((expr_2 ` (set x1)) \<union> (expr_2 ` (set x2))) \<le> 0"
    by simp
  hence le_0: "\<forall>x \<in> (expr_2 ` (set x1)). x \<le> 0" "\<forall>x \<in> (expr_2 ` (set x2)). x \<le> 0"
    using Sup_le_iff image_Un UnCI
    by metis+
  have "\<forall>x \<in> (expr_2 ` (set x1)). x \<ge> 1" 
    "\<forall>x \<in> (expr_2 ` (set x2)). x \<ge> 1" using expr_2_lb
    by blast+
  with le_0 show ?thesis using imageI 
    by simp
qed

lemma trace_left:
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  shows "(HML_trace \<phi>)"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from this(3) have "x1 = [] \<and> x2 = []" 
    using HML_trace_conj_empty 
    by blast
  then show ?case
    using trace_conj 
    by blast
next
  case (HML_poss \<alpha> \<psi>)
  hence "HML_trace \<psi>"
    using mon_pos
    by simp
  then show ?case by (rule HML_list.HML_trace.trace_pos)
qed

lemma HML_trace_lemma: 
"(HML_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using trace_left trace_right by blast

lemma simulation_right:
  assumes A1: "HML_simulation \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using A1
proof(induction \<phi> rule:HML_simulation.induct)
  case (sim_pos \<phi>)
  then show ?case
    using trace_right by force
next
  case (sim_conj xs)
  hence "\<forall>x\<in>set xs. expr_5 x \<le> 0" "\<forall>x\<in>set xs. expr_6 x \<le> 0"
    using less_eq_t.simps expr.simps
    by auto
  have "expr_5 (HML_conj xs []) = Sup ((expr_5 ` (set xs)))" 
    using expr_5.simps 
    by auto
  with \<open>\<forall>x\<in>set xs. expr_5 x \<le> 0\<close> have "expr_5 (HML_conj xs []) \<le> 0"
    using Sup_enat_def
    by simp
  have "expr_6 (HML_conj xs []) = Sup (expr_6 ` (set xs))"
    using expr_6.simps
    by auto
  with \<open>\<forall>x\<in>set xs. expr_6 x \<le> 0\<close> have "expr_6 (HML_conj xs []) \<le> 0"
    using Sup_enat_def
    by auto
  with \<open>expr_5 (HML_conj xs []) \<le> 0\<close> show ?case
    using less_eq_t.simps enat_ord_code(3) expr.simps 
    by simp
qed

lemma expr_6_conj:
  assumes "\<Psi> \<noteq> []"
  shows "expr_6 (HML_conj \<Phi> \<Psi>) \<ge> 1"
proof-
  from assms obtain a tail where "\<Psi> = (a#tail)"
    using list.exhaust_sel by blast
  hence "expr_6 (HML_conj \<Phi> \<Psi>) = (Sup ((expr_6 ` (set \<Phi>)) \<union> ((eSuc \<circ> expr_6) ` (set (a#tail)))))"
    using expr_6.simps(2) 
    by blast
  also have "... = (Sup ((expr_6 ` (set \<Phi>)) \<union> {eSuc(expr_6 a)} \<union>((eSuc \<circ> expr_6) ` (set tail))))"
    by simp
  also have "... = sup (eSuc (expr_6 a)) (Sup ((expr_6 ` (set \<Phi>)) \<union>((eSuc \<circ> expr_6) ` (set tail))))"
    using Sup_insert
    by simp
  also have "... \<ge> 1"
    using bot_enat_def eSuc_def
    by (metis eSuc_ile_mono le_supI1 one_eSuc zero_le)
  finally have "expr_6 (HML_conj \<Phi> \<Psi>) \<ge> 1" by this
  thus ?thesis 
    by blast
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
  assumes A1: "(less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" 
shows "x2 = []"
proof(rule ccontr)
  assume "x2 \<noteq> []"
  hence "expr_6 (HML_conj x1 x2) \<ge> 1" 
    using expr_6_conj
    by blast
  from A1 have "expr_6 (HML_conj x1 x2) \<le> 0"
    using expr.simps less_eq_t.simps
    by auto
  with \<open>expr_6 (HML_conj x1 x2) \<ge> 1\<close> show False
    using ile0_eq not_one_le_zero 
    by simp
qed

lemma simulation_left:
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  shows "(HML_simulation \<phi>)"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from this(3) x2_empty have "x2 = []" 
    by blast
  from HML_conj(3) have "\<forall>x \<in> set x1. (less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
    using mon_conj
    by blast
  with HML_conj(1) have "\<forall>x \<in> set x1. HML_simulation x"
    by blast
  then show ?case 
    using \<open>x2 = []\<close> HML_simulation.sim_conj 
    by blast
next
  case (HML_poss x1 \<phi>)
  then show ?case
    by (simp add: sim_pos)
qed

lemma "(HML_simulation \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using simulation_left simulation_right by blast

lemma expr_2_fail:
  assumes A1: "HML_failure (HML_conj [] x2)"
  shows "expr_2 (HML_conj [] x2) \<le> 2"
proof-
  from assms have "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    using HML_failure.simps
    by fastforce
  have "expr_2 (HML_conj [] x2) = 1 + Sup ((expr_2 ` (set x2)))"
    using expr_2.simps
    by simp
  have "\<forall>\<alpha>. expr_2 (HML_poss \<alpha> (HML_conj [] [])) = 1"
    using expr_2.simps Sup_enat_def 
    by auto
  with \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> have "Sup ((expr_2 ` (set x2))) \<le> 1"
    using Sup_enat_def image_iff
    by fastforce
  hence "1 + Sup ((expr_2 ` (set x2))) \<le> 1 + 1"
    using add_left_mono
    by blast
  hence "1 + Sup ((expr_2 ` (set x2))) \<le> 2"
    using one_add_one
    by auto
  thus ?thesis 
    using \<open>expr_2 (HML_conj [] x2) = 1 + Sup ((expr_2 ` (set x2)))\<close> 
    by simp
qed

lemma expr_3_fail:
  assumes "HML_failure (HML_conj [] x2)" 
  shows "expr_3 (HML_conj [] x2) \<le> 0"
proof-
  from assms have "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    using HML_failure.simps
    by fastforce
  have e3: "expr_3 (HML_conj [] x2) = Sup (expr_3 ` (set x2))"
    using expr_3.simps
    by simp
  have "\<forall>\<alpha>. expr_3 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_3.simps Sup_enat_def 
    by auto
  with \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> have "\<forall>x \<in> (expr_3 ` (set x2)). x \<le> 0"
    using image_iff
    by fastforce
  hence "Sup (expr_3 ` (set x2)) \<le> 0"
    using Sup_enat_def Sup_le_iff
    by fastforce
  with e3 show ?thesis by simp
qed

lemma expr_4_fail:
  assumes
A1: "HML_failure (HML_conj [] x2)" 
shows "expr_4 (HML_conj [] x2) \<le> 0"
proof-
  from assms have "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    using HML_failure.simps
    by fastforce
  have e4: "expr_4 (HML_conj [] x2) = Sup (expr_4 ` (set x2))"
    using expr_4.simps
    by simp
  have "\<forall>\<alpha>. expr_4 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_4.simps Sup_enat_def
    by auto
  with \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> have "\<forall>x \<in> (expr_4 ` (set x2)). x \<le> 0"
    using image_iff
    by fastforce
  hence "Sup (expr_4 ` (set x2)) \<le> 0"
    using Sup_le_iff Sup_enat_def
    by fastforce
  with e4 show ?thesis
    by simp
qed

lemma expr_5_fail:
assumes "HML_failure (HML_conj [] x2)" 
shows "expr_5 (HML_conj [] x2) \<le> 1"
proof-
  from assms have "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    using HML_failure.simps
    by fastforce 
  have e5: "expr_5 (HML_conj [] x2) = (Sup ((expr_5 ` (set x2)) \<union> (expr_1 ` (set x2))))"
    using expr_5.simps
    by simp
  have "\<forall>\<alpha>. expr_5 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_5.simps Sup_enat_def
    by fastforce
  with \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> have "\<forall>x \<in> set x2. expr_5 x = 0"
    by fastforce 
  have "\<forall>\<alpha>. expr_1 (HML_poss \<alpha> (HML_conj [] [])) = 1"
    using expr_1.simps Sup_enat_def
    by fastforce
  with \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> have "\<forall>x \<in> set x2. expr_1 x = 1"
    by fastforce
  hence "(Sup ((expr_5 ` (set x2)) \<union> (expr_1 ` (set x2)))) \<le> 1" using \<open>\<forall>x \<in> set x2. expr_5 x = 0\<close>
    using Sup_enat_def image_iff Sup_le_iff
    by fastforce
  then show ?thesis using e5 by simp
qed

lemma expr_6_fail:
assumes "HML_failure (HML_conj [] x2)"
shows "expr_6 (HML_conj [] x2) \<le> 1"
proof-
  from assms have "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    using HML_failure.simps
    by fastforce
  have e6: "expr_6 (HML_conj [] x2) = (Sup ((eSuc \<circ> expr_6) ` (set x2)))"
    using expr_6.simps
    by simp
  have "\<forall>\<alpha>. expr_6 (HML_poss \<alpha> (HML_conj [] [])) = 0"
    using expr_6.simps Sup_enat_def
    by fastforce
  find_theorems eSuc
  hence "(Sup ((eSuc \<circ> expr_6) ` (set x2))) \<le> 1" 
    using \<open>\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])\<close> Sup_enat_def image_iff Sup_le_iff one_eSuc
    by fastforce
  then show ?thesis using e6 by simp
qed

lemma failure_right:
  assumes A1: "HML_failure \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using A1
proof(induction \<phi> rule:HML_failure.induct)
  case (trace \<psi> \<alpha>)
  then show ?case
    by simp
next
  case (neg x2)
  assume "\<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  hence "(HML_failure (HML_conj ([]::'a formula_list list) x2))"
    using HML_failure.neg by blast
  then show ?case using expr_2_fail expr_3_fail expr_4_fail expr_5_fail expr_6_fail
less_eq_t.simps expr.simps
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

lemma failure_x1_empty:
  fixes x1 x2
  assumes A1: "conj_flattened (HML_conj x1 x2)" and A2: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, 2, 0, 0, 1, 1)"
shows "x1 = []"
proof(rule ccontr)
    assume A3: "x1 \<noteq> []"
    then have A4: "\<exists>x. x \<in> set x1"
      using ex_in_conv by blast
    from A2 have e3_eq_0: "expr_3 (HML_conj x1 x2) \<le> 0"
      by (metis expr.simps less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
    have eq: "expr_3 (HML_conj x1 x2) =
Max({0} \<union> {expr_3 x | x. x \<in> set x1} \<union> {expr_3 y | y. y \<in> set x2} \<union> {expr_1 x | x. x \<in> set x1})"
      by (rule expr_3_set)
    from conj_flattened_alt A1 have 
"(\<forall>x\<in>set x1. \<exists>\<alpha> x11. x = HML_poss \<alpha> x11)"
      by metis
    then have fa_x1: "\<forall>x \<in>set x1. expr_1 x \<ge> 1" 
      by auto
    from A3 have ne: "{expr_1 x | x. x \<in> set x1} \<noteq> {}"
      by simp
    have fin: "finite {expr_1 x | x. x \<in> set x1}" by simp
    from fin ne fa_x1 have ge_1: "Max {expr_1 x | x. x \<in> set x1} \<ge> 1"
      by (smt (verit, best) Collect_empty_eq Max_ge_iff mem_Collect_eq)
    have subs: "{expr_1 x | x. x \<in> set x1} \<subseteq> 
{0} \<union> {expr_3 x | x. x \<in> set x1} \<union> {expr_3 y | y. y \<in> set x2} \<union> {expr_1 x | x. x \<in> set x1}"
      by auto
    have fin: 
"finite ({0} \<union> {expr_3 x | x. x \<in> set x1} \<union> {expr_3 y | y. y \<in> set x2} \<union> {expr_1 x | x. x \<in> set x1})"
      by simp
    from subs fin ge_1 have 
"Max ({0} \<union> {expr_3 x | x. x \<in> set x1} \<union> {expr_3 y | y. y \<in> set x2} \<union> {expr_1 x | x. x \<in> set x1})
\<ge> 1"
      by (metis (no_types, lifting) Max_ge_iff UnCI Un_empty finite_subset ne)
    from this eq have "expr_3 (HML_conj x1 x2) \<ge> 1" 
      by simp
    from this e3_eq_0 show False 
      by simp
  qed


lemma failure_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))" and A2: "conj_flattened \<phi>"
  shows "HML_failure \<phi>"
  using A1 A2
proof(induction \<phi>)
  case (HML_conj x1 x2)
  from A2 have x1_e: "x1 = []"
    using HML_conj(3) HML_conj.prems(2) failure_x1_empty by blast
  have "x2 = [] \<or> x2 \<noteq> []"
    by simp
  then show ?case
  proof
    assume "x2 = []"
    from this x1_e show ?thesis
      using empty_conj by auto
  next
    assume "x2 \<noteq> []"
    from mon_conj have fa_le: "(\<forall>y\<in>set x2. less_eq_t (expr y) (\<infinity>, 2, 0, 0, 1, 1))"
      using HML_conj.prems(1) by blast
    then have e5: "(\<forall>y\<in>set x2. (expr_5 y) \<le> 1)"
      by (metis expr.simps less_eq_t.simps of_nat_1 of_nat_eq_enat of_nat_le_iff)
    have e5_set: "expr_5 (HML_conj x1 x2) = 
Max(  {0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2})"
      by (rule formula_prices_list.expr_5_set)
    have "expr_5 (HML_conj x1 x2) \<le> 1"
      by (metis HML_conj.prems(1) expr.simps less_eq_t.simps of_nat_1 of_nat_eq_enat of_nat_le_iff)
    from this e5_set have 
le_1: "Max({0} \<union> {expr_5 x | x. x \<in> set x1} \<union> {expr_5 y | y. y \<in> set x2} \<union> {expr_1 y | y. y \<in> set x2}) \<le>
1" 
      by simp
    have ne: "{expr_1 y | y. y \<in> set x2} \<noteq> {}"
      by (simp add: \<open>x2 \<noteq> []\<close>)
    from le_1 ne have "Max {expr_1 y | y. y \<in> set x2} \<le> 1" 
    by simp
  from this ne have e1: "\<forall>y \<in> set x2. expr_1 y \<le> 1" by auto
  have fa_pos: "(\<forall>x\<in>set x2. \<exists>\<alpha> x11. x = HML_poss \<alpha> x11)"
    using HML_conj.prems(2) conj_flattened_alt by blast
  have x2_empty_conj: "\<forall>y \<in> set x2. (\<exists>\<alpha> x11. y = HML_poss \<alpha> (HML_conj [] []))" 
  proof(rule ballI)
    fix y
    assume "y \<in> set x2"
    show "\<exists>\<alpha> x11. y = HML_poss \<alpha> (HML_conj [] [])"
    proof-
      from fa_pos have "\<exists>\<alpha> x11. y = HML_poss \<alpha> x11"
        using \<open>y \<in> set x2\<close> by fastforce
      then obtain \<alpha> x11 where A3: "y = HML_poss \<alpha> x11" by auto
      from A3 have "expr_1 y = expr_1 (HML_poss \<alpha> x11)"
        by simp
      from this e1 have "expr_1 (HML_poss \<alpha> x11) \<le> 1"
        using \<open>y \<in> set x2\<close> by fastforce
      have "expr_1 (HML_poss \<alpha> x11) = 1 + (expr_1 x11)" 
        by simp
      then have expr_1_x11: "expr_1 x11 \<le> 0"
        using \<open>expr_1 (HML_poss \<alpha> x11) \<le> 1\<close> by auto
      then have "x11 = HML_conj [] []" 
        proof(cases x11)
          case (HML_conj x111 x122)
          have expr_1_conj: "expr_1 (HML_conj x111 x122) \<le> 0"
            using HML_conj \<open>expr_1 x11 \<le> 0\<close> by blast
          have "conj_flattened (HML_conj x111 x122)"
            by (metis A3 HML_conj HML_conj.prems(2) \<open>y \<in> set x2\<close> conj_flattened.simps(1) conj_flattened.simps(2))
          then have "((\<forall>x \<in> set x111. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x) \<and> 
(\<forall>x \<in> set x122. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x))"
            using conj_flattened_alt by blast
          then have fa_poss:
"(\<forall>x \<in> set x111. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> (\<forall>x \<in> set x122. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>)))"
            by simp
          then have fa_poss_x122: "(\<forall>x \<in> set x122. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>))"
            using \<open>(\<forall>x\<in>set x111. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x) \<and> (\<forall>x\<in>set x122. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x)\<close> by blast
          from fa_poss have fa_poss_x111:"(\<forall>x \<in> set x111. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>))"
            using \<open>(\<forall>x\<in>set x111. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x) \<and> (\<forall>x\<in>set x122. (\<exists>\<alpha> \<phi>. x = HML_poss \<alpha> \<phi>) \<and> conj_flattened x)\<close> by blast
          have expr_1_eq: "expr_1 (HML_conj x111 x122) =
Max({0} \<union> {expr_1 x | x. x \<in> set x111} \<union> {expr_1 y | y. y \<in> set x122})" 
            by (rule formula_prices_list.expr_1_set_form)
          from this expr_1_conj have 
expr_1_eq: "Max ({0} \<union> {expr_1 x |x. x \<in> set x111} \<union> {expr_1 y |y. y \<in> set x122}) \<le> 0" 
            by simp
          have fin: "finite ({0} \<union> {expr_1 x | x. x \<in> set x111} \<union> {expr_1 y | y. y \<in> set x122})"
            by simp
          from expr_1_eq  show ?thesis 
proof(cases x111)
  case Nil
  have x111_e: "x111 = []" by (rule local.Nil)
  then show ?thesis 
  proof(cases x122)
    case Nil
    from this x111_e show ?thesis
      using HML_conj by fastforce
  next
    case (Cons a list)
    from this have ne: "{expr_1 y | y. y \<in> set x122} \<noteq> {}" 
      by auto
    from this expr_1_eq fin have "Max {expr_1 y | y. y \<in> set x122} \<le> 
Max ({0} \<union> {expr_1 x |x. x \<in> set x111} \<union> {expr_1 y |y. y \<in> set x122})"
      by (meson Max_mono sup_ge2)
    from this expr_1_eq have le_0: "Max {expr_1 y | y. y \<in> set x122} \<le> 0" 
      by simp
    from local.Cons fa_poss_x122 have "(\<exists>\<alpha> \<phi>. a = HML_poss \<alpha> \<phi>)" 
      by simp
    then obtain \<alpha> \<phi> where a_eq: "a = HML_poss \<alpha> \<phi>" 
      by auto
    then have "expr_1 a = 1 + expr_1 \<phi>" 
      by simp
    then have "expr_1 a \<ge> 1" 
      by simp
    from this ne local.Cons have "Max {expr_1 y | y. y \<in> set x122} \<ge> 1"
      by (metis (mono_tags, lifting) Max_ge_iff fin finite_Un list.set_intros(1) mem_Collect_eq)
    from this le_0 have False 
      by simp
    then show ?thesis by simp
  qed
next
  case (Cons a list)
    from this have ne: "{expr_1 y | y. y \<in> set x111} \<noteq> {}" 
      by auto
    from this fin have "Max {expr_1 y | y. y \<in> set x111} \<le> 
Max ({0} \<union> {expr_1 x |x. x \<in> set x111} \<union> {expr_1 y |y. y \<in> set x122})" 
      by simp
    from this expr_1_eq have le_0: "Max {expr_1 y | y. y \<in> set x111} \<le> 0" 
      by simp
    from local.Cons fa_poss_x111 have "(\<exists>\<alpha> \<phi>. a = HML_poss \<alpha> \<phi>)" 
      by simp
    then obtain \<alpha> \<phi> where a_eq: "a = HML_poss \<alpha> \<phi>" 
      by auto
    then have "expr_1 a = 1 + expr_1 \<phi>" 
      by simp
    then have "expr_1 a \<ge> 1" 
      by simp
    from this ne local.Cons have "Max {expr_1 y | y. y \<in> set x111} \<ge> 1"
      by (metis (mono_tags, lifting) Max_ge_iff fin finite_Un list.set_intros(1) mem_Collect_eq)
    from this le_0 have False 
      by simp
  then show ?thesis by simp
qed
        next
          case (HML_poss x21 x22)
          then have le_0: "expr_1 (HML_poss x21 x22) \<le> 0"
            using \<open>expr_1 x11 \<le> 0\<close> by blast
          have "expr_1 (HML_poss x21 x22) =
1 + expr_1 x22"
            by simp
          from this le_0 have False
            by simp
          then show ?thesis by simp
        qed
      then show ?thesis
        using A3 by blast
    qed
  qed 
  have "(\<forall>y \<in> (set x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<and> x1 = []) \<Longrightarrow> 
HML_failure (HML_conj x1 x2)"
    by (simp add: neg x1_e)
  from this x1_e x2_empty_conj show ?case 
    by simp
qed
next
  case (HML_poss x1 \<phi>)
  then show ?case
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
proof(cases \<phi>)
  case (HML_conj x11 x12)
  then show ?thesis
  proof-
    from A1 have A3: "\<forall>x \<in> set x11. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])"
      by (metis HML_conj HML_readiness.cases formula_list.distinct(1) formula_list.inject(1))
    from A1 have A4: "\<forall>y \<in> set x12. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])" 
      by (metis HML_conj HML_readiness.cases formula_list.distinct(1) formula_list.inject(1))
    have expr_4_poss_0: "\<forall>\<alpha>. expr_4 (HML_poss \<alpha> (HML_conj [] [])) = 0" 
      by simp
    from this A3 have x11_0: "\<forall>x\<in>set x11. \<exists>\<alpha>. expr_4 x = 0" 
      by auto
    from expr_4_poss_0 A4 have x12_0: "\<forall>y \<in> set x12. \<exists>\<alpha>. expr_4 y = 0" 
      by auto
    have e1_0: "expr_1 (HML_conj (pos_r x11)[]) \<le> 1"
      using A3 expr_1_conj_pos_r by fastforce
    then have e1_0: "Max {expr_1 (HML_conj (pos_r x11)[])} \<le> 1" 
      by simp
    have "expr_4 (HML_poss \<alpha> (HML_conj x11 x12)) = 
expr_4 (HML_conj x11 x12)" 
      by simp
      also have "... = 
Max ({expr_1 (HML_conj (pos_r x11)[])} \<union> {expr_4 x|x. x \<in> set x11} \<union> {expr_4 y|y. y \<in> set x12})"
        by (rule formula_prices_list.expr_4_set)
      also from x11_0 x12_0 e1_0 have "... \<le> 1" 
        by auto
      finally have "expr_4 (HML_poss \<alpha> (HML_conj x11 x12)) \<le> 1"
        by this
      then show ?thesis
        using HML_conj by blast
  qed
next
  case (HML_poss x21 x22)
  then show ?thesis
    by (metis A2 expr.simps expr_4.simps(1) less_eq_t.simps of_nat_1 of_nat_eq_enat of_nat_le_iff)
qed

lemma readiness_right:
  assumes A1: "HML_readiness \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using A1
proof(induction \<phi>)
  case (read_pos \<phi> \<alpha>)
  then show ?case 
  proof-
    assume A2: "less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1)"
    then show "less_eq_t (expr (HML_poss \<alpha> \<phi>)) (\<infinity>, 2, 1, 1, 1, 1)"
    proof-
      have A3: "expr_4 (HML_poss \<alpha> \<phi>) \<le> 1"
        by (metis expr.simps expr_4.simps(1) less_eq_t.simps local.read_pos(2) of_nat_1 of_nat_eq_enat of_nat_le_iff)
      show ?thesis
        by (metis A2 A3 enat_ord_simps(1) enat_ord_simps(3) expr.simps formula_prices_list.expr_2_pos formula_prices_list.expr_3_pos formula_prices_list.expr_5_pos formula_prices_list.expr_6_pos less_eq_t.simps one_enat_def)
    qed
  qed
    next
      case (read_conj xs ys)
      from read_conj have e1_xs: "(\<forall>x\<in>set xs. expr_1 x \<le> 1)"
        by auto
      from read_conj have e1_ys: "(\<forall>x\<in>set ys. expr_1 x \<le> 1)"
        by auto
      from read_conj have e1: "expr_1 (HML_conj xs ys) \<le> \<infinity>"
        by simp
      from read_conj have e2_xs: "(\<forall>x\<in>set xs. expr_2 x = 1)"
        by auto
      from read_conj have e2_ys: "(\<forall>x\<in>set ys. expr_2 x \<le> 1)" 
        by auto
      from read_conj formula_prices_list.expr_2_set have "expr_2 (HML_conj xs ys) =
Max({1} \<union> {1 + expr_2 x | x. x \<in> set xs} \<union> {1 + expr_2 y | y. y \<in> set ys})"
        by simp
      also from e2_xs e2_ys this have "... \<le> 2" 
        by auto
      finally have e2: "expr_2 (HML_conj xs ys) \<le> 2" by this
      from read_conj have e3_xs: "(\<forall>x\<in>set xs. expr_3 x \<le> 1)"
        by auto
      from read_conj have e3_ys: "(\<forall>x\<in>set ys. expr_3 x \<le> 1)" 
        by auto
      have e3: "expr_3 (HML_conj xs ys) =
Max({0} \<union> {expr_3 x | x. x \<in> set xs} \<union> {expr_3 y | y. y \<in> set ys} \<union> {expr_1 x | x. x \<in> set xs})"
        by (rule formula_prices_list.expr_3_set)
      also from e3_xs e3_ys read_conj have "... \<le> 1"
        by auto
      finally have e3: "expr_3 (HML_conj xs ys) \<le> 1" by this
      from read_conj have e4_xs: "(\<forall>x\<in>set xs. expr_4 x \<le> 1)" 
        by auto
      from read_conj have e4_ys: "(\<forall>x\<in>set ys. expr_4 x \<le> 1)"
        by auto
      from e1_xs e2_ys expr_1_conj_pos_r have e1_pos_r: "expr_1 (HML_conj (pos_r xs)[]) \<le> 1" 
        by fastforce
      have e4: "expr_4 (HML_conj xs ys) =
Max ({expr_1 (HML_conj (pos_r xs)[])} \<union> {expr_4 x|x. x \<in> set xs} \<union> {expr_4 y|y. y \<in> set ys})"
        by (rule formula_prices_list.expr_4_set)
      also from e4_xs e4_ys read_conj e1_pos_r have "... \<le> 1"
        by auto
      finally have e4: "expr_4 (HML_conj xs ys) \<le> 1" 
        by this
      from read_conj have e5_xs: "(\<forall>x\<in>set xs. expr_5 x \<le> 1)"
        by auto
      from read_conj have e5_ys: "(\<forall>x\<in>set ys. expr_5 x \<le> 1)"
        by auto
      have "expr_5 (HML_conj xs ys) =
Max({0} \<union> {expr_5 x | x. x \<in> set xs} \<union> {expr_5 y | y. y \<in> set ys} \<union> {expr_1 y | y. y \<in> set ys})"
        by (rule formula_prices_list.expr_5_set)
      also from e5_xs e5_ys e1_ys read_conj have "... \<le> 1" 
        by auto
      finally have e5: "expr_5 (HML_conj xs ys) \<le> 1"
        by this
      from read_conj have e6_xs: "(\<forall>x\<in>set xs. expr_6 x \<le> 1)" 
        by auto
      from read_conj have e6_ys: "(\<forall>x\<in>set ys. expr_6 x \<le> 0)"
        by auto
      have "expr_6 (HML_conj xs ys) =
Max({0} \<union> {expr_6 x | x. x \<in> set xs} \<union> {1 + expr_6 y | y. y \<in> set ys})" 
        by (rule HML_subsets.expr_6_union_neg)
      also from e6_xs e6_ys read_conj have "... \<le> 1" 
        by auto
      finally have e6: "expr_6 (HML_conj xs ys) \<le> 1"
        by this
      from e1 e2 e3 e4 e5 e6 show "less_eq_t (expr (HML_conj xs ys)) (\<infinity>, 2, 1, 1, 1, 1)"
        by (simp add: numeral_eq_enat one_enat_def)
        from read_conj have e1_ys: "(\<forall>x\<in>set ys. expr_1 x \<le> 1)"
        by auto
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
