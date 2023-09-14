theory HML_subsets
  imports 
    "HOL-Library.Extended_Nat"
    Main
    HML_list
  formula_prices_list
begin


fun less_eq_t :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> bool"
  where
"less_eq_t (n1, n2, n3, n4, n5, n6) (i1, i2, i3, i4, i5, i6) =
    (n1 \<le> i1 \<and> n2 \<le> i2 \<and> n3 \<le> i3 \<and> n4 \<le> i4 \<and> n5 \<le> i5 \<and> n6 \<le> i6)"

thm HML_trace.induct

(*Done*)
lemma mon_pos:
  fixes n1 and n2 and n3 and n4::nat and n5 and n6 and \<phi> and \<alpha>
  assumes A1: "less_eq_t (expr (HML_poss \<alpha> \<phi>)) (n1, n2, n3, n4, n5, n6)"
  shows "less_eq_t (expr \<phi>) (n1, n2, n3, n4, n5, n6)" 
using A1
proof(cases \<phi>)
  case (HML_conj x11 x12)
  assume A2: "\<phi> = HML_conj x11 x12"
  then show ?thesis
  proof-
    from A1 have E1: "expr_1 \<phi> \<le> n1"
      by (simp add: Suc_ile_eq order_less_imp_le)
    from A1 have E2: "expr_2 \<phi> \<le> n2" by simp
    from A1 have E3: "expr_3 \<phi> \<le> n3" by simp
    from A1 have E4: "expr_4 \<phi> \<le> n4" by simp
    from A1 have E5: "expr_5 \<phi> \<le> n5" by simp
    from A1 have E6: "expr_6 \<phi> \<le> n6" by simp
    from A1 E1 E2 E3 E4 E5 E6 show ?thesis by simp
  qed
next
  case (HML_poss x21 x22)
  assume A2: "\<phi> = HML_poss x21 x22"
  then show ?thesis 
  proof- 
    from A1 have E1: "expr_1 \<phi> \<le> n1"
      by (smt (z3) eSuc_enat expr.simps formula_prices_list.expr_1_pos ile_eSuc less_eq_t.simps old.prod.case order.trans plus_1_eq_Suc)
    from A1 E1 show ?thesis by simp
  qed
qed

(*Done*)
lemma expr_1_union:
  shows "expr_1 (HML_conj as bs) = Max ({0} \<union> {expr_1 x |x. x \<in> set as} \<union> {expr_1 (HML_conj [] bs)})"
proof(induction as arbitrary: bs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
  proof-
    assume A1: "(\<And>bs. expr_1 (HML_conj xs bs) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set xs} \<union> {expr_1 (HML_conj [] bs)}))"
    then show "expr_1 (HML_conj (x # xs) bs) = 
Max ({0} \<union> {expr_1 xa |xa. xa \<in> set (x # xs)} \<union> {expr_1 (HML_conj [] bs)})"
    proof-
      have A2: "{expr_1 xa |xa. xa \<in> set (x # xs)} = {expr_1 x} \<union> {expr_1 xa |xa. xa \<in> set xs}"
        by auto
    have "expr_1 (HML_conj (x # xs) bs) = Max ({0} \<union> {expr_1 (HML_conj (x # xs) bs)})"
      by simp
    also have "... = Max ({expr_1 (HML_conj (x # xs) bs)})"
      by simp
    also have "... = Max ({0} \<union> {expr_1 x} \<union> {expr_1 (HML_conj xs bs)})"
      by simp
    also have "... = Max({expr_1 x} \<union> {expr_1 (HML_conj xs bs)})"
      by simp
    also from A1 have "... = Max({expr_1 x} \<union> {Max({0} \<union> {expr_1 x |x. x \<in> set xs} \<union> {expr_1 (HML_conj [] bs)})})"
      by simp
    also from A2 have "... =  Max ({0} \<union> {expr_1 xa |xa. xa \<in> set (x # xs)} \<union> {expr_1 (HML_conj [] bs)})"
      by simp
    finally show E1: "expr_1 (HML_conj (x # xs) bs) = Max ({0} \<union> {expr_1 xa |xa. xa \<in> set (x # xs)} \<union> {expr_1 (HML_conj [] bs)})"
      by this
    qed
  qed
qed
(*Done*)
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

(*Done*)
(*Done*)
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

(*Done*)
lemma pos_r_1:
  assumes A1: "\<forall>x\<in>set xs. expr_1 x < expr_1 a"
  shows "pos_r (a#xs) = xs"
  using A1
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  assume A1: "\<forall>x\<in>set xs. expr_1 x < expr_1 a \<Longrightarrow> pos_r (a # xs) = xs" and
A2: "\<forall>x\<in>set (x # xs). expr_1 x < expr_1 a"
  define max_val_xs where "max_val_xs = Max (set (map (\<lambda>x. expr_1 x) (a#xs)))"
  define xs_new_xs where "xs_new_xs = filter (\<lambda>y. expr_1 y < max_val_xs) (a#xs)"
  define max_val where "max_val = Max (set (map (\<lambda>x. expr_1 x) (a#x#xs)))"
  define xs_new where "xs_new = filter (\<lambda>y. expr_1 y < max_val) (a#x#xs)"
  from A2 have "\<forall>x\<in>set xs. expr_1 x < expr_1 a"
    by simp
  from this have A3: "pos_r (a # xs) = xs" 
    by (rule A1)
  have pos_r_xs_def: "pos_r (a # xs) = xs_new_xs"
    by (metis max_val_xs_def pos_r.simps(2) xs_new_xs_def)
  from this A3 xs_new_xs_def have "xs = filter (\<lambda>y. expr_1 y < max_val_xs) (a # xs)"
    by simp

  have pos_r_def: "pos_r (a # x # xs) = xs_new"
    by (metis max_val_def pos_r.simps(2) xs_new_def)
  have A2: "set (map (\<lambda>x. expr_1 x) (a#x#xs)) = {expr_1 y|y. y \<in> set (a#x#xs)}"
    by auto
  also have A3:"... = {expr_1 a} \<union> {expr_1 y|y. y \<in> set (x#xs)}"
    by auto
  from A2 have "Max ({expr_1 a} \<union> {expr_1 y|y. y \<in> set (x#xs)}) = expr_1 a"
    by (smt (verit, best) Cons.prems List.finite_set Max_ge Max_in A3 empty_iff insert_iff insert_is_Un linorder_not_le mem_Collect_eq)
  from this A2 have "max_val = expr_1 a"
    using A3 max_val_def by presburger
  then have X: "xs_new = filter (\<lambda>y. expr_1 y < expr_1 a) (a#x#xs)"
    using xs_new_def by blast
   have "filter (\<lambda>y. expr_1 y < expr_1 a) (a#x#xs) = (x#xs)"
     by (simp add: Cons.prems)
   from this X have "xs_new = x # xs"
     by simp
   from pos_r_def this show ?case by (rule HOL.back_subst)
 qed

(*Done*)

(*Done*)
lemma pos_r_2:
  assumes A1: "(\<exists>x\<in>set xs. expr_1 a < expr_1 x)"
  shows "set (pos_r (a#xs)) = set (pos_r (xs)) \<union> {a}"
  using A1
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case 
    by (smt (verit, ccfv_SIG) List.finite_set Max_ge Max_in Un_insert_right dual_order.trans empty_iff filter.simps(2) filter_cong image_eqI insert_iff linorder_not_le list.map(2) list.set(2) list.set_map pos_r.simps(2) sup_bot.right_neutral)
qed

(*Done*)

(*Done*)
lemma pos_r_3:
  assumes A1: "(\<exists>x\<in>set xs. expr_1 a = expr_1 x) \<and> (\<forall>x\<in>set xs. expr_1 x \<le> expr_1 a)"
  shows "set (pos_r (a#xs)) = set (pos_r xs)"
  using A1
proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  assume A1: "(\<exists>x\<in>set xs. expr_1 a = expr_1 x) \<and> (\<forall>x\<in>set xs. expr_1 x \<le> expr_1 a) \<Longrightarrow>
    set (pos_r (a # xs)) = set (pos_r xs)" and
A2: "(\<exists>x\<in>set (x # xs). expr_1 a = expr_1 x) \<and> (\<forall>x\<in>set (x # xs). expr_1 x \<le> expr_1 a)"
  define max_val_xs where "max_val_xs = Max (set (map (\<lambda>x. expr_1 x) (a#xs)))"
  define xs_new_xs where "xs_new_xs = filter (\<lambda>y. expr_1 y < max_val_xs) (a#xs)"
  define max_val where "max_val = Max (set (map (\<lambda>x. expr_1 x) (a#x#xs)))"
  define xs_new where "xs_new = filter (\<lambda>y. expr_1 y < max_val) (a#x#xs)"
  from A2 have A3: "(\<forall>x\<in>set xs. expr_1 x \<le> expr_1 a)" 
    by simp
  have "{expr_1 x | x. x \<in> set (a#xs)} = ({expr_1 x | x. x \<in> set xs} \<union> {expr_1 a})"
    by auto
  then have expr_a_in: "expr_1 a \<in> {expr_1 x | x. x \<in> set (a#xs)}"
    by simp
  from A2 have "expr_1 x < expr_1 a \<or> expr_1 x = expr_1 a" 
    by auto
  then show ?case 
  proof(rule disjE)
    assume A4: "expr_1 x = expr_1 a"
    from A3 A4 have "(\<forall>y\<in>set (a#xs). expr_1 y \<le> expr_1 x)" 
      by simp
    from this A4 have "(\<forall>y \<in> {expr_1 x | x. x \<in> set (a#xs)}. y \<le> expr_1 a)" 
      by auto
    then have A5: "(\<And>y. y \<in> {expr_1 x | x. x \<in> set (a#xs)} \<Longrightarrow> y \<le> expr_1 a)"
      by simp
    have "finite ({expr_1 x | x. x \<in> set (a#xs)})" 
      by simp
    thm Max_eqI
    from this A5 expr_a_in have max_val_a: "Max({expr_1 x | x. x \<in> set (a#xs)}) = expr_1 a" 
      by (rule Max_eqI)
    have "set (map (\<lambda>x. expr_1 x) (a#xs)) = {expr_1 x | x. x \<in> set (a#xs)}" 
      by auto
    then have "max_val_xs = Max({expr_1 x | x. x \<in> set (a#xs)})" using max_val_xs_def
      by simp
    from this max_val_a have "max_val_xs = expr_1 a" 
      by simp
    from this A4 have max: "max_val_xs = expr_1 x"
      by simp

    have fin_2: "finite ({expr_1 y | y. y \<in> set (a#x#xs)})"
      by simp
    have "{expr_1 y | y. y \<in> set (a#x#xs)} = {expr_1 y | y. y \<in> set (x#xs)} \<union> {expr_1 a}"
      by auto
    then have a_in: "expr_1 a \<in> {expr_1 y | y. y \<in> set (a#x#xs)}"
      by auto
    from A3 A4 have "\<forall>x\<in>set (a#x#xs). expr_1 x \<le> expr_1 a"
      by simp
    then have fa_le: "(\<And>y. y \<in> {expr_1 z | z. z \<in> set (a#x#xs)} \<Longrightarrow> y \<le> expr_1 a)"
      by auto
    from fin_2 fa_le a_in have max_2: "Max({expr_1 y | y. y \<in> set (a#x#xs)}) = expr_1 a"
      by (rule Max_eqI)
    from max_2 A3 have "Max({expr_1 y | y. y \<in> set (a#x#xs)}) = expr_1 x"
      using A4 by presburger
    have "set (map (\<lambda>x. expr_1 x) (a#x#xs)) = {expr_1 y | y. y \<in> set (a#x#xs)}" 
      by auto
    then have "max_val = Max({expr_1 y | y. y \<in> set (a#x#xs)})"
      using max_val_def by presburger
    from this A3 A4 max_2 have "max_val = expr_1 a"
      by simp
    from this A4 have max_2: "max_val = expr_1 x"
      by simp
    from this max have max_eq: "max_val = max_val_xs"
      by simp
    from max_2 have "filter (\<lambda>y. expr_1 y < max_val) (a#x#xs) = filter (\<lambda>y. expr_1 y < expr_1 x) (a#x#xs)"
      by simp
    also have xs_new_1: "... = filter (\<lambda>y. expr_1 y < expr_1 x) (a#xs)"
      by simp
    finally have xs_new_1: "filter (\<lambda>y. expr_1 y < max_val) (a#x#xs) =filter (\<lambda>y. expr_1 y < expr_1 x) (a#xs)"
      by this
    from max have "filter (\<lambda>y. expr_1 y < max_val_xs) (a#xs) = filter (\<lambda>y. expr_1 y < expr_1 x) (a#xs)"
      by simp
    from this xs_new_1 have "filter (\<lambda>y. expr_1 y < max_val) (a#x#xs) = filter (\<lambda>y. expr_1 y < max_val_xs) (a#xs)"
      by simp
    then have pos_eq: "xs_new = xs_new_xs"
      using xs_new_def xs_new_xs_def by blast
    have A11: "pos_r(a #x #xs) = xs_new"
      by (metis max_val_def pos_r.simps(2) xs_new_def)
    have "pos_r(a#xs) = xs_new_xs" 
      by (metis max_val_xs_def pos_r.simps(2) xs_new_xs_def)
    from this A11 pos_eq have "pos_r(a#x#xs) = pos_r(a#xs)" 
      by simp
    then show ?thesis
      using A4 \<open>max_val_xs \<equiv> Max (set (map expr_1 (a # xs)))\<close> max by force
  next
    assume A4: "expr_1 x < expr_1 a"
    from A2 have A5: "(\<exists>x\<in>set (x # xs). expr_1 a = expr_1 x)" 
      by simp
    from A5 A4 have A6: "(\<exists>x\<in>set xs. expr_1 a = expr_1 x)"
      by simp
    from this obtain y where A7: "y \<in> set xs" and A8: "expr_1 a = expr_1 y" by (rule bexE)
    thm Max_eqI
    from A3 A8 A4 have x_xs: "\<forall>x \<in> set (x#xs). expr_1 x \<le> expr_1 y" 
      by simp
    from A4 A8 have x_y: "expr_1 x < expr_1 y"
      by simp
    from A7 have y_in: "y \<in> set (x#xs)" 
      by simp
    have "finite ({expr_1 y|y. y \<in> set (x#xs)})"
      by simp
    from this x_xs y_in Max_eqI have max_x_xs: "Max {expr_1 y|y. y \<in> set (x#xs)} = expr_1 y"
      by blast
    have "{expr_1 y|y. y \<in> set (x#xs)} = (set (map (\<lambda>x. expr_1 x) (x#xs)))"
      by auto
    from this max_x_xs have max_x_xs: "Max (set (map (\<lambda>x. expr_1 x) (x#xs))) = expr_1 y"
      by simp
    from A3 A8 have A9: "\<forall>x \<in> set (a#xs). expr_1 x \<le> expr_1 y"
      by simp
    from A7 have A10:"y \<in> set (a#xs)" 
      by simp
    have "finite ({expr_1 x|x. x \<in> set (a#xs)})"
      by simp
    from this A9 A10 Max_eqI have max_1: "Max {expr_1 x|x. x \<in> set (a#xs)} = expr_1 y"
      by blast
    have "{expr_1 y|y. y \<in> set (a#x#xs)} = (set (map (\<lambda>x. expr_1 x) (a#x#xs)))"
      by auto

    from A3 A8 A4 have A11: "\<forall>x \<in> set (a#xs). expr_1 x \<le> expr_1 y"
      by simp
    from A7 have A12: "y \<in> set (a#xs)" 
      by simp
    have "finite ({expr_1 y|y. y \<in> set (a#xs)})"
      by simp
    from this A11 A12 Max_eqI have max_1: "Max {expr_1 y|y. y \<in> set (a#xs)} = expr_1 y"
      by blast
    have "{expr_1 y|y. y \<in> set (a#xs)} = (set (map (\<lambda>x. expr_1 x) (a#xs)))"
      by auto
    from this max_1 have "Max (set (map (\<lambda>x. expr_1 x) (a#xs))) = expr_1 y"
      by simp
    then have max_1: "max_val_xs = expr_1 y"
      using max_val_xs_def by blast


    from A3 A8 A4 have A11: "\<forall>x \<in> set (a#x#xs). expr_1 x \<le> expr_1 y"
      by simp
    from A7 have A12: "y \<in> set (a#x#xs)" 
      by simp
    have "finite ({expr_1 y|y. y \<in> set (a#x#xs)})"
      by simp
    from this A11 A12 Max_eqI have max_2: "Max {expr_1 y|y. y \<in> set (a#x#xs)} = expr_1 y"
      by blast
    have "{expr_1 y|y. y \<in> set (a#x#xs)} = (set (map (\<lambda>x. expr_1 x) (a#x#xs)))"
      by auto
    from this max_2 have "Max (set (map (\<lambda>x. expr_1 x) (a#x#xs))) = expr_1 y"
      by simp
    then have max_2: "max_val = expr_1 y"
      using max_val_def by blast
    from max_val_def xs_new_def have "pos_r (a#x#xs) = xs_new"
      by (metis pos_r.simps(2))
    also from xs_new_def have "... = filter (\<lambda>y. expr_1 y < max_val) (a#x#xs)" 
      by simp
    also from max_2 have "... = filter (\<lambda>z. expr_1 z < expr_1 y) (a#x#xs)"
      by simp
    also from A8 have "... = filter (\<lambda>z. expr_1 z < expr_1 y) (x#xs)"
      by simp
    finally have pos_r_y: "pos_r(a#x#xs) = filter (\<lambda>z. expr_1 z < expr_1 y) (x#xs)" 
      by this

    define max_val_x where "max_val_x = Max (set (map (\<lambda>x. expr_1 x) (x#xs)))"
    define xs_new_x where "xs_new_x = filter (\<lambda>y. expr_1 y < max_val_x) (x#xs)"
    from max_x_xs have max_x_y: "max_val_x = expr_1 y"
      using max_val_x_def by blast
    have "pos_r (x#xs) = xs_new_x"
      by (metis max_val_x_def pos_r.simps(2) xs_new_x_def)
    also from max_x_y have "... = filter (\<lambda>z. expr_1 z < expr_1 y) (x#xs)"
      using xs_new_x_def by blast
    also from pos_r_y have "... = pos_r(a#x#xs)" 
      by (rule HOL.sym)
    finally have "pos_r (x#xs) = pos_r(a#x#xs)" 
      by this
    then show ?thesis by simp
  qed
qed

(*Done*)

(*Done*)
lemma expr_1_pos_r:
  assumes A1: "expr_1 (HML_conj (pos_r (a#xs)) ys) \<le> n4"
  defines "A \<equiv> {0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}"
  defines "B \<equiv> ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)})"
  shows "expr_1 (HML_conj (pos_r xs) ys) \<le> n4"
proof-
  have fin_A: "finite ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)})"
    by simp
  have fin_pos_r: "finite {expr_1 x |x. x \<in> set (pos_r (a#xs))}"
    by simp
  from expr_1_union have A2: "expr_1 (HML_conj (pos_r (a#xs)) ys) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)})" by simp
  from A1 this have pos_r_A: 
"Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)}) \<le> n4"
    by (rule HOL.back_subst)
  have subs_pos_r: "{expr_1 x |x. x \<in> set (pos_r (a#xs))} \<subseteq> ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 (HML_conj [] ys)})" 
    by auto
  from expr_1_union have A3: "expr_1 (HML_conj (pos_r xs) ys) =
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)})" by simp
  thm Max_le_iff
  have A4: "finite ({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)})" by simp
  have A5: "{0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)} \<noteq> {}" by simp
  from A4 A5 have max_fa:
"(Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)}) \<le> n4) =
(\<forall>a\<in>({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)}). a \<le> n4)" 
    by (rule Max_le_iff)
  have A6: "(\<forall>a\<in>({0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)}). a \<le> n4)"
  proof(rule ballI)
    fix b
    assume A7: "b \<in> {0} \<union> {expr_1 x |x. x \<in> set (pos_r xs)} \<union> {expr_1 (HML_conj [] ys)}"
    moreover {
      assume A8: "b = 0"
      then have "b \<le> n4" by simp
    }
    moreover {
      assume A8: "b \<in> {expr_1 x |x. x \<in> set (pos_r xs)}"
      then have A9: "{expr_1 x |x. x \<in> set (pos_r xs)} \<noteq> {}"
        by auto
      have A10: "(\<forall>x \<in> set xs. expr_1 a > expr_1 x) \<or> ((\<exists>x \<in> set xs. expr_1 a < expr_1 x) \<or> 
((\<exists>x\<in> set xs. expr_1 a = expr_1 x) \<and> (\<forall>x \<in> set xs. expr_1 x  \<le> expr_1 a)))"
        by force
      from A8 have b_le_pos_r: "b \<le> Max {expr_1 x |x. x \<in> set (pos_r xs)}"
        by simp
      from A10 have "b \<le> n4"
      proof
          assume "\<forall>x\<in>set xs. expr_1 x < expr_1 a"
          then have A10: "pos_r (a#xs) = xs" 
            by (rule HML_subsets.pos_r_1)
          have A11: "set (pos_r xs) \<subseteq> set (xs)"
            by (metis Orderings.order_eq_iff filter_is_subset pos_r.elims)
          from this A10 have subs: "set (pos_r (xs)) \<subseteq> set (pos_r (a#xs))"
            by simp
          then have subs_xs_axs: "{expr_1 x |x. x \<in> set (pos_r xs)} \<subseteq> {expr_1 x |x. x \<in> set (pos_r (a#xs))}"
            by auto
          from A9 have "set (pos_r xs) \<noteq> {}" by simp
          from this A10 A11 have ne: "set (pos_r (a # xs)) \<noteq> {}"
            by auto
          then have "{expr_1 x |x. x \<in> set (pos_r (a # xs))} \<noteq> {}"
            by simp
          thm Max_mono
          from subs_pos_r this fin_A have 
"Max {expr_1 x |x. x \<in> set (pos_r (a # xs))} \<le> Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a # xs))} \<union> {expr_1 (HML_conj [] ys)})"
            by (rule Max_mono)
          from this pos_r_A have a_xs_n4: "Max {expr_1 x |x. x \<in> set (pos_r (a # xs))} \<le> n4" 
            by (rule Nat.le_trans)
          from subs_xs_axs A9 fin_pos_r have 
"Max {expr_1 x |x. x \<in> set (pos_r xs)} \<le> Max {expr_1 x |x. x \<in> set (pos_r (a # xs))}"
            by (rule Max_mono)
          from this a_xs_n4 have "Max {expr_1 x |x. x \<in> set (pos_r xs)} \<le> n4" 
            by (rule Nat.le_trans)
          from b_le_pos_r this show "b \<le> n4"
            by (rule Nat.le_trans)
        next
          assume "(\<exists>x\<in>set xs. expr_1 a < expr_1 x) \<or>
    (\<exists>x\<in>set xs. expr_1 a = expr_1 x) \<and> (\<forall>x\<in>set xs. expr_1 x \<le> expr_1 a)"
          then show "b \<le> n4"
          proof(rule disjE)
            assume "\<exists>x\<in>set xs. expr_1 a < expr_1 x"
            then have "set (pos_r (a#xs)) = set (pos_r xs) \<union> {a}"
              by (rule pos_r_2)
            then have 
"{expr_1 x |x. x \<in> set (pos_r (a # xs))} = {expr_1 x | x. x\<in> set (pos_r xs) \<union> {a}}"
              by simp
            also have "... = {expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a}"
              by auto
            finally have set_eq: "{expr_1 x |x. x \<in> set (pos_r (a # xs))} = {expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a}"
              by this
            then have max_eq: "Max {expr_1 x |x. x \<in> set (pos_r (a # xs))} = Max({expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a})"
              by simp
            have subs_1: "{expr_1 x | x. x\<in> set (pos_r xs)} \<subseteq> ({expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a})"
              by auto
            have fin_1: "finite ({expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a})"
              by simp
            thm Max_mono
            from subs_1 A9 fin_1 have 
"Max {expr_1 x | x. x\<in> set (pos_r xs)} \<le> Max ({expr_1 x | x. x\<in> set (pos_r xs)} \<union> {expr_1 a})"
              by (rule Max_mono)
            from this max_eq have 
"Max {expr_1 x |x. x \<in> set (pos_r xs)} \<le> Max {expr_1 x |x. x \<in> set (pos_r (a # xs))}" 
              by simp
            also have "... \<le> n4"
              by (metis (no_types, lifting) A8 Max.subset_imp UnCI emptyE fin_A order_trans pos_r_A set_eq subs_pos_r)
            then show "b \<le> n4"
              using b_le_pos_r calculation by linarith
          next
            assume "(\<exists>x\<in>set xs. expr_1 a = expr_1 x) \<and> (\<forall>x\<in>set xs. expr_1 x \<le> expr_1 a)"
            then have "set (pos_r (a#xs)) = set (pos_r xs)" 
              by (rule pos_r_3)
            then have subs_xs_axs: "{expr_1 x |x. x \<in> set (pos_r xs)} = {expr_1 x |x. x \<in> set (pos_r (a#xs))}"
              by auto
            then have "Max {expr_1 x |x. x \<in> set (pos_r xs)} = Max {expr_1 x |x. x \<in> set (pos_r (a#xs))}" 
              by simp
            also have "... \<le> n4"
              by (metis (no_types, lifting) A9 Max_mono dual_order.trans fin_A pos_r_A subs_pos_r subs_xs_axs)
            finally have "Max {expr_1 x |x. x \<in> set (pos_r xs)} \<le> n4"
              by this
            then show "b \<le> n4"
              using b_le_pos_r dual_order.trans by blast
          qed
        qed
      }
      moreover {
        assume A8: "b \<in> {expr_1 (HML_conj [] ys)}"
        from A1 A2 have "expr_1 (HML_conj [] ys) \<le> n4" by simp
        from this A8 have "b \<le> n4" by simp
      }
      ultimately show "b \<le> n4"
        by auto
    qed

      show ?thesis
        using A3 A6 max_fa by presburger
    qed


(*Done*)
lemma expr_1_conj_pos_r:
  assumes A1: "\<forall>x1a \<in> set x1. expr_1 x1a \<le> n4"
and fa_x2: "\<forall>x2a \<in> set x2. expr_1 x2a \<le> n4"
shows "expr_1 (HML_conj (pos_r x1) x2) \<le> n4"
proof-
  from expr_1_set_form have expr_1_set_form: "expr_1 (HML_conj (pos_r x1) x2) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r x1)} \<union> {expr_1 y |y. y \<in> set x2})" 
    by auto
  show ?thesis
proof(cases x1)
  case Nil
  assume A2: "x1 = []"
  have "pos_r [] = []" by simp
  from this A2 have pos_r_x1: "pos_r x1 = []" 
    by simp
  then show ?thesis 
  proof(cases x2)
    case Nil
    assume A3: "x2 =[]"
    then show ?thesis 
    proof-
      from pos_r_x1 A3 have A4: "expr_1 (HML_conj (pos_r x1) x2) = expr_1 (HML_conj [] [])" 
        by simp
      have "expr_1 (HML_conj [] []) = 0" by simp
      from this A4 show ?thesis by simp
    qed
  next
    case (Cons y ys)
    assume A3: "x2 = y # ys"
    from this expr_1_set_form have "expr_1 (HML_conj (pos_r x1) x2) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r x1)} \<union> {expr_1 y |y. y \<in> set x2})"
      by simp
    also from pos_r_x1 A3 have "... = 
Max ({0} \<union> {expr_1 z |z. z \<in> set (y#ys)})" 
      by simp
    finally have A4: "expr_1 (HML_conj (pos_r x1) x2) = Max ({0} \<union> {expr_1 z |z. z \<in> set (y#ys)})"
      by this
    thm Max_le_iff
    have ne: "{expr_1 z |z. z \<in> set (y#ys)} \<noteq> {}" by auto
    have fin: "finite({expr_1 z |z. z \<in> set (y#ys)})" by simp
    from ne fin Max_le_iff have 
"(\<forall>x2a \<in> set (y#ys). expr_1 x2a \<le> n4) \<Longrightarrow> (Max {expr_1 z |z. z \<in> set (y#ys)} <= n4)"
      by auto
    from this A3 fa_x2 have max_y_ys: "Max {expr_1 z |z. z \<in> set (y#ys)} <= n4"
      by simp
    have "Max {0} \<le> n4" by simp
    from this max_y_ys have Max_Max_le_n4: "Max ({Max {0}} \<union> {Max {expr_1 z |z. z \<in> set (y#ys)}}) \<le> n4" 
      by simp
    have ne_0: "{0} \<noteq> {}" by simp
    have fin_0: "finite {0}" by simp
    from ne fin ne_0 fin_0 Max_Max_le_n4 Max_of_union have 
"Max ({0} \<union> {expr_1 z |z. z \<in> set (y#ys)}) \<le> n4" 
      by simp
    from this A4 show ?thesis by simp
  qed
next
  case (Cons a xs)
  assume A3: "x1 = a # xs"
  then show ?thesis 
proof(cases x2)
  case Nil
  from expr_1_set_form have "expr_1 (HML_conj (pos_r x1) x2) = 
 Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r x1)} \<union> {expr_1 y |y. y \<in> set x2})" by simp
  also from A3 local.Nil have "... = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))})" 
    by simp
  finally have expr_1_max: "expr_1 (HML_conj (pos_r x1) x2) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))})" by this
  have "pos_r (a#xs) = [] \<or> pos_r (a#xs) \<noteq> []"
    by simp
  then show ?thesis
  proof
    assume "pos_r (a # xs) = []"
    then have max_simp: "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}) = Max {0}" 
      by simp
    then have "Max {0} = 0" by simp
    from max_simp this expr_1_max show ?thesis 
      by simp
  next
    assume ne_pos_r: "pos_r (a # xs) \<noteq> []"
    have "set (pos_r (a #xs)) \<subseteq> set (a#xs)"
      by (metis filter_is_subset pos_r.simps(2))
    from this A3 have fa_pos_r: "\<forall>x1a\<in>set (pos_r(a#xs)). expr_1 x1a \<le> n4"
      using A1 by blast
    have fin_pos_r: "finite({expr_1 x |x. x \<in> set (pos_r (a#xs))})"
      by simp
    thm Max_in
    from this fin_pos_r ne_pos_r fa_pos_r have max_pos_r: "Max {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<le> n4" 
      by (smt (verit, del_insts) Max_in empty_Collect_eq list.set_sel(1) mem_Collect_eq)
    have "Max {0} \<le> n4" by simp
    from this max_pos_r have max_max: "Max ({Max {0}} \<union> {Max {expr_1 x |x. x \<in> set (pos_r (a#xs))}}) \<le> n4"
      by simp
    have fin_0: "finite {0}"
      by simp
    have ne_0: "{0} \<noteq> {}"
      by simp
    from ne_pos_r have "{expr_1 x |x. x \<in> set (pos_r (a#xs))} \<noteq> {}"
      by simp
    from this fin_pos_r ne_0 fin_0 Max_of_union have
"Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}) = 
Max({Max {0}} \<union> {Max {expr_1 x |x. x \<in> set (pos_r (a#xs))}})" 
      by simp
    from this max_max have "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}) \<le> n4"
      by simp
    from this expr_1_max  Orderings.ord_class.ord_eq_le_trans show ?thesis 
      by simp
  qed
next
  case (Cons y ys)
  assume A4: "x2 = y # ys"
  from expr_1_set_form have "expr_1 (HML_conj (pos_r x1) x2) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r x1)} \<union> {expr_1 y |y. y \<in> set x2})"
    by simp
  also from A3 A4 have "... = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 z |z. z \<in> set (y#ys)})" 
    by simp
  finally have expr_1_form: "expr_1 (HML_conj (pos_r x1) x2) =
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 z |z. z \<in> set (y#ys)})" 
    by this
    have ne_ys: "{expr_1 z |z. z \<in> set (y#ys)} \<noteq> {}" by auto
    have fin_ys: "finite({expr_1 z |z. z \<in> set (y#ys)})" by simp
    from ne_ys fin_ys Max_le_iff have 
"(\<forall>x2a \<in> set (y#ys). expr_1 x2a \<le> n4) \<Longrightarrow> (Max {expr_1 z |z. z \<in> set (y#ys)} <= n4)"
      by auto
    from this A4 fa_x2 have max_y_ys: "Max {expr_1 z |z. z \<in> set (y#ys)} <= n4"
      by simp
    have le_0: "Max {0} \<le> n4" by simp
    have "pos_r (a#xs) = [] \<or> pos_r (a#xs) \<noteq> []"
    by simp
    then show ?thesis
    proof
      assume "pos_r (a # xs) = []"
      then have max_simp: "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 z |z. z \<in> set (y#ys)}) =
Max ({0} \<union> {expr_1 z |z. z \<in> set (y#ys)})" 
        by simp
      also have "... = Max({Max {0}} \<union> {Max {expr_1 z |z. z \<in> set (y#ys)}})"
        using ne_ys by auto
      also from max_y_ys have "... \<le> n4" 
        by simp
      finally have "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 z |z. z \<in> set (y#ys)}) \<le> n4"
        by this
      from expr_1_form this show ?thesis 
        by (rule HOL.forw_subst)
  next
    assume ne_pos_r: "pos_r (a # xs) \<noteq> []"
    have "set (pos_r (a #xs)) \<subseteq> set (a#xs)"
      by (metis filter_is_subset pos_r.simps(2))
    from this A3 have fa_pos_r: "\<forall>x1a\<in>set (pos_r(a#xs)). expr_1 x1a \<le> n4"
      using A1 by blast
    have fin_pos_r: "finite({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))})"
      by simp
    thm Max_in
    from this fin_pos_r ne_pos_r fa_pos_r have max_pos_r: "Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))}) \<le> n4"
      by auto
    from this max_y_ys have max_max_n4: "Max ({Max ({0} \<union> 
{expr_1 x |x. x \<in> set (pos_r (a#xs))})} \<union> {Max{expr_1 z |z. z \<in> set (y#ys)}}) \<le>
n4" by simp
    have fin_0: "finite {0}"
      by simp
    have ne_0: "{0} \<noteq> {}"
      by simp
    from fin_pos_r ne_pos_r fin_ys ne_ys ne_0 have "Max ({Max ({0} \<union> 
{expr_1 x |x. x \<in> set (pos_r (a#xs))})} \<union> {Max{expr_1 z |z. z \<in> set (y#ys)}}) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (pos_r (a#xs))} \<union> {expr_1 z |z. z \<in> set (y#ys)})"
      by (metis (no_types, lifting) Max_of_union Un_empty)
    from this max_max_n4 expr_1_form  show ?thesis 
      by simp
  qed
  qed
qed
qed

lemma expr_4_is:
  fixes n4 and xs and ys and a
  assumes A2: "expr_4 (HML_conj xs ys) \<le> n4 \<Longrightarrow> 
\<forall>x\<in>set xs.(expr_4 x \<le> n4)" and
A3: "expr_4 (HML_conj (a # xs) ys) \<le> n4"
shows "\<forall>x\<in>set (a # xs). expr_4 x \<le> n4"
proof(rule ballI)
  fix x
  assume "x \<in> set (a # xs)"
  have E4: "expr_4 (HML_conj (a#xs) ys) = 
Max ({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})"
        by simp
  also have "... = 
Max({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})" 
    by simp
  also from A3 have E_4: "... \<le> n4" 
    by simp
  have expr_4_xs_def: "expr_4 (HML_conj xs ys) = Max ({expr_4_rest (HML_conj xs ys)} \<union> {expr_1 (HML_conj (pos_r xs) ys)})"
    by simp
  moreover {
  thm Max_ge
  have max_in: "Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)}) \<in> 
({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})" 
    by simp
  have fin_a_xs :"finite ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})" 
    by simp
  from fin_a_xs max_in have "Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)}) \<le> 
Max({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})"
    by (rule Max_ge)
  from this E_4 have le_n4: "Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)}) \<le> n4" 
    by simp
  have fin_subs: "finite ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})" 
    by simp
  have ne_a: "{expr_4_rest a} \<noteq> {}"
    by simp
  have subs_a: "{expr_4_rest a} \<subseteq> ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})"
    by simp
  from fin_subs ne_a subs_a le_n4 have max_a: "Max {expr_4_rest a} \<le> n4"
    by simp
  have ne: "{expr_4_rest (HML_conj xs ys)} \<noteq> {}"
    by simp
  have subs: "{expr_4_rest (HML_conj xs ys)} \<subseteq> ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})" 
    by simp
  from fin_subs ne subs le_n4 have "Max {expr_4_rest (HML_conj xs ys)} \<le> n4" 
    by simp
  from this max_a have "Max {expr_4_rest (HML_conj xs ys)} \<le> n4 \<and> Max {expr_4_rest a} \<le> n4"
    by simp
}
  moreover {
    have ne: "{expr_1 (HML_conj (pos_r (a#xs)) ys)} \<noteq> {}" 
      by simp
    have fin: "finite ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})"
      by simp
    have subs: "{expr_1 (HML_conj (pos_r (a#xs)) ys)} \<subseteq> ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})" 
      by simp
    from E_4 ne fin subs have "Max {expr_1 (HML_conj (pos_r (a#xs)) ys)} \<le> n4" 
      by simp
    from this expr_1_pos_r have "Max {expr_1 (HML_conj (pos_r xs) ys)} \<le> n4" 
      by fastforce
  }
  ultimately have max_le_n4: 
"Max {expr_4_rest (HML_conj xs ys)} \<le> n4 \<and> Max {expr_4_rest a} \<le> n4 \<and> Max {expr_1 (HML_conj (pos_r xs) ys)} \<le> n4" 
    by simp
  from this A2 have fa_xs: "\<forall>x\<in>set xs. expr_4 x \<le> n4" by simp
  have "expr_4 (HML_conj (a # xs) ys) = 
Max ({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})"
    by simp
  from max_le_n4 have expr_rest_a: "Max {expr_4_rest a} \<le> n4" by simp
  then have expr_rest_a: "expr_4_rest a \<le> n4" by simp
  have "expr_4 a \<le> n4"
  proof(cases a)
    case (HML_conj x11 x12)
    show ?thesis 
    proof(rule ccontr)
      assume "expr_4 a > n4"
      have a_subst: "expr_4 a = expr_4 (HML_conj x11 x12)"
        using HML_conj by fastforce
      have "expr_4_rest (HML_conj (a#xs) ys) = 
Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})"
        by simp
      from this E4 have 
"expr_4 (HML_conj (a#xs) ys) = 
Max ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union>
 {expr_1 (HML_conj (pos_r (a # xs)) ys)})"
        by (rule HOL.subst)
      from this A3 have "... \<le> n4" 
        by (rule HOL.subst)
      then have "Max {Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<le> n4"
        by simp
      then have "\<forall>x \<in> {Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})}. x \<le> n4"
        by simp
      then have "Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)}) \<le> n4"
        by simp
      from this a_subst have le_n4: "Max {expr_4_rest (HML_conj x11 x12)} \<le> n4"
        using HML_conj by fastforce
      have "expr_4 (HML_conj x11 x12) =
Max ({expr_4_rest (HML_conj x11 x12)} \<union> {expr_1 (HML_conj (pos_r x11) x12)})"
        by simp
      also have gr_n4_s: "... > n4"
        using HML_conj \<open>n4 < expr_4 a\<close> calculation by presburger
      have fin_s: "finite ({expr_4_rest (HML_conj x11 x12)} \<union> {expr_1 (HML_conj (pos_r x11) x12)})"
        by simp
      have ne: "{expr_4_rest (HML_conj x11 x12)} \<noteq> {}" 
        by simp
      from gr_n4_s have "(Max {expr_4_rest (HML_conj x11 x12)} > n4) \<or> 
(Max {expr_1 (HML_conj (pos_r x11) x12)} > n4)"
        by auto
      from gr_n4_s fin_s ne have "Max {expr_4_rest (HML_conj x11 x12)} > n4" sorry
  next
    case (HML_poss x21 x22)
    then show ?thesis sorry
  qed
(*-----------------*)
    using expr_rest_a
  proof(induction a)
    case (HML_conj x1 x2)
    assume A4: "(\<And>x1a. x1a \<in> set x1 \<Longrightarrow> expr_4_rest x1a \<le> n4 \<Longrightarrow> expr_4 x1a \<le> n4)"
and A5: "(\<And>x2a. x2a \<in> set x2 \<Longrightarrow> expr_4_rest x2a \<le> n4 \<Longrightarrow> expr_4 x2a \<le> n4)"
and A6: "expr_4_rest (HML_conj x1 x2) \<le> n4"
    then show "expr_4 (HML_conj x1 x2) \<le> n4"
    proof(cases x1)
      have "expr_4 (HML_conj x1 x2) =
Max ({expr_4_rest (HML_conj x1 x2)} \<union> {expr_1 (HML_conj (pos_r x1) x2)})"
        by simp
      from expr_4_rest_set A6 have rest_set:
"Max ({0} \<union> {expr_4_rest x |x. x \<in> set x1} \<union> {expr_4_rest y |y. y \<in> set x2}) \<le> n4"
        by metis
      have ne: "{expr_4_rest x |x. x \<in> set x1} \<noteq> {}"
        (*TODO*)
        (*Wenn Menge nicht leer ist muss sie \<le> n4 sein, da sonst vereinigung auch größer als n4 ist.*)
      have fin_set: "finite ({0} \<union> {expr_4_rest x |x. x \<in> set x1} \<union> {expr_4_rest y |y. y \<in> set x2})"
        by simp
      have "{expr_4_rest x |x. x \<in> set x1} \<subseteq>
 {0} \<union> {expr_4_rest x |x. x \<in> set x1} \<union> {expr_4_rest y |y. y \<in> set x2}"
        by auto
      from fin_set this rest_set have "Max {expr_4_rest x |x. x \<in> set x1} \<le> 
Max ({0} \<union> {expr_4_rest x |x. x \<in> set x1} \<union> {expr_4_rest y |y. y \<in> set x2})" 
      have "expr_1 (HML_conj (pos_r x1) x2) \<le> n4" 
      proof(induction x1)
        case Nil
        then show ?case sorry
      next
        case (Cons a x1)
        then show ?case sorry
      qed
    then have "\<forall>x1a \<in> set x1. expr_4_rest x1a \<le> n4" 
    then show ?case sorry
  next
    case (HML_poss x1 b)
    then show ?case by simp
  qed
  from this fa_xs have "\<forall>x\<in>set (a#xs). expr_4 x \<le> n4" 
  oops

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
      from A3 have E2_a: "expr_2 a \<le> n2"
        using dual_order.trans by fastforce
      from A3 have E2_xs: "expr_2 (HML_conj xs ys) \<le> n2"
        using dual_order.trans by fastforce
      from A3 have E3_a: "expr_3 a \<le> n3"
        using dual_order.trans by fastforce
      from A3 have E3_xs: "expr_3 (HML_conj xs ys) \<le> n3"
        using dual_order.trans by fastforce
      moreover {
      have E4: "expr_4 (HML_conj (a#xs) ys) = 
Max ({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})"
        by simp
      also have "... = 
Max({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})} \<union> 
{expr_1 (HML_conj (pos_r (a#xs)) ys)})" 
        by simp
      also from A3 have E_4: "... \<le> n4" 
        by simp
      have "expr_4 (HML_conj xs ys) =
Max ({expr_4_rest (HML_conj xs ys)} \<union> {expr_1 (HML_conj (pos_r xs) ys)})" 
        by simp
      have subs_4: "{expr_4_rest (HML_conj (a#xs) ys)} \<subseteq> 
({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})"
        by simp
      thm Max_mono
      have ne_4: "{expr_4_rest (HML_conj (a#xs) ys)} \<noteq> {}"
        by simp
      have fin_4: "finite ({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})"
        by simp
      from subs_4 ne_4 fin_4 have "Max {expr_4_rest (HML_conj (a#xs) ys)} \<le>
 Max ({expr_4_rest (HML_conj (a#xs) ys)} \<union> {expr_1 (HML_conj (pos_r (a#xs)) ys)})" by (rule Max_mono)
      from this A3 have max_rest: "Max {expr_4_rest (HML_conj (a#xs) ys)} \<le> n4"
        by (meson E_4 dual_order.trans enat_ord_simps(1))
      have E4_2: "expr_4_rest (HML_conj (a#xs) ys) = 
Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj xs ys)})"
        by simp
      from A3 expr_1_pos_r have E4_a: "expr_4 a \<le> n4" sorry
      from A3 have E4_xs: "expr_4 (HML_conj xs ys) \<le> n4" sorry
    }
      from A3 have E5_a: "expr_5 a \<le> n5"
        using dual_order.trans by fastforce
      from A3 have E5_xs: "expr_5 (HML_conj xs ys) \<le> n5" 
        using dual_order.trans by fastforce
      from A3 have E6_a: "expr_6 a \<le> n6"
        using dual_order.trans by fastforce
      from A3 have E6_xs: "expr_6 (HML_conj xs ys) \<le> n6" 
        using dual_order.trans by fastforce
      from A2 E1_a E1_xs E2_a E2_xs E3_a E3_xs E4_a E4_xs E5_a E5_xs E6_a E6_xs show ?thesis
        by simp
    qed
  qed
next
  show "(\<forall>y \<in> set ys. less_eq_t (expr y) (n1, n2, n3, n4, n5, n6))"
    sorry
qed

lemma expr_2_lb: "expr_2 f \<ge> 1"
proof(induction f)
  case (HML_conj x1 x2)
  then show ?case 
    proof(cases x1)
      case Nil
      then have "x1 = []" by simp
      then show ?thesis 
      proof(cases x2)
        case Nil
        then have "x2 = []" by simp
        then show ?thesis
          by (simp add: \<open>x1 = []\<close>)
      next
        case (Cons y ys)
        then show ?thesis 
        proof-
          have "expr_2 (HML_conj x1 x2) = (Max ({1 + expr_2 y} \<union> {expr_2 (HML_conj [] ys)}))"
            using formula_prices_list.expr_2_conj_right local.Cons local.Nil by blast
          then show ?thesis by simp
        qed
      qed
    next
    case (Cons x xs)
    then show ?thesis 
      by simp
  qed
next
  case (HML_poss x1 f)
  then show ?case by simp
qed

lemma trace_right: 
  fixes "\<phi>"
  assumes A1: "HML_trace \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using A1
proof(induct \<phi> rule:HML_trace.induct)
  case trace_conj
  then show ?case using one_enat_def zero_enat_def by auto
next
  case IV: (trace_pos \<phi> \<alpha>)
  then show ?case using HML_trace.cases by fastforce
qed

lemma HML_trace_conj_empty:
  fixes x1 x2
  assumes A1: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, 1, 0, 0, 0, 0)" 
  shows "x1 = [] \<and> x2 = []"
proof-
  from A1 have A2: "expr_2 (HML_conj x1 x2) \<le> 1"
    by (simp add: one_enat_def)
  have A3: "x1 = []"
  proof(rule ccontr)
    assume "x1 \<noteq> []"
    then have "\<exists>x xs. x1 = (x # xs)"
      by (meson list.exhaust)
    then obtain x xs where "x1 = (x#xs)" 
      by auto
    then have A4: "expr_2 (HML_conj x1 x2) = (Max ({1 + expr_2 x} \<union> {expr_2 (HML_conj xs x2)}))" 
      by simp
    from expr_2_lb have "expr_2 x \<ge> 1" by auto
    from this A4 have "expr_2 (HML_conj x1 x2) > 1" 
      by simp
    from this A2 show False by simp
  qed
have A4: "x2 = []"
  proof(rule ccontr)
    assume "x2 \<noteq> []"
    then have "\<exists>y ys. x2 = (y # ys)"
      by (meson list.exhaust)
    then obtain y ys where "x2 = (y#ys)" 
      by auto
    show False
    proof(cases x1)
      case Nil
      then show ?thesis
      proof-
        have A5: "expr_2 (HML_conj x1 x2) = (Max ({1 + expr_2 y} \<union> {expr_2 (HML_conj [] ys)}))"
          using \<open>x2 = y # ys\<close> formula_prices_list.expr_2_conj_right local.Nil by blast
        from expr_2_lb have "expr_2 y \<ge> 1" by auto
        from this A5 have "expr_2 (HML_conj x1 x2) > 1"
          by simp
        from this A2 show False by simp
      qed
    next
      case (Cons x xs)
      then show ?thesis 
      proof-
        have A6: "expr_2 (HML_conj x1 x2) = (Max ({1 + expr_2 x} \<union> {expr_2 (HML_conj xs x2)}))"
          using formula_prices_list.expr_2_conj local.Cons by blast
        from expr_2_lb have "expr_2 x \<ge> 1" by auto
        from this A6 have "expr_2 (HML_conj x1 x2) > 1" 
          by simp
        from this A2 show False by simp
      qed
    qed
  qed
  from A3 A4 show ?thesis 
    by simp
qed

lemma trace_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  shows "(HML_trace \<phi>)"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  then show ?case 
  proof-
    from A1 HML_trace_conj_empty have "x1 = [] \<and> x2 = []"
      using HML_conj by blast
      then show ?thesis
        using HML_conj trace_conj by blast
    qed
next
  case (HML_poss \<alpha> \<psi>)
  assume A1: "less_eq_t (expr \<psi>) (\<infinity>, 1, 0, 0, 0, 0) \<Longrightarrow> HML_trace \<psi>" and
A2: "less_eq_t (expr (HML_poss \<alpha> \<psi>)) (\<infinity>, 1, 0, 0, 0, 0)"
  then show ?case 
  proof- 
    from A1 have "HML_trace \<psi>"
      using A2 by auto
    then show ?thesis 
      by (rule HML_list.HML_trace.trace_pos)
  qed
qed

lemma "(HML_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using trace_left trace_right by blast

lemma simulation_right:
  fixes "\<phi>"
  assumes A1: "HML_simulation \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using A1
proof(induction \<phi> rule:HML_simulation.induct)
  case (sim_pos \<phi>)
  then show ?case
    using trace_right by force
next
  case (sim_conj xs)
  then show ?case
  proof(induction xs)
    case Nil
    then show ?case
      using zero_enat_def by force
  next
    case (Cons x xs)
    then show ?case
    proof-
      have C1: "less_eq_t (expr (HML_conj xs [])) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
        by (meson Cons.IH Cons.prems list.set_intros(2))
      have C2: "less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
        using Cons.prems by auto
      from C1 have C3: "expr_5 (HML_conj xs []) = 0"
        using enat_0_iff(2) by fastforce
      from C2 have C4: "expr_5 x = 0"
        using enat_0_iff(2) by force
      have "expr_5 (HML_conj (x # xs) []) = Max ({0} \<union> {expr_5 x} \<union> {expr_5 (HML_conj xs [])})" 
        by simp
      from this C4 C3 have dim_5: "expr_5 (HML_conj (x # xs) []) = 0" 
        by simp
      from C1 have C5: "expr_6 (HML_conj xs []) = 0"
        using enat_0_iff(2) by force
      from C2 have C6: "expr_6 x = 0"
        using enat_0_iff(2) by auto
      have "expr_6 (HML_conj (x#xs) []) =  Max({0} \<union> {expr_6 x} \<union> {expr_6 (HML_conj xs [])})"
        by simp
      from this C5 C6 have dim_6: "expr_6 (HML_conj (x#xs) []) = 0" 
        by simp
      from dim_5 dim_6 show ?case
        using enat_0 by auto
    qed
  qed
qed

lemma expr_6_conj:
  fixes \<Phi> 
  shows "expr_6 (HML_conj \<Phi> (x#xs)) \<ge> 1"
proof(induction \<Phi>)
  case Nil
  then show ?case
    by simp
next
  case (Cons a \<Phi>)
  then show ?case 
    by simp
qed

lemma expr_6_union_pos:
  shows "expr_6 (HML_conj x1 x2) = Max({0} \<union> {expr_6 xa | xa. xa \<in> set x1} \<union> {expr_6 (HML_conj [] x2)})"
proof(induction x1 arbitrary: x2)
  case Nil
  then show ?case by simp
  next
    case (Cons a x11)
    then show ?case
    proof-
    assume A1: "(\<And>x2. expr_6 (HML_conj x11 x2) =
           Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x11} \<union> {expr_6 (HML_conj [] x2)}))"
    then show "expr_6 (HML_conj (a # x11) x2) =
    Max ({0} \<union> {expr_6 xa |xa. xa \<in> set (a # x11)} \<union> {expr_6 (HML_conj [] x2)})"
    proof-
      have A2: "{expr_6 xa |xa. xa \<in> set (a # x11)} = {expr_6 a} \<union> {expr_6 xa |xa. xa \<in> set x11}"
        by auto
      then have "Max ({0} \<union> {expr_6 xa |xa. xa \<in> set (a # x11)} \<union> {expr_6 (HML_conj [] x2)}) = 
Max({0} \<union> {expr_6 a} \<union> {expr_6 xa |xa. xa \<in> set x11} \<union> {expr_6 (HML_conj [] x2)})" by simp
      also have "... = Max({expr_6 a} \<union> {Max({0} \<union> {expr_6 xa |xa. xa \<in> set x11} \<union> {expr_6 (HML_conj [] x2)})})" 
        by simp
      also from A1 have "... = Max({expr_6 a} \<union> {expr_6 (HML_conj x11 x2)})" by simp
      also have "... = expr_6 (HML_conj (a # x11) x2)" by simp
      finally show ?thesis by simp
    qed
  qed
qed

lemma Max_eq_expr_6:
  fixes x1 x2
  defines DA: "A \<equiv> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
  defines DB: "B \<equiv> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})}"
  shows "Max A = Max B"
proof- 
  have fin_A: "finite A" 
  proof-
    have A1: "finite {expr_6 xa |xa. xa \<in> set x1}" by simp
    have A2: "finite {1 + expr_6 ya |ya. ya \<in> set x2}" by simp
    have A3: "finite {0}" by simp
    from A1 A2 A3 show ?thesis
      using DA by blast
  qed

  have fin_B: "finite B" 
  proof-
    have A1: "finite {expr_6 xa |xa. xa \<in> set x1}" by simp
    have A2: "finite {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})}" by simp
    have A3: "finite {0}" by simp
    from A1 A2 A3 show ?thesis
      using DB by blast
  qed
  have left: "Max A \<ge> Max B"
  proof-
    have A1: "(Max A \<ge> Max B ) = 
(Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}) \<ge> 
Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})}))"
      using DA DB by blast
  have left: "Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})}) \<le>
         Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
  proof-
    have "{1 + expr_6 ya |ya. ya \<in> set x2} \<subseteq> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
      by auto
    hence "Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}) \<le> Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      by (simp add: Max.coboundedI)

    moreover have "{0} \<subseteq> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
      by auto
    hence "Max {0} \<le> Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      by (simp add: Max.coboundedI)

    moreover have "{expr_6 xa |xa. xa \<in> set x1} \<subseteq> {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
      by auto
    hence "Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1}) \<le> Max({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      by (simp add: Max.coboundedI)
    ultimately show ?thesis by simp
  qed
  from this A1 show ?thesis by simp
qed
  have right: "Max A \<le> Max B"
  proof-
    thm Max_ge_iff
    thm Max_in
    thm Max_eq_if
    have A1: "Max A \<le> Max B = (\<forall>a\<in>A. \<exists>b\<in>B. a \<le> b)"
      by (smt (verit, best) DA DB Max_ge Max_in Un_insert_right empty_not_insert fin_A fin_B le_trans sup_commute)
  have right: "\<forall>a\<in>A. \<exists>b\<in>B. a \<le> b" 
  proof(rule ballI)
    fix a
    assume A1: "a \<in> A"
    moreover {
      assume A2: "a = 0"
      then have "a \<in> B"
        using assms(2) by blast
      have "a \<le> a" by simp
      from this \<open>a \<in> B\<close> have "\<exists>x \<in> B. a \<le> x" by auto
      }
    moreover {
      assume A2: "a \<in> {expr_6 xa |xa. xa \<in> set x1}"
      then obtain xa where "a = expr_6 xa" and "xa \<in> set x1" by auto
      from A2 have "a \<in> B"
        using assms(2) by blast
      have "a \<le> a" by simp
      from this \<open>a \<in> B\<close> have "\<exists>x \<in> B. a \<le> x" by auto
    }
    moreover {
      assume A2: "a \<in> {0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
      have A3: "Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}) \<in> B"
        using DB by blast
      have "a \<le> Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
        using A2 by force
      from this A3 have "\<exists>x \<in> B. a \<le> x" by auto
    }
    moreover {
      from DA have "A = {0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
        by (rule HOL.meta_eq_to_obj_eq)
      from \<open>a \<in> A\<close> this have "a \<in> ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}))"
        by simp
      then have "a \<in> {0} \<or> a \<in> {expr_6 xa |xa. xa \<in> set x1} \<or> a \<in> {0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}" 
        by auto
    }
    ultimately show "\<exists>b\<in>B. a \<le> b" by auto
  qed
  from this A1 show ?thesis by simp
qed
  from left right show ?thesis by simp
qed

lemma expr_6_union_neg:
  shows "expr_6 (HML_conj x1 x2) = Max({0} \<union> {expr_6 xa | xa. xa \<in> set x1} \<union> {1 + expr_6 ya | ya. ya \<in> set x2})"
proof-
  from expr_6_union_pos have A1: "expr_6 (HML_conj x1 x2) = Max({0} \<union> {expr_6 xa | xa. xa \<in> set x1} \<union> {expr_6 (HML_conj [] x2)})"
    by auto
  have A2: "expr_6 (HML_conj [] x2) = Max({0} \<union> {1 + expr_6 ya | ya. ya \<in> set x2})"
  proof(induction x2)
    case Nil
    then show ?case by simp
  next
    case (Cons a x2)
    then show ?case
    proof-
      assume A3: "expr_6 (HML_conj [] x2) = Max({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      show "expr_6 (HML_conj [] (a # x2)) = Max({0} \<union> {1 + expr_6 ya |ya. ya \<in> set (a # x2)})"
      proof-
        have A4: "{1 + expr_6 ya |ya. ya \<in> set (a # x2)} = {1 + expr_6 a} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}"
          by auto
        then have "Max({0} \<union> {1 + expr_6 ya |ya. ya \<in> set (a # x2)}) = Max({0} \<union> {1 + expr_6 a} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
          by simp
        also from A3 have "... = Max({0} \<union> {1 + expr_6 a} \<union> {Max( {0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})})" 
          by simp
        also from A3 have "... = Max({0} \<union> {1 + expr_6 a} \<union> {expr_6 (HML_conj [] x2)})" 
          by simp
        also have "... = expr_6 (HML_conj [] (a # x2))"
          by simp
        finally show ?thesis by simp
      qed
    qed
  qed
  from this A1 have "expr_6 (HML_conj x1 x2) = 
Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {Max ({0} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})})" 
    by (rule HOL.subst)
  also from Max_eq_expr_6 have 
"... = Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1}  \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
    by metis
  finally show ?thesis by this
qed 

lemma x2_empty:
  assumes A1: "(less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" and
A2: "\<forall>x2a \<in> set x2. (less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
shows "x2 = []"
  using A1 A2
proof(induction x1)
  case Nil
  then show ?case 
    by (smt (verit, ccfv_SIG) A1 HML_subsets.expr_6_conj enat_0_iff(2) expr.simps expr_6.elims formula_list.inject(1) formula_list.simps(4) le_zero_eq less_eq_t.simps list.distinct(1) not_one_le_zero)
next
  case (Cons a list)
  then show ?case
  proof-
    from A1 have A2: "expr_6 (HML_conj x1 x2) = 0"
      using enat_0_iff(2) by force
    have A3: "expr_6 (HML_conj x1 x2) = 
Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      using expr_6_union_neg  by auto
    have "{1 + expr_6 ya |ya. ya \<in> set x2} \<subseteq> ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2})"
      by auto
    then have A4: "Max ({0} \<union> {expr_6 xa |xa. xa \<in> set x1} \<union> {1 + expr_6 ya |ya. ya \<in> set x2}) \<le> Max({1 + expr_6 ya |ya. ya \<in> set x2})"
      using A2 A3 by linarith
    have A5: "x2 \<noteq> [] \<Longrightarrow> Max({1 + expr_6 ya |ya. ya \<in> set x2}) \<ge> 1"
      by (metis A2 HML_subsets.expr_6_conj list.exhaust not_one_le_zero)
    show ?thesis
    proof(rule ccontr)
      assume A6: "x2 \<noteq> []"
      from this A5 have A7: "Max({1 + expr_6 ya |ya. ya \<in> set x2}) \<ge> 1"
        by simp
      from A2 A3 A4 A6 have A8: "Max({1 + expr_6 ya |ya. ya \<in> set x2}) \<le> 0"
        by (metis HML_subsets.expr_6_conj neq_Nil_conv not_one_le_zero)
      from A7 A8 show False by simp
    qed
  qed
qed

lemma simulation_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  shows "(HML_simulation \<phi>)"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  then show ?case 
  proof-
    assume A2: "(\<And>x1a. x1a \<in> set x1 \<Longrightarrow> less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0) \<Longrightarrow> HML_simulation x1a)" and
A3: " (\<And>x2a. x2a \<in> set x2 \<Longrightarrow> less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0) \<Longrightarrow> HML_simulation x2a)" and
A4: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0)"
    show "HML_simulation (HML_conj x1 x2)"
    proof-
      (*from A1 have A1: "(less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" sorry*)
      from A2 have A2: "\<forall>x1a \<in> set x1. HML_simulation x1a"
        using A4 mon_conj by blast 
      from A3 have A3: "\<forall>x2a \<in> set x2. HML_simulation x2a" 
        using A4 mon_conj by blast
      from A2 have "\<forall>x1a \<in> set x1. (less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
        using simulation_right by blast
      from A3 have "\<forall>x2a \<in> set x2. (less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
        using simulation_right by blast
      from this A1 A4 x2_empty have A4: "x2 = []"
        by auto
      have A5: "(\<forall>x1a \<in> (set x1). HML_simulation x1a)\<longrightarrow>HML_simulation (HML_conj  x1 [])"
        using HML_simulation.sim_conj by blast
      from this A4 show ?case
        using A2 by blast
    qed    
    fix x1a and x2a
    assume A1: "x1a \<in> set x1 \<Longrightarrow> less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x1a" and
A2: "x2a \<in> set x2 \<Longrightarrow> less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x2a" and
A3: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  qed
next
  case (HML_poss x1 \<phi>)
  then show ?case
    by (simp add: sim_pos)
qed

lemma "(HML_simulation \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using simulation_left simulation_right by blast

lemma expr_4_fail:
  fixes \<phi> :: "('a)formula_list" and \<alpha>
  assumes A1: "HML_failure (HML_poss \<alpha> \<phi>)" and A2: "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1)"
  shows "expr_4 (HML_poss \<alpha> \<phi>) = 0"
  using A2 enat_0_iff(2) by auto

lemma expr_2_fail:
  assumes A1: "HML_failure (HML_conj [] x2)" and A2: "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  shows "expr_2 (HML_conj [] x2) \<le> 2"
  using A1 A2
proof(induction x2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x2)
  then show ?case
  proof-
    assume A3: "(HML_failure (HML_conj [] x2) \<Longrightarrow>
     \<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<Longrightarrow> expr_2 (HML_conj [] x2) \<le> 2)"
and A4: "HML_failure (HML_conj [] (a # x2))"
and A5: "\<forall>y\<in>set (a # x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    show ?thesis
    proof-
      from A5 have "\<exists>\<alpha>. a = HML_poss \<alpha> (HML_conj [] [])"
        by (simp add: Cons.prems(2))
      then have "expr_2 a = 1"
        by auto
      from A3 A4 A5 have A6: "expr_2 (HML_conj [] x2) \<le> 2"
        by (metis (no_types, opaque_lifting) HML_failure.simps formula_list.distinct(1) formula_list.inject(1) list.set_intros(2))
      have "expr_2 (HML_conj [] (a # x2)) = (Max ({1 + expr_2 a} \<union> {expr_2 (HML_conj [] x2)}))"
        by simp
      also have "... = (Max ({2} \<union> {expr_2 (HML_conj [] x2)}))"
        by (simp add: \<open>expr_2 a = 1\<close>)
      also from A6 have "... = 2"
        by simp
      finally show ?thesis 
        by simp
    qed
  qed
qed

lemma expr_3_fail:
  assumes A1: "HML_failure (HML_conj [] x2)" and A2: "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  shows "expr_3 (HML_conj [] x2) \<le> 0"
  using A1 A2
proof(induction x2)
  case Nil
  then show ?case
    by simp
next
  case (Cons a x2)
  then show ?case  
  proof-
    assume A3: "(HML_failure (HML_conj [] x2) \<Longrightarrow>
     \<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<Longrightarrow> expr_3 (HML_conj [] x2) \<le> 0)"
and A4: "HML_failure (HML_conj [] (a # x2))"
and A5: "\<forall>y\<in>set (a # x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    then show ?thesis
    proof-
      from A5 have "\<exists>\<alpha>. a = HML_poss \<alpha> (HML_conj [] [])"
        by simp
      then have A6: "expr_3 a = 0"
        by auto
      from A3 A4 A5 have A7: "expr_3 (HML_conj [] x2) = 0" 
        by (metis (no_types, opaque_lifting) HML_failure.simps formula_list.distinct(1) formula_list.inject(1) le_zero_eq list.set_intros(2))
      show ?thesis 
        by (simp add: A6 A7)
    qed
  qed
qed

lemma expr_4_fail_neg:
assumes A1: "HML_failure (HML_conj [] x2)" and A2: "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  shows "expr_4 (HML_conj [] x2) \<le> 0"
  using A1 A2
proof(induction x2)
  case Nil
  then show ?case 
by simp
next
  case (Cons a x2)
  then show ?case 
  proof-
    assume A3: "(HML_failure (HML_conj [] x2) \<Longrightarrow>
     \<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<Longrightarrow> expr_4 (HML_conj [] x2) \<le> 0)"
and A4: "HML_failure (HML_conj [] (a # x2))"
and A5: "\<forall>y\<in>set (a # x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
    show "expr_4 (HML_conj [] (a # x2)) \<le> 0"
    proof-
      have "expr_4 a = 0"
        using local.Cons(3) by fastforce
      from A3 A4 A5 have "expr_4 (HML_conj [] x2) = 0"
        by (metis (no_types, opaque_lifting) HML_failure.simps formula_list.inject(1) formula_list.simps(4) le_zero_eq list.set_intros(2))
      have "expr_4 (HML_conj [] (a # x2)) = 
Max ({expr_4_rest (HML_conj [] (a#x2))} \<union> {expr_1 (HML_conj (pos_r []) (a#x2))})"
        by simp
      also have "... = Max ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_1 (HML_conj [] x2)})} \<union> {0})"
        by simp
      also have "... = Max ({Max ({0} \<union> {0} \<union> {expr_4_rest (HML_conj [] x2)})} \<union> {0})"
        using A5 by auto
      also have "... = Max ({Max ({0} \<union> {0} \<union> {0})} \<union> {0})"
        using \<open>expr_4 (HML_conj [] x2) = 0\<close> by force
      also have "... = 0"
        by simp
      finally show ?thesis
        by simp
    qed
  qed
qed

lemma expr_5_fail:
assumes A1: "HML_failure (HML_conj [] x2)" and A2: "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  shows "expr_5 (HML_conj [] x2) \<le> 1"
  using A1 A2
proof(induction x2)
  case Nil
  then show ?case 
    by simp
next
  case (Cons a x2)
  then show ?case 
  proof-
assume A3: "(HML_failure (HML_conj [] x2) \<Longrightarrow>
     \<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<Longrightarrow> expr_5 (HML_conj [] x2) \<le> 1)"
and A4: "HML_failure (HML_conj [] (a # x2))"
and A5: "\<forall>y\<in>set (a # x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  show ?thesis
  proof-
    have A6: "expr_5 a = 0"
      using A5 by auto
    have A7: "expr_1 a = 1"
      using A5 by force
    have A8: "expr_5 (HML_conj [] x2) \<le> 1"
      by (metis (no_types, opaque_lifting) A3 A4 HML_failure.cases formula_list.distinct(1) formula_list.inject(1) list.set_intros(2) neg)
    have "expr_5 (HML_conj [] (a # x2)) = Max ({0} \<union> {expr_5 a} \<union> {expr_5 (HML_conj [] x2)} \<union> {expr_1 a})"
      by simp
    also from A6 A7 A8 have "... = 1"
      by simp
    finally show ?thesis
      by simp
    qed
  qed
qed

lemma expr_6_fail:
assumes A1: "HML_failure (HML_conj [] x2)" and A2: "\<forall>y\<in>set x2.\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  shows "expr_6 (HML_conj [] x2) \<le> 1"
  using A1 A2
proof(induction x2)
  case Nil
  then show ?case by simp
next
  case (Cons a x2)
  then show ?case
  proof-
assume A3: "(HML_failure (HML_conj [] x2) \<Longrightarrow>
     \<forall>y\<in>set x2. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []) \<Longrightarrow> expr_6 (HML_conj [] x2) \<le> 1)"
and A4: "HML_failure (HML_conj [] (a # x2))"
and A5: "\<forall>y\<in>set (a # x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])"
  show ?thesis
  proof-
    have A6: "expr_6 a = 0"
      using A5 by force
    from A3 A4 A5 have A7: "expr_6 (HML_conj [] x2) \<le> 1"
      by (metis (no_types, opaque_lifting) HML_failure.simps formula_list.distinct(1) formula_list.inject(1) list.set_intros(2))
    have "expr_6 (HML_conj [] (a # x2)) \<le> Max({0}  \<union> {1 + expr_6 a} \<union> {expr_6 (HML_conj [] x2)})"
      by simp
    also from A6 A7 have "... \<le> 1"
      by simp
    finally show ?thesis
      by this
    qed
  qed
qed

thm subst

lemma failure_right:
  fixes \<phi>
  assumes A1: "HML_failure \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using A1
proof(induction \<phi> rule:HML_failure.induct)
  case (trace \<psi> \<alpha>)
  then show ?case 
  proof-
    have A2: "expr_2 (HML_poss \<alpha> \<psi>) \<le> 2 "
      using linorder_not_le local.trace(2) by fastforce
    have A3: "expr_3 (HML_poss \<alpha> \<psi>) \<le> 0"
      using enat_0_iff(2) local.trace(2) by force
    have A4: "expr_4 (HML_poss \<alpha> \<psi>) \<le> 0"
      by (metis HML_failure.trace Orderings.order_eq_iff expr_4_fail trace.IH trace.hyps)
    have A5: "expr_5 \<psi> \<le> 1"
      by (metis expr.simps less_eq_t.simps local.trace(2) of_nat_1 of_nat_eq_enat of_nat_le_iff)
    have A6: "expr_6 \<psi> \<le> 1"
      by (metis expr.simps less_eq_t.simps local.trace(2) of_nat_1 of_nat_eq_enat of_nat_le_iff)
    from A1 A2 A3 A4 A5 A6 show ?thesis
      using trace.IH by auto
  qed
next
  case (neg x2 \<alpha>)
  then show ?case
  proof-
    assume "\<forall>y\<in>set x2. y = HML_poss \<alpha> (HML_conj [] [])"
    show "less_eq_t (expr (HML_conj [] x2)) (\<infinity>, 2, 0, 0, 1, 1)"
    proof-
      have A2: "expr_2 (HML_conj [] x2) \<le> 2"
        by (meson HML_failure.neg expr_2_fail local.neg)
      have A3: "expr_3 (HML_conj [] x2) \<le> 0"
        by (meson HML_failure.neg expr_3_fail local.neg)
      have A4: "expr_4 (HML_conj [] x2) \<le> 0"
        by (meson HML_failure.neg expr_4_fail_neg local.neg) 
      have A5: "expr_5 (HML_conj [] x2) \<le> 1" 
        by (meson HML_failure.neg expr_5_fail local.neg) 
      have A6: "expr_6 (HML_conj [] x2) \<le> 1" 
        by (meson HML_failure.neg expr_6_fail local.neg) 
      from A1 A2 A3 A4 A5 A6 show ?thesis
        by (simp add: Pair_inject numeral_eq_enat one_enat_def zero_enat_def)
    qed
  qed
qed

(* ------------ *)
(* Ab hier: Alles veraltet *)

lemma failure_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  shows "HML_failure \<phi>"
  by (smt (verit, del_insts) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) neg subformula.cases)

lemma "(HML_failure \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using failure_left failure_right by blast

lemma expr_4_read:
  fixes \<phi> and \<alpha>
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
    have "expr_4 (HML_poss \<alpha> (HML_conj x11 x12)) \<le> 1"
    proof(induct x11 arbitrary: x12)
      case Nil
      then show ?case
        by (smt (verit, ccfv_threshold) empty_iff formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.set(1) subformula.cases) 
    next
      case (Cons a x11)
      then show ?case
        by (smt (verit, del_insts) empty_iff formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.set(1) subformula.cases) 
    qed
    thus ?thesis
      using HML_conj by blast
  qed
next
  case (HML_poss x21 x22)
  then show ?thesis
    by (metis A2 expr.simps expr_4.simps(2) formula_prices_list.expr_4_pos less_eq_t.simps of_nat_1 of_nat_eq_enat of_nat_le_iff) 
qed

lemma readiness_right:
  fixes \<phi>
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
        by (meson expr_4_read local.read_pos(2) read_pos.hyps)
      show ?thesis
        by (metis A2 A3 enat_ord_simps(1) enat_ord_simps(3) expr.simps formula_prices_list.expr_2_pos formula_prices_list.expr_3_pos formula_prices_list.expr_5_pos formula_prices_list.expr_6_pos less_eq_t.simps one_enat_def)
    qed
  qed
    next
  case (read_conj xs \<alpha> ys)
  then show ?case
    by (smt (verit, best) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) subformula.cases) 
qed

lemma readiness_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  shows "HML_readiness \<phi>"
  by (smt (verit, del_insts) empty_iff formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.set(1) read_conj subformula.cases)

lemma "(HML_readiness \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using readiness_left readiness_right by blast

lemma expr_4_ft_poss:
  fixes \<phi> and \<alpha>
  assumes A1: "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  shows "expr_4 (HML_poss \<alpha> \<phi>) \<le> 0"
proof(cases \<phi>)
  case (HML_conj x11 x12)
  then show ?thesis
    by (smt (verit, ccfv_SIG) empty_iff formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.set(1) subformula.cases)
next
  case (HML_poss x21 x22)
  then show ?thesis
    by (metis A1 expr.simps expr_4.simps(2) formula_prices_list.expr_4_pos less_eq_t.simps of_nat_0 of_nat_eq_enat of_nat_le_iff)
qed

lemma expr_4_rest_left:
  fixes y and ys
  assumes A1: "(\<forall>x\<in>set (y#ys). \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))"
  shows "expr_4_rest (HML_conj [] (y#ys)) = 0" 
  using A1
proof(induction ys)
  case Nil
  then show ?case
    by auto
next
  case (Cons a ys)
  then show ?case 
    by auto
qed

lemma expr_4_rest_ft:
  fixes x and xs and ys
  assumes A1: "x \<in> set xs" and A2: "((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x)) \<and>
       (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
  shows "expr_4_rest (HML_conj [x] ys) = 0" 
proof(cases ys)
  case Nil
  then show ?thesis
    using assms(2) expr_4_ft_poss by auto
next
  case (Cons a ys)
  then show ?thesis
  proof-
    from A2 have A3: "\<exists>\<alpha>. (a = HML_poss \<alpha> (HML_conj [] []))"
      by (simp add: local.Cons) 
    then obtain \<alpha> where "(a = HML_poss \<alpha> (HML_conj [] []))" by (rule exE)
    then have A4: "expr_4_rest a = 0"
      by simp
    from A2 have A5: "(\<forall>y\<in>set (a#ys). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
      using local.Cons by blast
    from this expr_4_rest_left have A6: "expr_4_rest (HML_conj [] ys) = 0"
      by fastforce
    have "expr_4_rest (HML_conj [x] (a#ys)) = Max ({0} \<union> {expr_4_rest x} \<union> {expr_4_rest (HML_conj [] (a#ys))})" 
      by simp
    also have "... = Max ({0} \<union> {expr_4_rest (HML_conj [] (a#ys))})"
      by (metis A2 expr_4.simps(2) expr_4_ft_poss formula_prices_list.expr_4_pos le_zero_eq sup.idem)
    also have "... = Max ({0} \<union> {Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj [] ys)})})" 
      by simp
    also from A6 have "... = Max ({0} \<union> {Max ({0} \<union> {expr_4_rest a} \<union> {0})})" 
      by simp
    also from A4 have "... = 0" 
      by simp
    finally show ?thesis
      using local.Cons by force
  qed
qed

lemma expr_4_ft_conj:
  fixes \<phi> and xs and ys
  assumes A1: "(xs = [] \<and> ys = []) \<or>
  (\<exists>x\<in>set xs.
      ((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x)) \<and>
      (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])))"
  shows "expr_4 (HML_conj xs ys) = 0"
  using A1 
proof(rule disjE)
  assume "xs = [] \<and> ys = []" 
  then show ?thesis 
    by simp
next
  assume A1: "\<exists>x\<in>set xs.
       ((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x)) \<and>
       (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
  then show ?thesis
proof(cases xs)
  case Nil
  then show ?thesis
    using A1 by auto
next
  case (Cons a list)
  assume A2: "xs = (a#list)"
  show ?thesis
    using A1
  proof(rule bexE)
    fix x
    assume A3: "x \<in> set xs" and A4: "((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x)) \<and>
       (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"
    show ?thesis
    proof-
      from A3 A4 have A5: "expr_4_rest (HML_conj [x] ys) = 0" 
        by (rule expr_4_rest_ft)
      from A4 have "(\<forall>y. y \<in> set xs \<longrightarrow> y = x)" 
        by simp
      then have "xs = [x]" 
        by (smt (verit, ccfv_threshold) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) subformula.cases)
      from A4 have "expr_4 x = 0"
        by (simp add: enat_0_iff(1))
      then have A6: "expr_4_rest x = 0"
        by (metis A4 expr_4.simps(2) expr_4_ft_poss expr_4_rest.simps(1) le_0_eq)
      have "expr_4 (HML_conj xs ys) = Max ({expr_4_rest (HML_conj xs ys)} \<union> {expr_4_r (HML_conj (pos_comp_r xs) ys)})"
        by simp
      also have "... = Max ({expr_4_rest (HML_conj [x] ys)} \<union> {expr_4_r (HML_conj (pos_comp_r [x]) ys)})"
        by (simp add: \<open>xs = [x]\<close>)
      also from A5 have "... = Max ({0} \<union> {expr_4_r (HML_conj (pos_comp_r [x]) ys)})"
        by simp 
      also have "... = 0" 
        by simp
      finally show ?thesis by simp
      qed
    qed
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
    have "expr_3 (HML_poss \<alpha> \<phi>) \<le> 0"  (*WTF Warum knn das bewiesen werden? Ist meine definition falsch? oder liegt es am poss case?*)
      by (smt (verit, best) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) subformula.cases)
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
  assume A2: "xs = [] \<and> ys = [] \<or>
  (\<exists>x\<in>set xs.
      ((HML_failure_trace x \<and> less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x)) \<and>
      (\<forall>y\<in>set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])))"
  then show ?case 
  proof-
    from A2 expr_4_ft_conj have A4: "expr_4 (HML_conj xs ys) \<le> 0"
      by (metis le_zero_eq)
      by (rule expr_4_ft_conj) 
    have A5: "expr_5 (HML_conj xs ys) \<le> 1"
      by (smt (verit, best) empty_iff formula_list.inject(1) formula_list.simps(4) formula_prices_list.expr_5_conj_empty indcution_basis_subformula less_eq_nat.simps(1) list.set(1) subformula.cases)
    have A6: "expr_6 (HML_conj xs ys) \<le> 1"
      by (smt (verit, best) empty_iff formula_list.inject(1) formula_list.simps(4) formula_prices_list.expr_6_conj_empty indcution_basis_subformula less_eq_nat.simps(1) list.set(1) subformula.cases)
    from A2 A4 A5 A6 show ?thesis
      by (simp add: one_enat_def zero_enat_def)
  qed
qed

lemma failure_trace_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  shows "(HML_failure_trace \<phi>)"
  using A1
proof(induction \<phi>)
  case (HML_conj x1 x2)
  assume A2: "\<And>x1a. x1a \<in> set x1 \<Longrightarrow> less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x1a" and
A3: "\<And>x2a. x2a \<in> set x2 \<Longrightarrow> less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1) \<Longrightarrow> HML_failure_trace x2a" and
A4: "less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  then show "HML_failure_trace (HML_conj x1 x2)"
  proof(cases x1)
    case Nil
    assume "x1 = []"
    then show ?thesis 
proof(cases x2)
  case Nil
  assume "x2 = []"
  then show ?thesis 
  proof-
    from \<open>x1 = []\<close> \<open>x2 = []\<close> have "x1 = [] \<and> x2 = []" by simp
then show ?thesis
  using f_trace_e_conj by blast
qed
next
  case (Cons a list)
  assume "x2 = (a#list)"
  then show ?thesis 
  proof-
    have "\<forall>y \<in> set (a#list).\<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])" 
from A3 have "\<forall>x2a \<in> set x2. HML_failure_trace x2a" sorry
qed
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
    have "(x1 = [] \<and> x2 = []) \<or> (\<exists>x \<in> set x1. (HML_failure_trace x \<and> (\<forall>y. y \<in> set x1 \<longrightarrow> y = x))
 \<and> (\<forall> y \<in> set x2. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] []))))" sorry
then show ?thesis by (rule HML_list.HML_failure_trace.f_trace_conj)
    from A2 have "\<forall>x1a \<in> set x1. HML_failure_trace x1a"
      by (smt (verit, del_insts) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) subformula.cases)
    from A4 have ""
  qed
  next
  case (HML_poss x1 \<phi>)
  then show ?case sorry
qed

lemma "(HML_failure_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" 

end