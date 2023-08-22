theory HML_subsets
  imports 
    "HOL-Library.Extended_Nat"
    Main
    HML_list
  formula_prices_list
begin

value "\<infinity>::enat"

datatype inat = N nat | Inf

fun less_eq :: "nat \<Rightarrow> inat \<Rightarrow> bool"
where
  "less_eq n (N m) = (n \<le> m)" |
  "less_eq _ Inf = True"

fun less_eq_t :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> bool"
  where
"less_eq_t (n1, n2, n3, n4, n5, n6) (i1, i2, i3, i4, i5, i6) =
    (n1 \<le> i1 \<and> n2 \<le> i2 \<and> n3 \<le> i3 \<and> n4 \<le> i4 \<and> n5 \<le> i5 \<and> n6 \<le> i6)"

thm HML_trace.induct

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
proof(cases \<phi>)
  case (HML_conj x1 x2)
  then show ?thesis 
  proof-
    from A1 HML_trace_conj_empty have "x1 = [] \<and> x2 = []"
      using HML_conj by blast
      then show ?thesis
        using HML_conj trace_conj by blast
    qed
next
  case (HML_poss \<alpha> \<psi>)
  then show ?thesis 
    by (smt (verit, del_insts) formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.distinct(1) list.set_cases subformula.simps)
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

lemma simulation_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  shows "(HML_simulation \<phi>)"
proof(induction \<phi>)
  case (HML_conj x1 x2)
  then show ?case 
  proof-
      assume A2: "(\<And>x1a. x1a \<in> set x1 \<Longrightarrow> HML_simulation x1a)" 
and  A3: "(\<And>x2a. x2a \<in> set x2 \<Longrightarrow> HML_simulation x2a)"
    show "HML_simulation (HML_conj x1 x2)"
    proof-
      (*from A1 have A1: "(less_eq_t (expr (HML_conj x1 x2)) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))" sorry*)
      from A2 have A2: "\<forall>x1a \<in> set x1. HML_simulation x1a" by simp
      from A3 have A3: "\<forall>x2a \<in> set x2. HML_simulation x2a" by simp
      from A2 have "\<forall>x1a \<in> set x1. (less_eq_t (expr x1a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
        using simulation_right by blast
      from A3 have "\<forall>x2a \<in> set x2. (less_eq_t (expr x2a) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
        using simulation_right by blast
      have A4: "x2 = []"
        by (smt (verit) empty_iff empty_set formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula subformula.simps)
      have A5: "(\<forall>x1a \<in> (set x1). HML_simulation x1a)\<longrightarrow>HML_simulation (HML_conj  x1 [])"
        using HML_simulation.sim_conj by blast
      from this A4 show ?case
        using A2 by blast
    qed
  qed
next
  case (HML_poss x1 \<phi>)
  then show ?case by (rule HML_list.HML_simulation.intros(1))
qed

lemma "(HML_simulation \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 0, 0))"
  using simulation_left simulation_right by blast

lemma expr_4_fail:
  fixes \<phi> :: "('a)formula_list" and \<alpha>
  assumes A1: "HML_failure (HML_poss \<alpha> \<phi>)" and A2: "less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1)"
  shows "expr_4 (HML_poss \<alpha> \<phi>) = 0"
proof(cases \<phi>)
  have A2: "expr_4 \<phi> = 0"
    using A2 enat_0_iff(2) by auto
  from A1 have A3: "HML_failure \<phi>"
    using HML_failure.cases by blast
  case (HML_conj x11 x12)
  then show ?thesis
  proof-
    from A3 have "x11 = []"
      using HML_conj HML_failure.simps by force
    from A1 have A4: "\<forall>y \<in> set x12. \<exists>\<beta>. y = (HML_poss \<beta> (HML_conj [] []))"
      by (metis A3 HML_conj HML_failure.cases formula_list.distinct(1) formula_list.inject(1))
    from A2 have "expr_4 (HML_conj x11 x12) = 0"
      using HML_conj by blast
    show ?thesis
    proof-
      have "expr_4 (HML_poss \<alpha> \<phi>) = expr_4_rest (HML_poss \<alpha> \<phi>)"
        by simp
      also have "... = expr_4_rest \<phi>"
        by simp
      also have "... = expr_4_rest (HML_conj [] x12)"
        by (simp add: HML_conj \<open>x11 = []\<close>)
      also have "... = 0"
        using A4
      proof(induction x12)
        case Nil
        then show ?case by simp
      next
        case (Cons a x12)
        then show ?case 
        proof-
          assume A2: "(\<forall>y\<in>set x12. \<exists>\<beta>. y = HML_poss \<beta> (HML_conj [] []) \<Longrightarrow> expr_4_rest (HML_conj [] x12) = 0)"
and A3: "\<forall>y\<in>set (a # x12). \<exists>\<beta>. y = HML_poss \<beta> (HML_conj [] [])"
          then show ?thesis
          proof-
            from A3 have "\<exists>\<beta>. a = (HML_poss \<beta> (HML_conj [] []))" 
              by simp
            then have A4: "expr_4_rest a = 0" 
              by auto
            have "expr_4_rest (HML_conj [] (a # x12)) = 
            Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj [] x12)})" 
              by simp
            also have "... = Max ({0} \<union> {expr_4_rest a} \<union> {0})"
              by (simp add: A2 A3)
            also have "... = 0"
              by (simp add: A4)
            finally show ?thesis 
              by this
          qed
        qed
      qed
      finally show ?thesis by this
    qed
  qed
next
  case (HML_poss x21 x22)
  then show "expr_4 (HML_poss \<alpha> \<phi>) = 0"
    using A2 enat_0_iff(2) by auto
qed

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
Max ({expr_4_rest (HML_conj [] (a#x2))} \<union> {expr_4_r (HML_conj (pos_comp_r []) x2)})"
        by simp
      also have "... = Max ({Max ({0} \<union> {expr_4_rest a} \<union> {expr_4_rest (HML_conj [] x2)})} \<union> {0})"
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
      by (metis HML_failure.trace expr_4_fail le_eq_less_or_eq trace.IH trace.hyps)
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
    by (metis A2 expr.simps expr_4.simps(2) formula_prices_list.expr_4_pos less_eq_t.simps of_nat_1 of_nat_eq_enat of_nat_le_iff) sorry
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
    by (smt (verit, best) empty_iff formula_list.inject(1) formula_list.simps(4) indcution_basis_subformula list.set(1) subformula.cases) sorry
qed
  

lemma readiness_left:
  fixes \<phi>
  assumes A1: "(less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  shows "HML_readiness \<phi>"
  by (smt (verit, del_insts) empty_iff formula_list.distinct(1) formula_list.inject(1) indcution_basis_subformula list.set(1) read_conj subformula.cases)

lemma "(HML_readiness \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using readiness_left readiness_right by blast

end