theory Impossible_futures
imports Transition_Systems HML formula_prices_list Failure_traces
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
inductive hml_impossible_futures ::  "('a, 's)hml \<Rightarrow> bool"
  where
  if_tt: "hml_impossible_futures TT" |
  if_pos: "hml_impossible_futures (hml_pos \<alpha> \<phi>)" if "hml_impossible_futures \<phi>" |
if_conj: "hml_impossible_futures (hml_conj I J \<Phi>)"
if "I = {}" "\<forall>x \<in> (\<Phi> ` J). (hml_trace x)"

definition hml_impossible_futures_formulas
  where
"hml_impossible_futures_formulas \<equiv> {\<phi>. hml_impossible_futures \<phi>}"

definition expr_impossible_futures
  where
"expr_impossible_futures = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1))}"

context lts
begin

definition expr_impossible_futures_equivalent 
  where
"expr_impossible_futures_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_impossible_futures \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

text \<open>Proposition\<close>

inductive HML_impossible_futures ::  "('a, 's)hml \<Rightarrow> bool"
  where
  if_tt: "HML_impossible_futures TT" |
  if_pos: "HML_impossible_futures (hml_pos \<alpha> \<phi>)" if "HML_impossible_futures \<phi>" |
if_conj: "HML_impossible_futures (hml_conj I J \<Phi>)"
if "\<forall>x \<in> (\<Phi> ` I). TT_like x" "\<forall>x \<in> (\<Phi> ` J). (hml_trace x)"

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
  case (if_conj \<Phi> I J)
  assume pos_tt_like: "\<forall>x \<in> (\<Phi> ` I). TT_like x" and neg_trace: "\<forall>x\<in>\<Phi> ` J. hml_trace x"
  hence "\<forall>x\<in>\<Phi> ` J. expr_3 x = 0"
and "\<forall>x\<in>\<Phi> ` J. expr_2 x = 1"
    using enat_0_iff(2) trace_right expr_2_lb nle_le 
    by fastforce+
  hence "Sup (expr_3 ` \<Phi> ` J) = 0"
    by (metis SUP_bot_conv(2) bot_enat_def)
  have "Sup (expr_3 ` \<Phi> ` I) \<le> 0" 
and "Sup (expr_1 ` \<Phi> ` I) \<le> 0"
    using pos_tt_like bot_enat_def SUP_least e3_tt expr_3_pos le_numeral_extra(3)
     apply metis
    using pos_tt_like bot_enat_def SUP_least e1_tt expr_1_pos le_numeral_extra(3) 
    by (metis add.commute add_0 eSuc_ile_mono eSuc_plus_1)
  hence e3: "expr_3 (hml_conj I J \<Phi>) = 0"
    using expr_3_conj pos_tt_like \<open>Sup (expr_3 ` \<Phi> ` J) = 0\<close> image_comp
    by (metis Sup_union_distrib bot.extremum_uniqueI bot_enat_def sup.orderE)
  have "Sup (expr_2 ` \<Phi> ` J) \<le> 1"
    using \<open>\<forall>x\<in>\<Phi> ` J. expr_2 x = 1\<close>
    by (simp add: Sup_le_iff)
  have "Sup (expr_2 ` \<Phi> ` I) \<le> 1"
    using pos_tt_like bot_enat_def 
    by (metis SUP_least e2_tt expr_2_pos le_numeral_extra(4)) 
  hence e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using pos_tt_like \<open>Sup (expr_2 ` \<Phi> ` J) \<le> 1\<close> one_add_one expr_2_conj
add_left_mono image_Un image_comp
    by (metis (no_types, lifting) Sup_union_distrib sup.bounded_iff)
  have "\<forall>x\<in>\<Phi> ` J. expr_6 x \<le> 0"
    using enat_0_iff(2) trace_right expr.simps less_eq_t.simps neg_trace
    by auto
  hence "Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff one_eSuc)
  have "\<forall>x \<in> (\<Phi> ` I). expr_6 x \<le> 0"
    using expr_TT pos_tt_like expr.simps
    by fastforce
  hence "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    by (metis SUP_image SUP_least)
  hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using expr_6_conj \<open>Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1\<close> pos_tt_like 
    by (simp add: Sup_union_distrib)
  have "\<forall>x\<in>\<Phi> ` J. expr_4 x \<le> 0" 
    using neg_trace trace_right
    by auto
  hence "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
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
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0"
    using \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close> expr_4_conj
    by (simp add: Sup_union_distrib sup.orderE)
  from e2 e3 e4 e6 show ?case using expr.simps less_eq_t.simps
    by auto
qed

lemma e6_e5_le_0:
  assumes "expr_6 \<phi> \<le> 0"
  shows "expr_5 \<phi> \<le> 0"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case by simp
next
  case (hml_pos x1 \<phi>)
  then show ?case by simp
next
  case (hml_conj I J \<Phi>)
  hence sup: "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 0"
    using expr_6_conj by simp
  hence "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 0" "\<forall>x \<in> \<Phi> ` J. expr_5 x \<le> 0"
     apply (metis (no_types, lifting) Sup_upper UnI1 comp_apply image_iff le_zero_eq)
    using sup bot_enat_def empty_iff hml_conj.prems le_zero_eq
    by (metis Sup_union_distrib eSuc_Sup imageI image_comp sup_bot.neutr_eq_iff zero_ne_eSuc)
  hence fa_e5: "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_5 x \<le> 0"
    using hml_conj 
    by force
  have "\<forall>x \<in> \<Phi> ` J. expr_1 x \<le> 0"
  proof(rule ccontr)
    assume "\<not> (\<forall>x\<in>\<Phi> ` J. expr_1 x \<le> 0)"
    then obtain x where "x\<in>\<Phi> ` J" "expr_1 x \<ge> 1" 
      by (metis ileI1 not_le_imp_less one_eSuc)
    have "eSuc (expr_6 x) \<ge> 1"
      by (simp add: one_eSuc)
    hence "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<ge> 1"
      using \<open>x \<in> \<Phi> ` J\<close> empty_iff expr_6.expr_6_conj
      by (smt (verit, del_insts) SUP_bot_conv(2) SUP_image Sup_union_distrib bot.extremum_uniqueI bot_enat_def comp_apply sup sup_bot.neutr_eq_iff)
    then show False using sup by simp
  qed
  with fa_e5 have "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 0"
    using SUP_image SUP_le_iff hml_conj.prems le_zero_eq sup_bot_right
    by (metis (no_types, lifting) Sup_union_distrib image_Un le_sup_iff)
  then show ?case by simp
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
  case (hml_conj x1 x2 x3)
  have "expr_5 (hml_conj x1 x2 x3) = (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))"
    using expr_5_conj by blast
  hence "1 \<le> (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))"
    using hml_conj(2) dual_order.trans 
    by simp
  have e6_eq: "expr_6 (hml_conj x1 x2 x3) = (Sup ((expr_6 \<circ> x3) ` x1 \<union> ((eSuc \<circ> expr_6 \<circ> x3) ` x2)))"
    using expr_6_conj
    by force
  have "(x3 ` x2 \<noteq> {}) \<longrightarrow> Sup(((eSuc \<circ> expr_6 \<circ> x3) ` x2)) \<ge> 1"
    using eSuc_def 
    by (metis eSuc_Sup eSuc_ile_mono empty_iff equals0I i0_lb imageI image_comp one_eSuc)
  hence "(x3 ` x2 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)"
    by (simp add: Sup_union_distrib le_supI2)
  have "(x3 ` x2 = {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)"
  proof
    assume "x3 ` x2 = {}"
    hence "1 \<le> (Sup ((expr_5 \<circ> x3) ` x1))" 
      using \<open>1 \<le> (Sup ((expr_5 \<circ> x3) ` x1 \<union> (expr_5 \<circ> x3) ` x2 \<union> (expr_1 \<circ> x3) ` x2))\<close>
      using bot_enat_def by force
    then obtain x where "x \<in> (x3 ` x1)" "1 \<le> expr_5 x"
      using bot_enat_def comp_apply
      by (metis (no_types, lifting) SUP_bot_conv(2) iless_eSuc0 image_eqI linorder_not_le one_eSuc)
    hence "1 \<le> expr_6 x"
      using hml_conj
      by blast
    hence "Sup ((expr_6 \<circ> x3) ` x1) \<ge> 1"
      using \<open>x \<in> (x3 ` x1)\<close> SUP_image SUP_lessD linorder_not_le 
      by metis
    then show "1 \<le> expr_6 (hml_conj x1 x2 x3)" 
      using expr_6_conj e6_eq \<open>x3 ` x2 = {}\<close> by auto
  qed
  with \<open>(x3 ` x2 \<noteq> {}) \<longrightarrow> (expr_6 (hml_conj x1 x2 x3) \<ge> 1)\<close> 
  show "1 \<le> expr_6 (hml_conj x1 x2 x3)"
    by blast
qed

lemma expr_2_le_2_is_trace: 
  assumes "expr_2 (hml_conj I J \<Phi>) \<le> 2"
  shows "\<forall>x \<in> (\<Phi> ` I \<union> \<Phi> ` J). (hml_trace x)"
proof
  fix x
  assume "x \<in> (\<Phi> ` I \<union> \<Phi> ` J)"
  from assms have "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` J). x <= 1"
and "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x <= 1"
    using expr_2_conj
    using Sup_union_distrib Sup_upper dual_order.order_iff_strict one_eSuc plus_1_eSuc(1) one_add_one
    by (smt (verit) eSuc_ile_mono le_sup_iff order_trans)+
  hence e2: "expr_2 x \<le> 1"
    using \<open>x \<in> (\<Phi> ` I \<union> \<Phi> ` J)\<close>
    by fastforce
  show " hml_trace x"
    using e2
  proof(induction x)
    case TT
    then show ?case 
      using hml_trace.simps
      by blast
  next
    case (hml_pos x21 x22)
    then show ?case 
      using hml_trace.simps
      by fastforce 
  next
    case (hml_conj x31 x32 x33)
    from \<open>expr_2 (hml_conj x31 x32 x33) \<le> 1\<close> expr_2_le_1
    show ?case using hml_trace.simps
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
  case (hml_conj I J \<Phi>)
  have "\<forall>x \<in> (\<Phi> ` J). (hml_trace x)"
    using expr_2_le_2_is_trace expr.simps hml_conj.prems less_eq_t.simps
    by (metis Un_iff)
  from hml_conj have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 2"
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
      hence "expr_3 (hml_conj I J \<Phi>) \<ge> 1"
        using expr_3_conj 
        by (metis Sup_union_distrib bot_enat_def iless_eSuc0 linorder_not_le one_eSuc sup_eq_bot_iff)
      with hml_conj(2) have False
        by auto
      then show ?thesis by blast
    next
      case (hml_conj x31 x32 x33)
      have "\<forall>x \<in> (x33 ` x31 \<union> x33 ` x32). expr_2 x \<ge> 1"
        using expr_2_lb
        by blast
      hence "(x33 ` x31 \<union> x33 ` x32) \<noteq> {} \<longrightarrow> expr_2 x \<ge> 2"
        using hml_conj expr_2_lb expr_2_le_1
        by (metis dual_order.order_iff_strict ileI1 one_add_one plus_1_eSuc(1) sup_eq_bot_iff) 
      hence "(x33 ` x31 \<union> x33 ` x32) \<noteq> {} \<longrightarrow> Sup ((expr_2 \<circ> \<Phi>) ` I) \<ge> 2"
        using SUP_image SUP_lessD \<open>x \<in> \<Phi> ` I\<close> linorder_not_le
        by metis
      hence "(x33 ` x31 \<union> x33 ` x32) \<noteq> {} \<longrightarrow> expr_2 (hml_conj I J \<Phi>) \<ge> 3"
        using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close>
        by (metis  dual_order.trans numeral_le_one_iff semiring_norm(69))
      hence "(x33 ` x31 \<union> x33 ` x32) \<noteq> {} \<longrightarrow> False" 
        using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> 
\<open>x33 ` x31 \<union> x33 ` x32 \<noteq> {} \<longrightarrow> 2 \<le> Sup ((expr_2 \<circ> \<Phi>) ` I)\<close>
        by (meson  numeral_le_one_iff order_trans semiring_norm(69))
      hence "x33 ` x31 = {}" "x33 ` x32 = {}"
        by blast+
      then show ?thesis
        by (simp add: TT_like.intros(2) hml_conj)
    qed
  qed
  then show ?case using \<open>\<forall>x \<in> (\<Phi> ` J). (hml_trace x)\<close> if_conj
    by (simp add: if_conj)
qed

lemma impossible_futures_lemma:
  shows "HML_impossible_futures \<phi> = less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, \<infinity>, 1)"
  using impossible_futures_left impossible_futures_right by blast

context lts begin
lemma alt_impossible_futures_def_implies_impossible_futures_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_impossible_futures \<phi>"
  shows "\<exists>\<psi>. HML_impossible_futures \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case if_tt
  then show ?case 
    using HML_impossible_futures.if_tt by blast
next
  case (if_pos \<phi> \<alpha>)
  then show ?case 
    using HML_impossible_futures.if_pos by fastforce
next
  case (if_conj I \<Phi> J)
  hence "HML_impossible_futures (hml_conj I J \<Phi>)" 
    by (simp add: Impossible_futures.HML_impossible_futures.if_conj)
  then show ?case by blast
qed

lemma impossible_futures_def_implies_alt_impossible_futures_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_impossible_futures \<phi>"
  shows "\<exists>\<psi>. hml_impossible_futures \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case if_tt
  then show ?case 
    using hml_impossible_futures.if_tt by blast
next
  case (if_pos \<phi> \<alpha>)
  then show ?case 
    using hml_impossible_futures.if_pos by force
next
  case (if_conj \<Phi> I J)
  hence "\<forall>x \<in> \<Phi>`J. (\<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> x \<longleftrightarrow> s \<Turnstile> \<psi>))"
    by blast
  hence "\<forall>j \<in> J. (\<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>))"
    by blast
  hence "\<And>j. j \<in> J \<Longrightarrow> \<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>)" by blast
  define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J then (SOME \<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> i \<longleftrightarrow> s \<Turnstile> \<psi>)) 
                              else undefined))"
  have "\<And>j. j \<in> J \<Longrightarrow> hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)"
    unfolding \<Psi>_def using \<open>\<And>j. j \<in> J \<Longrightarrow> \<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>)\<close>
    by (smt (verit, ccfv_SIG) someI)
  hence "\<forall>j \<in> J. hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)" 
    by blast
  hence "hml_impossible_futures (hml_conj {} J \<Psi>)" 
    using hml_impossible_futures.simps by fastforce
  have "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {} J \<Psi>)" 
    using HML_true_TT_like HML_true_def \<open>\<forall>j \<in> J. hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)\<close> if_conj.hyps(1) by auto
  then show ?case 
    using \<open>hml_impossible_futures (hml_conj {} J \<Psi>)\<close> by blast
qed

end
end