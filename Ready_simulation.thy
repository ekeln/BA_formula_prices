theory Ready_simulation
imports Transition_Systems HML formula_prices_list Simulation Ready_traces
begin

subsection \<open>Failures semantics\<close>

text \<open>\<close>
text \<open>\<close>
inductive hml_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"hml_ready_sim TT" |
"hml_ready_sim (hml_pos \<alpha> \<phi>)" if "hml_ready_sim \<phi>" |
"hml_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). hml_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). (\<exists>\<alpha>. y = (hml_pos \<alpha> TT)) \<or> y = TT)"

definition hml_ready_sim_formulas where
  "hml_ready_sim_formulas \<equiv> {\<phi>. hml_ready_sim \<phi>}"

definition expr_ready_sim
  where
"expr_ready_sim = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1))}"

context lts
begin

definition expr_ready_sim_equivalent 
  where
"expr_ready_sim_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_ready_sim \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

text \<open>Proposition\<close>

inductive HML_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"HML_ready_sim TT" |
"HML_ready_sim (hml_pos \<alpha> \<phi>)" if "HML_ready_sim \<phi>" |
"HML_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). HML_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"

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
    using 3 SUP_image SUP_least expr.simps image_is_empty less_eq_t.simps sup_bot_right
    by (metis expr_6.expr_6_conj)
  then show ?case 
    by (metis \<open>expr_1 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_3 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_4 (hml_conj I J \<Phi>) \<le> 1\<close> enat_ord_code(3) expr.elims less_eq_t.simps)
qed

lemma ready_sim_right:
  assumes "HML_ready_sim \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
  using assms
proof(induction \<phi> rule:HML_ready_sim.induct)
  case 1
  then show ?case 
    by simp 
next
  case (2 \<phi> \<alpha>) 
  then show ?case 
    by simp
next
  case (3 \<Phi> I J)
  hence "\<forall>y\<in>\<Phi> ` J. less_eq_t (expr y) (1, \<infinity>, 1, 1, 0, 0)"
    using expr_single_pos_pos 
    by (metis Ready_traces.single_pos_pos.intros(2) nested_empty_pos_conj.intros(1))
  hence fa_neg: "\<forall>y \<in>\<Phi> ` J.  expr_1 y \<le> 1"
"\<forall>y \<in>\<Phi> ` J.  expr_5 y \<le> 0"
"\<forall>y \<in>\<Phi> ` J.  expr_6 y \<le> 0"
    using less_eq_t.simps expr.simps 
    by force+
  from 3 have "\<forall>x\<in>\<Phi> ` I. less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
    by blast
  hence fa_pos: "\<forall>x \<in>\<Phi> ` I.  expr_5 x \<le> 1" "\<forall>x \<in>\<Phi> ` I.  expr_6 x \<le> 1"
    using less_eq_t.simps expr.simps 
    by force+
  with fa_neg have e5: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
    by (simp add: SUP_least Sup_union_distrib)
  from fa_neg have "Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def 
    by (simp add: SUP_least one_eSuc)
  with fa_neg fa_pos have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    by (simp add: SUP_least Sup_union_distrib)
  then show ?case using e5 less_eq_t.simps expr.simps 
    by simp
qed

lemma expr_5_expr_6_le_1_stacked_pos_conj_J_empty_neg:
  assumes "expr_5 (hml_conj I J \<Phi>) \<le> 1" "expr_6 (hml_conj I J \<Phi>) \<le> 1"
  shows "(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_J_empty y)"
proof
  fix y
  assume "y \<in> \<Phi> ` J"
  have sup: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
"(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    using assms expr_5_conj expr_6_conj
    by force+
  hence "expr_5 y \<le> 1" "expr_1 y \<le> 1" "expr_6 y \<le> 0"
      prefer 3 using \<open>y \<in> \<Phi> ` J\<close> sup 
    apply (metis Sup_le_iff UnCI comp_apply eSuc_ile_mono image_iff one_eSuc)
    using \<open>y \<in> \<Phi> ` J\<close> sup 
    by (metis Sup_le_iff UnCI comp_apply image_iff)+
  then show "stacked_pos_conj_J_empty y"
  proof(induction y)
    case TT
    then show ?case 
      using stacked_pos_conj_J_empty.intros(1) by blast
  next
    case (hml_pos x1 \<chi>)
    hence "expr_1 \<chi> \<le> 0"
"expr_6 \<chi> \<le> 1"
"expr_5 \<chi> \<le> 1"
      using expr_1_pos expr_6_pos
      by simp+
    hence "stacked_pos_conj_J_empty \<chi>"
      using hml_pos.IH hml_pos.prems(3) by auto
    then show ?case 
      using stacked_pos_conj_J_empty.simps by blast
  next
    case (hml_conj x1 x2 x3)
    hence "Sup ((eSuc \<circ> expr_6 \<circ> x3) ` x2) \<le> 0"
      using Sup_union_distrib expr_6_conj
      by (metis SUP_image Sup_empty bot_enat_def image_empty le_zero_eq not_one_le_zero)
    hence "\<forall>x \<in> x3 ` x2. eSuc (expr_6 x) \<le> 0"
      by (metis SUP_image eSuc_Sup empty_iff empty_is_image not_eSuc_ilei0)
    hence "x3 ` x2 = {}"
      by simp
    have "Sup ((expr_5 \<circ> x3) ` x1) \<le> 1"
"Sup ((expr_1 \<circ> x3) ` x1) \<le> 1"
"Sup ((expr_6 \<circ> x3) ` x1) \<le> 0"
      using expr_1_conj expr_5_conj expr_6.expr_6_conj Sup_union_distrib hml_conj
      using \<open>x3 ` x2 = {}\<close> by force+
    hence "\<forall>x \<in> x3 ` x1. expr_1 x \<le> 1"
"\<forall>x \<in> x3 ` x1. expr_5 x \<le> 1"
"\<forall>x \<in> x3 ` x1. expr_6 x \<le> 0"
      using Sup_le_iff 
      by (metis SUP_image imageI)+
    hence "\<forall>x \<in> x3 ` x1. stacked_pos_conj_J_empty x"
      using hml_conj 
      by blast
    then show ?case using \<open>x3 ` x2 = {}\<close> stacked_pos_conj_J_empty.simps 
      by fastforce
  qed
qed

lemma ready_sim_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
  shows "HML_ready_sim \<phi>"
  using assms
  proof (induction \<phi>)
    case TT
    then show ?case 
      using HML_ready_sim.intros(1) by blast
  next
    case (hml_pos x1 \<phi>)
    then show ?case 
      by (simp add: HML_ready_sim.intros(2)) 
  next
    case (hml_conj I J \<Phi>)
    hence "expr_5 (hml_conj I J \<Phi>) \<le> 1"
  "expr_6 (hml_conj I J \<Phi>) \<le> 1"
      by (metis expr.simps less_eq_t.simps)+
    hence "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 1"
  "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
      using expr_5_conj expr_6.expr_6_conj Sup_union_distrib 
      by (metis le_sup_iff)+
    hence "\<forall>x \<in> \<Phi> ` I. expr_5 x \<le> 1" "\<forall>x \<in> \<Phi> ` I. expr_6 x \<le> 1"
      using Sup_le_iff
      by (metis image_comp image_eqI)+   
    hence "\<forall>x \<in> \<Phi> ` I. less_eq_t (expr x) (\<infinity>, \<infinity>, \<infinity>, \<infinity>, 1, 1)"
      by simp
    hence "\<forall>x \<in> \<Phi> ` I. HML_ready_sim x" using hml_conj
      by blast
    have "Sup((expr_5 \<circ> \<Phi>) ` J) \<le> 1" "Sup((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
      using \<open>expr_5 (hml_conj I J \<Phi>) \<le> 1\<close>
      by (simp add: Sup_union_distrib)+
    hence "\<forall>x \<in> \<Phi> ` J. expr_1 x \<le> 1"
      using Sup_le_iff
      by (metis image_comp image_eqI)
    have "Sup((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) <= 1"
      using \<open>expr_6 (hml_conj I J \<Phi>) \<le> 1\<close>
      by (simp add: Sup_union_distrib)
    hence "Sup((expr_6 \<circ> \<Phi>) ` J) <= 0"
      by (metis (no_types, opaque_lifting) SUP_image Sup_enat_def eSuc_Sup eSuc_ile_mono one_eSuc zero_le)
    hence "\<forall>x \<in> \<Phi> ` J. expr_6 x \<le> 0"
      using Sup_le_iff
      by (metis image_comp image_eqI)
    with \<open>\<forall>x \<in> \<Phi> ` J. expr_1 x \<le> 1\<close> have "\<forall>x \<in> \<Phi> ` J. single_pos_pos x"
      using single_pos_pos_expr by blast
    then show ?case using \<open>\<forall>x \<in> \<Phi> ` I. HML_ready_sim x\<close> hml_ready_sim.intros(3) 
      by (meson Ready_simulation.HML_ready_sim.intros(3))
qed

context lts begin

lemma alt_single_pos_pos:
  fixes s::'s
  assumes "single_pos_pos \<phi>" "\<not> HML_true \<phi>"
  shows "\<forall>s. \<exists>I \<Phi>. 
          (s \<Turnstile> \<phi>) = (s \<Turnstile> (hml_conj I {} \<Phi>)) \<and> (\<forall>\<psi> \<in> \<Phi> ` I. (\<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT))"
  using assms proof(induct)
  case 1
  then show ?case 
    using TT_like.intros(1) lts.HML_true_TT_like 
    by auto
next
  case (2 \<psi> \<alpha>)
  hence "HML_true \<psi>" 
    using HML_true_nested_empty_pos_conj by blast
  define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = s then (hml_pos \<alpha> TT)::('a, 's)hml else undefined))"
  hence "\<forall>t. (t \<Turnstile> (hml_pos \<alpha> \<psi>)) = (t \<Turnstile> (hml_conj {s} {} \<Psi>))" 
    using HML_true_def \<open>HML_true \<psi>\<close> by auto 
  hence "\<forall>t. (t \<Turnstile> hml_pos \<alpha> \<psi>) = (t \<Turnstile> hml_conj {s} {} \<Psi>) \<and> (\<forall>\<psi>\<in>\<Psi> ` {s}. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)"
    using HML_true_def \<Psi>_def \<open>HML_true \<psi>\<close> by force
  then show ?case by blast
next
  case (3 \<Phi> I J)
  show "\<forall>s. \<exists>Ia \<Phi>'.
              (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj Ia {} \<Phi>') \<and> (\<forall>\<psi>\<in>\<Phi>' ` Ia. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)"
  proof
    fix s::'s
    define Is where "Is \<equiv> {t. (\<exists>\<alpha>. t \<in> derivatives t \<alpha>)}"
      
  show "\<exists>Ia \<Phi>'.
          (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj Ia {} \<Phi>') \<and> (\<forall>\<psi>\<in>\<Phi>' ` Ia. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)"
    sorry
  
  qed
qed

lemma single_pos_pos_equiv_to_pos_conj:
  fixes s::'s
  assumes "single_pos_pos \<phi>" "\<not>HML_true \<phi>"
  shows "\<exists>I \<Phi>. (\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> (hml_conj I {} \<Phi>)) \<and> (\<forall>\<psi> \<in> \<Phi> ` I. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT))"
  using assms proof(induct)
  case 1
  then show ?case 
    using TT_like.intros(1) lts.HML_true_TT_like by blast
next
  case (2 \<psi> \<alpha>)
  hence "HML_true \<psi>" 
    using HML_true_nested_empty_pos_conj by blast
  define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = s then (hml_pos \<alpha> TT)::('a, 's)hml else undefined))"
  hence "\<forall>t. (t \<Turnstile> (hml_pos \<alpha> \<psi>)) = (t \<Turnstile> (hml_conj {s} {} \<Psi>))" 
    using HML_true_def \<open>HML_true \<psi>\<close> by auto 
  hence "\<forall>t. (t \<Turnstile> hml_pos \<alpha> \<psi>) = (t \<Turnstile> hml_conj {s} {} \<Psi>) \<and> (\<forall>\<psi>\<in>\<Psi> ` {s}. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)"
    using HML_true_def \<Psi>_def \<open>HML_true \<psi>\<close> by force
  then show ?case by blast
next
  case (3 \<Phi> I J)
  have "\<forall>s. (s \<Turnstile> (hml_conj I J \<Phi>)) = (s \<Turnstile> (hml_conj (I-{i. HML_true (\<Phi> i)}) J \<Phi>))" 
    using DiffD1 DiffI HML_true_def by auto
  define reach_der where "reach_der \<equiv> {s. \<exists>t \<alpha>. s \<in> derivatives t \<alpha>}"
  define univ_set where "univ_set \<equiv> {x::'s.True}"
  define pos_set where "pos_set \<equiv> {\<psi>. \<exists>\<phi> \<in> \<Phi> ` I. \<exists>I' \<Phi>'. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> (hml_conj I' {} \<Phi>'))
                                                                 \<and> \<psi> \<in> \<Phi>' ` I'}"
  have "(\<nexists>f::'s \<Rightarrow>('a, 's)hml. \<forall>x \<in> pos_set. \<exists>i \<in> univ_set. f i = x) 
          \<longrightarrow> (\<forall>s. \<not> s \<Turnstile> (hml_conj I J \<Phi>))"
  proof
    assume "\<nexists>f. \<forall>x\<in>pos_set. \<exists>i\<in>univ_set. f i = x"
    show "\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>" proof
      fix t ::'s
      {
        assume "t \<Turnstile> (hml_conj I J \<Phi>)"
        have "\<exists>f::'s \<Rightarrow> ('a, 's) hml. \<forall>x \<in> pos_set. \<exists>i \<in> univ_set. f i = x" 
        proof-
          have "I \<union> J \<subseteq> univ_set"
            unfolding univ_set_def by blast

          have "\<forall>x \<in> pos_set. \<exists>i \<in> univ_set. \<Phi> i = x" sorry
        proof(rule ccontr)
      }
  qed
  show " \<exists>Ia \<Phi>'.
          \<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj Ia {} \<Phi>') \<and> (\<forall>\<psi>\<in>\<Phi>' ` Ia. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT) "
  proof(cases "(\<nexists>f::'s \<Rightarrow>('a, 's)hml. \<forall>x \<in> pos_set. \<exists>i \<in> reach_der. f i = x)")
    case True
    then show ?thesis sorry
  next
    case False
    then obtain f where "\<forall>x\<in>pos_set. \<exists>i\<in>reach_der. f i = x" by blast
    have "\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj reach_der {} f) \<and> (\<forall>\<psi>\<in>f ` reach_der. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)"
    sorry
    then show ?thesis sorry
  qed
  
  define Indexunion where "Indexunion \<equiv> {J. (\<exists>\<phi> \<in> \<Phi> ` I. (\<exists>\<Phi>. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_conj I {} \<Phi>) \<and> (\<forall>\<psi>\<in>\<Phi> ` I. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT)))}"
  have "card Indexunion \<ge> card "
  have ""
  consider "\<forall>I' J'. "
  then show ?case sorry
qed

lemma alt_ready_sim_implies_ready_sim:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_ready_sim \<phi>"
  shows "\<exists>\<psi>. HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case 1
  then show ?case 
    using Ready_simulation.HML_ready_sim.intros(1) by blast
next
  case (2 \<phi> \<alpha>)
  then obtain \<psi> where "HML_ready_sim \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "HML_ready_sim (hml_pos \<alpha> \<psi>)" 
    using Ready_simulation.HML_ready_sim.simps by blast
  then show ?case 
    by (meson \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close> hml_sem_pos)
next
  case (3 \<Phi> I J)
  consider "I \<inter> J = {} \<and> (\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. y = hml_pos \<alpha> TT)" 
    | "(\<exists>i. i \<in> (I \<inter> J)) \<and> (\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. y = hml_pos \<alpha> TT)" 
    | "(\<exists>j \<in> J. \<Phi> j = TT)"
    using "3" by blast
  then show ?case proof(cases)
    case 1
    hence "(\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. y = hml_pos \<alpha> TT)" 
      using "3"
      by simp
    have "\<forall>\<alpha>. single_pos_pos (hml_pos \<alpha> TT)" 
      using Ready_traces.single_pos_pos.simps nested_empty_pos_conj.intros(1) by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> I
                            then (SOME \<psi>. HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))) 
                            else (if i \<in> J then \<Phi> i else undefined)))"
    have "\<forall>j \<in> I. \<exists>\<psi>. HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<psi>))"
      using "3" by blast
    hence "\<forall>i\<in> I. \<exists>\<psi>. \<Psi> i = \<psi> \<and> HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))" 
      unfolding \<Psi>_def someI_ex
      by (smt (verit) someI_ex)
    hence "\<forall>j \<in> I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)" 
      using "3" "1" Ready_simulation.HML_ready_sim.intros image_iff \<Psi>_def 
      by blast
    have "\<forall>i \<in> J. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)"
      using "1" "3"
      unfolding \<Psi>_def 
      by force
    have "\<forall>i \<in> J. single_pos_pos (\<Psi> i)"
      unfolding \<Psi>_def
      using "1" "3" \<open>\<forall>\<alpha>. Ready_traces.single_pos_pos (hml_pos \<alpha> TT)\<close>
      by fastforce
    hence "HML_ready_sim (hml_conj I J \<Psi>)" 
      using \<open>\<forall>j \<in> I. \<exists>\<psi>. HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<psi>))\<close> 
      by (metis (mono_tags, lifting) Ready_simulation.HML_ready_sim.intros(3) \<open>\<forall>i\<in>I. \<exists>\<psi>. \<Psi> i = \<psi> \<and> Ready_simulation.HML_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))\<close> image_iff)
    have "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Psi>)))"
      by (simp add: \<open>\<forall>i\<in>J. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)\<close> \<open>\<forall>j\<in>I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)\<close>)
    then show ?thesis 
      using "1" HML_ready_sim.intros(1) \<open>\<forall>j \<in> I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)\<close> \<open>Ready_simulation.HML_ready_sim (hml_conj I J \<Psi>)\<close> by blast
  next
    case 2
    assume  "(\<exists>i. i \<in> I \<inter> J) \<and> (\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. y = hml_pos \<alpha> TT)"
      then obtain i where "i \<in> I \<inter> J" by blast
      hence "\<forall>s. \<not>((s \<Turnstile> (\<Phi> i)) \<and> (\<not>(s \<Turnstile> (\<Phi> i))))" 
        by blast
      hence "\<forall>s. \<not>((\<forall>i \<in> I. s \<Turnstile> (\<Phi> i)) \<and> (\<forall>j \<in> J. \<not>(s \<Turnstile> (\<Phi> j))))"
        using \<open>i \<in> I \<inter> J\<close> by blast
      hence "\<forall>s. \<not>s\<Turnstile>(hml_conj I J \<Phi>)" 
        using hml_sem_conj by presburger
      have "single_pos_pos (\<Phi> i)"
        using \<open>i \<in> I \<inter> J\<close> "3"
        using "2" Ready_traces.single_pos_pos.intros(2) nested_empty_pos_conj.intros(1) by fastforce
      hence "HML_ready_sim (\<Phi> i)" 
        using "3" Ready_simulation.HML_ready_sim.intros(1) Ready_simulation.HML_ready_sim.intros(2) \<open>i \<in> I \<inter> J\<close> by fastforce
      hence "HML_ready_sim (hml_conj {i} {i} \<Phi>)" 
        using \<open>single_pos_pos (\<Phi> i) \<close>
        by (simp add: Ready_simulation.HML_ready_sim.intros(3))
      have "\<forall>s. \<not>s\<Turnstile>(hml_conj {i} {i} \<Phi>)" 
        by simp
      then show ?thesis 
        using \<open>Ready_simulation.HML_ready_sim (hml_conj {i} {i} \<Phi>)\<close> \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> by blast
    next
      case 3
      assume "\<exists>j\<in>J. \<Phi> j = TT"
      then obtain j where "j\<in> J" "\<Phi> j = TT" by blast
      hence "\<forall>s. \<not>s\<Turnstile>(hml_conj I J \<Phi>)" 
        by fastforce
      have "HML_ready_sim (hml_conj {} {j} \<Phi>)" 
        by (smt (verit, del_insts) Ready_simulation.HML_ready_sim.intros(3) Ready_traces.single_pos_pos.simps \<open>\<Phi> j = TT\<close> ball_empty image_empty image_insert insert_iff)
      have "\<forall>s. \<not>s\<Turnstile>(hml_conj {} {j} \<Phi>)" 
        by (simp add: \<open>\<Phi> j = TT\<close>)
      then show ?thesis using \<open>HML_ready_sim (hml_conj {} {j} \<Phi>)\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> by blast
    qed
qed

lemma ready_sim_implies_alt_ready_sim:
fixes \<phi> :: "('a, 's) hml"
  assumes "HML_ready_sim \<phi>"
  shows "\<exists>\<psi>. hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case 1
  then show ?case 
    using hml_ready_sim.intros(1) by blast
next
  case (2 \<phi> \<alpha>)
  then obtain \<psi> where "hml_ready_sim \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "hml_ready_sim (hml_pos \<alpha> \<psi>)" 
    using Ready_simulation.hml_ready_sim.simps by blast
  then show ?case 
    by (meson \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close> hml_sem_pos)
next
  case (3 \<Phi> I J)
  consider "I \<inter> J = {} \<and> (\<forall>y\<in>\<Phi> ` J. single_pos_pos y \<and> \<not>HML_true y)" 
    | "(\<exists>i. i \<in> (I \<inter> J))" 
    | "(\<exists>j \<in> J. HML_true (\<Phi> j))"
    using "3" by blast
  then show ?case proof(cases)
    case 1
    hence "(\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) = (s \<Turnstile> (hml_pos \<alpha> TT))))" 
      using "3" single_pos_pos_equiv_to_pos by blast
    have "\<forall>\<alpha>. single_pos_pos (hml_pos \<alpha> TT)" 
      using Ready_traces.single_pos_pos.simps nested_empty_pos_conj.intros(1) by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> I
                            then (SOME \<psi>. hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))) 
                            else (if i \<in> J then (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> (\<Phi> i)) = (s \<Turnstile> (hml_pos \<alpha> TT)))) TT) else undefined)))"
    have "\<forall>j \<in> I. \<exists>\<psi>. hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<psi>))"
      using "3" by blast
    hence "\<forall>i\<in> I. \<exists>\<psi>. \<Psi> i = \<psi> \<and> hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))" 
      unfolding \<Psi>_def someI_ex
      by (smt (verit) someI_ex)
    hence "\<forall>j \<in> I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)" 
      using "3" "1" Ready_simulation.HML_ready_sim.intros image_iff \<Psi>_def 
      by blast
    have "\<forall>i \<in> J. \<exists>\<alpha>. \<Psi> i = (hml_pos \<alpha> TT)"
      using "1" "3" \<open>(\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) = (s \<Turnstile> (hml_pos \<alpha> TT))))\<close> someI_ex
      unfolding \<Psi>_def
      by auto
    hence "\<forall>i \<in> J. \<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> (\<Phi> i)) = (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)"
      unfolding \<Psi>_def 
      using "1" by auto 
    have "\<forall>i \<in> J. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)" 
      proof
      fix i
      assume "i \<in> J"
      then show "\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)" proof-
        have "\<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> (\<Phi> i)) = (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)"
        using \<open>\<forall>i\<in>J. \<Psi> i = hml_pos (SOME \<alpha>. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> hml_pos \<alpha> TT)) TT\<close> \<open>i \<in> J\<close> by blast
      then obtain \<alpha> where "\<Psi> i = (hml_pos \<alpha> TT)"
        by blast
      hence "\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> hml_pos \<alpha> TT)" 
        by (smt (verit, ccfv_threshold) \<open>\<Psi> i = hml_pos (SOME \<alpha>. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> hml_pos \<alpha> TT)) TT\<close> \<open>\<forall>y\<in>\<Phi> ` J. \<exists>\<alpha>. \<forall>s. (s \<Turnstile> y) = (s \<Turnstile> hml_pos \<alpha> TT)\<close> \<open>i \<in> J\<close> image_iff someI_ex)
      hence "\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)" 
        using \<open>\<Psi> i = hml_pos \<alpha> TT\<close> by presburger
      then show "\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)" by blast
    qed
  qed
    have "\<forall>i \<in> J. \<exists>\<alpha>. (\<Psi> i) = hml_pos \<alpha> TT"
      unfolding \<Psi>_def
      using "1" "3" \<open>\<forall>\<alpha>. Ready_traces.single_pos_pos (hml_pos \<alpha> TT)\<close> by fastforce
    hence "hml_ready_sim (hml_conj I J \<Psi>)" 
      using \<open>\<forall>j \<in> I. \<exists>\<psi>. hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<psi>))\<close> Ready_simulation.HML_ready_sim.intros(3) \<open>\<forall>i\<in>I. \<exists>\<psi>. \<Psi> i = \<psi> \<and> hml_ready_sim \<psi> \<and> (\<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<psi>))\<close> image_iff
      by (simp add: hml_ready_sim.intros(3))
    have "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Psi>)))"
      by (simp add: \<open>\<forall>i\<in>J. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<Psi> i)\<close> \<open>\<forall>j\<in>I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)\<close>)
    then show ?thesis 
      using "1" HML_ready_sim.intros(1) \<open>\<forall>j \<in> I. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> \<Psi> j)\<close> \<open>hml_ready_sim (hml_conj I J \<Psi>)\<close> by blast
  next
    case 2
    assume  "(\<exists>i. i \<in> I \<inter> J)"
    then obtain i where "i \<in> I \<inter> J" by blast
    hence "\<forall>s. \<not>((s \<Turnstile> (\<Phi> i)) \<and> (\<not>(s \<Turnstile> (\<Phi> i))))" 
      by blast
    hence "\<forall>s. \<not>((\<forall>i \<in> I. s \<Turnstile> (\<Phi> i)) \<and> (\<forall>j \<in> J. \<not>(s \<Turnstile> (\<Phi> j))))"
      using \<open>i \<in> I \<inter> J\<close> by blast
    hence "\<forall>s. \<not>s\<Turnstile>(hml_conj I J \<Phi>)" 
      using hml_sem_conj by presburger
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>j. (if j = i then TT::('a, 's)hml else undefined))"
    hence "hml_ready_sim (hml_conj {i} {i} \<Psi>)" 
      by (smt (verit) hml_ready_sim.simps image_empty image_insert singletonD)
    have "\<forall>s. \<not>s\<Turnstile>(hml_conj {i} {i} \<Psi>)" 
      by simp
    then show ?thesis 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> \<open>hml_ready_sim (hml_conj {i} {i} \<Psi>)\<close> by blast
  next
    assume "\<exists>j\<in>J. HML_true (\<Phi> j)"
    hence "\<forall>s. \<not>(s\<Turnstile>(hml_conj I J \<Phi>))" 
      using HML_true_def by force
    obtain j where "j\<in>J" "HML_true (\<Phi> j)" 
      using \<open>\<exists>j\<in>J. HML_true (\<Phi> j)\<close> by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = j then TT::('a, 's)hml else undefined))"
    have "hml_ready_sim (hml_conj {} {j} \<Psi>)" 
      by (simp add: \<Psi>_def hml_ready_sim.intros(3))
    have "\<forall>s. \<not>(s\<Turnstile>(hml_conj {} {j} \<Psi>))" 
      by (simp add: \<Psi>_def)
    then show ?thesis using \<open>hml_ready_sim (hml_conj {} {j} \<Psi>)\<close> 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> by blast
  qed
qed

end
end