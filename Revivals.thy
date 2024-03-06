theory Revivals
imports Transition_Systems HML formula_prices_list Failures Expr_helper
begin

subsection \<open>Readiness semantics\<close>

text \<open>\<close>
inductive hml_readiness :: "('a, 's)hml \<Rightarrow> bool"
  where
read_tt: "hml_readiness TT" |
read_pos: "hml_readiness (hml_pos \<alpha> \<phi>)" if "hml_readiness \<phi>" |
read_conj: "hml_readiness (hml_conj I J \<psi>s)" 
if "\<forall>i \<in> I. (\<exists>\<alpha>. ((\<psi>s i) = hml_pos \<alpha> TT))" "(\<forall>j \<in> J. (\<exists>\<alpha>. ((\<psi>s j) = hml_pos \<alpha> TT)) \<or> \<psi>s j = TT)" 

definition hml_readiness_formulas
  where
"hml_readiness_formulas \<equiv> {\<phi>. hml_readiness \<phi>}"

text \<open>\begin{figure}[htbp]
    \centering
\begin{tikzpicture}[auto,node distance=1.5cm]
  \coordinate (p1) at (-3,0);
  \node at (-3, 0.2) {$p_1$}; 
  \node[below left of=p1] (p2) {$p_2$};
  \node[below right of=p1] (p3) {$p_3$};
  \node[below of=p2] (p4) {$p_4$};
  \node[below of=p3] (p5) {$p_5$};
  
  \draw[->] (p1) -- node[above] {a} (p2);
  \draw[->] (p1) -- node[above] {a} (p3);
  \draw[->] (p2) -- node[left] {b} (p4);
  \draw[->] (p3) -- node[right] {c} (p5);

\coordinate (q1) at (3,0);
  \node at (3, 0.2) {$q_1$}; 
  \node[below left of=q1] (q2) {$q_2$};
  \node[below of=q1] (q3) {$q_3$};
  \node[below right of=q1] (q4) {$q_4$};
  \node[below of=q2] (q5) {$q_5$};
  \node[below of=q4] (q6) {$q_6$};
  
  \draw[->] (q1) -- node[left] {a} (q2);
  \draw[->] (q1) -- node[above] {a} (q3);
  \draw[->] (q1) -- node[right] {a} (q4);
  \draw[->] (q2) -- node[right] {b} (q5);
  \draw[->] (q3) -- node[right] {b} (q5);
  \draw[->] (q3) -- node[right] {c} (q6);
  \draw[->] (q4) -- node[right] {c} (q6);
\end{tikzpicture}
\caption{TEEEEEEEEEEEEEEEEEEST}
    \label{fig:your_label}
\end{figure}\<close>

definition expr_ready_trace
  where
"expr_ready_trace = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 1, 1, 1))}"

context lts
begin

definition expr_ready_trace_equivalent 
  where
"expr_ready_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_ready_trace \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"


text \<open>Proposition\<close>

inductive HML_revivals :: "('a, 's) hml \<Rightarrow> bool" 
  where
revivals_tt: "HML_revivals TT" |
revivals_pos: "HML_revivals (hml_pos \<alpha> \<phi>)" if "HML_revivals \<phi>" |
revivals_conj: "HML_revivals (hml_conj I J \<Phi>)" if "(\<exists>x \<in> (\<Phi> ` I). (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>) \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> TT_like y))
\<or> (\<forall>y \<in> (\<Phi> ` I).TT_like y)"
"(\<forall>x \<in> (\<Phi> ` J). TT_like x \<or> (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>))"
lemma revivals_right:
  assumes "HML_revivals \<phi>"
  shows "less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 0, 1, 1)"
  using assms
proof(induction \<phi> rule: HML_revivals.induct)
  case revivals_tt
  then show ?case by simp
next
  case (revivals_pos \<phi> \<alpha>)
  then show ?case by simp
next
  case (revivals_conj \<Phi> I J)
  hence neg: "\<forall>x\<in>\<Phi> ` J. less_eq_t (expr x) (1, 1, 0, 0, 0, 0)"
    using e1_tt e2_tt e3_tt e4_tt e5_tt e6_tt expr.simps expr_TT 
    by (metis le_numeral_extra(3) le_numeral_extra(4) less_eq_t.simps linordered_nonzero_semiring_class.zero_le_one)
  hence f2: "\<forall>x \<in> ((expr_1 \<circ> \<Phi>) ` J). x \<le> 1"
   "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` J). x \<le> 1"
   "\<forall>x \<in> ((expr_3 \<circ> \<Phi>) ` J). x \<le> 0"
   "\<forall>x \<in> ((expr_4 \<circ> \<Phi>) ` J). x \<le> 0"
   "\<forall>x \<in> ((expr_5 \<circ> \<Phi>) ` J). x \<le> 0"
   "\<forall>x \<in> ((expr_6 \<circ> \<Phi>) ` J). x \<le>  0"
    using expr.simps by simp+


  have "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
and "Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 1"
and "Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0" 
using Sup_le_iff f2
         apply (simp add: SUP_least)
    using Sup_le_iff f2
         apply (simp add: SUP_least)
    using Sup_le_iff f2
    by (metis)+
  from revivals_conj(1) show ?case proof
    assume "\<forall>y\<in>\<Phi> ` I. TT_like y"
    hence "\<forall>y\<in>\<Phi> ` I. less_eq_t (expr y) (0, 1, 0, 0, 0, 0)"
      using expr_TT by auto
  hence f1: "\<forall>x \<in> ((expr_1 \<circ> \<Phi>) ` I). x \<le> 0"
   "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<le> 1"
   "\<forall>x \<in> ((expr_3 \<circ> \<Phi>) ` I). x \<le> 0"
   "\<forall>x \<in> ((expr_4 \<circ> \<Phi>) ` I). x \<le> 0"
   "\<forall>x \<in> ((expr_5 \<circ> \<Phi>) ` I). x \<le> 0"
   "\<forall>x \<in> ((expr_6 \<circ> \<Phi>) ` I). x \<le>  0"
    using expr.simps by simp+
have "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1"
and "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
and "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
    using Sup_le_iff f1
         apply (simp add: SUP_least)
    using Sup_le_iff f1
         apply (simp add: SUP_least)
    using Sup_le_iff f1 SUP_bot_conv(2) bot_enat_def
    by (metis )+
  have e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_2_conj one_add_one
    by (metis Sup_union_distrib add_left_mono le_sup_iff)
  have e3: "expr_3 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0\<close> 
      one_add_one expr_3_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  from \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0\<close> have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) <= 0" 
    using SUP_image dual_order.trans mon_expr_1_pos_r by metis
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0" 
    using \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close>
      expr_4_conj Sup_union_distrib le_sup_iff
    by metis
  have e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1" 
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_5_conj 
    by (simp add: Sup_union_distrib)
  from \<open>Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0\<close> have "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def f2(6)
    by (metis eSuc_Sup image_comp image_is_empty nle_le one_eSuc zero_le) 
    hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_6_conj 
    by (simp add: Sup_union_distrib)
  then show ?thesis using e2 e3 e4 e5 e6 expr.simps less_eq_t.simps 
    by (metis enat_ord_code(3))
next
  assume "\<exists>x\<in>\<Phi> ` I. (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) \<and> (\<forall>y\<in>\<Phi> ` I. x \<noteq> y \<longrightarrow> TT_like y)"
  then obtain \<phi> where "\<phi> \<in> \<Phi> ` I" "(\<exists>\<alpha> \<chi>. \<phi> = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)" "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> TT_like y)"
    by blast
  hence expr_\<phi>: "expr_1 \<phi> = 1" "expr_2 \<phi> = 1" "expr_3 \<phi> = 0" "expr_4 \<phi> = 0" "expr_5 \<phi> = 0" "expr_6 \<phi> = 0"
    using e1_tt e2_tt e3_tt e4_tt e5_tt e6_tt expr.simps expr_TT 
    by metis+
  have "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_1 y = 0)"
"(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_2 y = 1)"
"(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_3 y = 0)"
"(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_4 y = 0)"
"(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_5 y = 0)"
"(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_6 y = 0)"
    using \<open>(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> TT_like y)\<close> expr_TT expr.simps 
    by fastforce+
  hence "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
    using expr_\<phi> 
    by (metis SUP_image SUP_least linorder_linear zero_less_one_class.zero_le_one)+
  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using expr_\<phi> \<open>(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> expr_1 y = 0)\<close> 
    by (metis \<open>\<phi> \<in> \<Phi> ` I\<close> image_iff le_zero_eq pos_r_bounded)
  have e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_2_conj one_add_one
    by (metis Sup_union_distrib add_left_mono le_sup_iff)
  have e3: "expr_3 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0\<close> 
      one_add_one expr_3_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  have e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0" 
    using \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0\<close>
      expr_4_conj Sup_union_distrib le_sup_iff
    by metis
  have e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1" 
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_5_conj 
    by (simp add: Sup_union_distrib)
  from \<open>Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0\<close> have "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def f2(6)
    by (metis eSuc_Sup image_comp image_is_empty nle_le one_eSuc zero_le) 
    hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_6_conj 
    by (simp add: Sup_union_distrib)
  then show ?thesis using e2 e3 e4 e5 e6 less_eq_t.simps expr.simps 
    by auto
  qed
qed

lemma pos_r_apply:
  assumes "\<forall>x \<in> (pos_r (\<Phi> ` I)). expr_1 x \<le> n" "\<forall>x \<in> \<Phi> ` I. expr_1 x \<le> m"
  shows "\<forall>x \<in> (\<Phi> ` I). expr_1 x \<le> n \<or> (\<exists>x \<in> \<Phi> ` I. expr_1 x \<le> m \<and> (\<forall>y \<in> \<Phi> ` I. y \<noteq> x \<longrightarrow> expr_1 y \<le> n))"
proof-
  from assms show ?thesis 
    by (metis (no_types, lifting) DiffI pos_r.simps singletonD)
qed

lemma e1_le_0_e2_le_1:
  assumes "expr_1 \<phi> \<le> 0" "expr_2 \<phi> \<le> 1"
  shows "TT_like \<phi>"
  using assms proof(induction \<phi>)
  case TT
  then show ?case 
    using TT_like.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  from this(2) have False by simp
  then show ?case by simp
next
  case (hml_conj I J \<Phi>)
  hence "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_2 x \<le> 0" 
    using expr_2_le_1 
    by (metis empty_iff empty_is_image sup_bot_right)
  hence "\<Phi> ` (I \<union> J) = {}" 
    using expr_2_le_1 hml_conj.prems(2) by blast
  then show ?case 
    by (simp add: TT_like.intros(2))
qed

lemma e1_le_1_e2_le_1:
  assumes "expr_1 \<phi> \<le> 1" "expr_2 \<phi> \<le> 1"
  shows "TT_like \<phi> \<or> (\<exists>\<alpha> \<psi>. \<phi> = (hml_pos \<alpha> \<psi>) \<and> TT_like \<psi>)"
  using assms proof(induction \<phi>)
  case TT
  then show ?case 
    using TT_like.intros(1) by blast
next
  case (hml_pos x1 \<phi>)
  hence "expr_1 \<phi> \<le> 0" "expr_2 \<phi> \<le> 1"
    by simp+
  hence "TT_like \<phi>" using e1_le_0_e2_le_1 
    by blast
  then show ?case 
    by blast
next
  case (hml_conj I J \<Phi>)
  hence "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_2 x \<le> 0" 
    using expr_2_le_1 
    by (metis empty_iff empty_is_image sup_bot_right)
  hence "\<Phi> ` (I \<union> J) = {}" 
    using expr_2_le_1 hml_conj.prems(2) by blast
  then show ?case 
    by (simp add: TT_like.intros(2))
qed

lemma revivals_pos:
  assumes "less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, 2, 1, 0, 1, 1)"
  shows "(\<exists>x \<in> (\<Phi> ` I). (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>) \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> TT_like y))
\<or> (\<forall>y \<in> (\<Phi> ` I).TT_like y)"
proof-
  have "expr_2 (hml_conj I J \<Phi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)"
    using expr_2_conj by blast
  also have "... \<le> 2" 
    using assms by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 1" 
    by (metis enat_add_left_cancel_le infinity_ne_i1 one_add_one)
  hence "\<forall>x \<in> \<Phi> ` I. expr_2 x \<le> 1" "\<forall>x \<in> \<Phi> ` J. expr_2 x \<le> 1"
    using Sup_le_iff 
    by (metis UnI1 UnI2 comp_apply image_iff image_eqI)+
  have "expr_3 (hml_conj I J \<Phi>) = (Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J))"
    using expr_3_conj by blast
  hence e3_le_1: "... \<le> 1" using assms by simp
  hence "\<forall>x \<in> \<Phi> ` I. expr_1 x \<le> 1" "\<forall>x \<in> \<Phi> ` I. expr_3 x \<le> 1" "\<forall>x \<in> \<Phi> ` J. expr_3 x \<le> 1"
    using Sup_le_iff comp_apply 
      apply (metis (no_types, opaque_lifting) SUP_image SUP_upper Sup_union_distrib dual_order.trans sup_ge1)
    using e3_le_1 Sup_le_iff comp_apply 
    by (metis UnCI image_iff)+
  have "expr_4 (hml_conj I J \<Phi>) = Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J)"
    using expr_4_conj by simp
  hence "... \<le> 0" using assms by simp
  hence "\<forall>x \<in> (pos_r (\<Phi> ` I)). expr_1 x \<le> 0" 
    by (meson Sup_le_iff UnCI Un_upper1 image_subset_iff)
  hence "(\<forall>x \<in> (\<Phi> ` I). expr_1 x \<le> 0) \<or> (\<exists>x \<in> \<Phi> ` I. expr_1 x \<le> 1 \<and> (\<forall>y \<in> \<Phi> ` I. y \<noteq> x \<longrightarrow> expr_1 y \<le> 0))"
    using pos_r_apply \<open>\<forall>x\<in>\<Phi> ` I. expr_1 x \<le> 1\<close> by blast
  then show ?thesis proof
    assume "\<forall>x\<in>\<Phi> ` I. expr_1 x \<le> 0"
    hence "\<forall>x\<in>\<Phi> ` I. TT_like x"
      using \<open>\<forall>x \<in> \<Phi> ` I. expr_2 x \<le> 1\<close> e1_le_0_e2_le_1 by blast
    then show ?thesis by blast
  next
    assume "\<exists>x\<in>\<Phi> ` I. expr_1 x \<le> 1 \<and> (\<forall>y\<in>\<Phi> ` I. y \<noteq> x \<longrightarrow> expr_1 y \<le> 0)"
    then obtain x where "x\<in>\<Phi> ` I" "expr_1 x \<le> 1" "(\<forall>y\<in>\<Phi> ` I. y \<noteq> x \<longrightarrow> expr_1 y \<le> 0)"
      by blast
    hence "(\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) \<or> TT_like x"
      using e1_le_1_e2_le_1 \<open>\<forall>x\<in>\<Phi> ` I. expr_2 x \<le> 1\<close> by blast
    have "(\<forall>y\<in>\<Phi> ` I. y \<noteq> x \<longrightarrow> TT_like y)"
      using \<open>(\<forall>y\<in>\<Phi> ` I. y \<noteq> x \<longrightarrow> expr_1 y \<le> 0)\<close> e1_le_0_e2_le_1 \<open>\<forall>x\<in>\<Phi> ` I. expr_2 x \<le> 1\<close> by blast
    then show ?thesis
      using \<open>(\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) \<or> TT_like x\<close> by metis
  qed
qed

lemma revivals_left:
  assumes "less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 0, 1, 1)"
  shows "HML_revivals \<phi>"
using assms proof(induction \<phi>)
  case TT
  then show ?case 
    using revivals_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    using HML_revivals.simps 
    by (metis mon_pos)
next
  case (hml_conj I J \<Phi>)
  have neg: "(\<forall>j \<in> J. (TT_like (\<Phi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Phi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
    using expr_2_expr_5_restrict_negations hml_conj(2) less_eq_t.simps expr.simps
    by metis
  have "(\<exists>x \<in> (\<Phi> ` I). (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>) \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> TT_like y))
          \<or> (\<forall>y \<in> (\<Phi> ` I).TT_like y)" 
    using hml_conj(2) revivals_pos by auto
  then show ?case using neg HML_revivals.simps revivals_conj
    by (smt (verit, ccfv_threshold) image_iff)
qed

end
end