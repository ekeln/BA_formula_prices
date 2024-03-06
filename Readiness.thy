theory Readiness
imports Transition_Systems HML formula_prices_list Failures
begin

subsection \<open>Readiness semantics\<close>

text \<open>Readiness semantics provides a finer distinguishing power than failures by not only considering the actions that a system refuses after a given sequence of actions, but explicitly modeling the actions the system can engage in.
(Figure ... ) highlights the difference, between $p_1$ and $q_1$, no matter which actions the observer refuses at whatever point in the execution, the other process has an execution path that is indistinguishable. The processes are failures and failure trace equivalent.
However, unlike $p_1$, $q_1$ can transition to a state $q_3$ where it is ready to perform actions a and b.\<close>

text \<open>\textbf{Definition} The language $\mathcal{O}_R$ of readiness-formulas is defined recursively:
$$\langle a \rangle \varphi \text{ if } \varphi \in \mathcal{O}_R \,|\, \bigwedge_{i\in I}\lnot\langle a \rangle \textsf{T}$$\<close>

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

inductive HML_readiness :: "('a, 's)hml \<Rightarrow> bool"
  where
read_tt: "HML_readiness TT" |
read_pos: "HML_readiness (hml_pos \<alpha> \<phi>)" if "HML_readiness \<phi>"|
read_conj: "HML_readiness (hml_conj I J \<Phi>)" 
if "(\<forall>x \<in> (\<Phi> ` (I \<union> J)). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"


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
  case (read_conj \<Phi> I J)
  from assms have "(\<forall>x \<in> (\<Phi> ` I) \<union> (\<Phi> ` J). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    using local.read_conj by blast
  hence "(\<forall>x \<in> (\<Phi> ` I) \<union> (\<Phi> ` J). less_eq_t (expr x) (1, 1, 0, 0, 0, 0))"
    using e1_tt e2_tt e3_tt e4_tt e5_tt e6_tt expr.simps expr_TT
    by (metis dual_order.refl i0_lb less_eq_t.simps)
  hence f1: "\<forall>x \<in> ((expr_1 \<circ> \<Phi>) ` I). x \<le> 1"
 "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<le> 1"
"\<forall>x \<in> ((expr_3 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_4 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_5 \<circ> \<Phi>) ` I). x \<le> 0"
 "\<forall>x \<in> ((expr_6 \<circ> \<Phi>) ` I). x \<le>  0"
and f2: "\<forall>x \<in> ((expr_1 \<circ> \<Phi>) ` J). x \<le> 1"
 "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` J). x \<le> 1"
"\<forall>x \<in> ((expr_3 \<circ> \<Phi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_4 \<circ> \<Phi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_5 \<circ> \<Phi>) ` J). x \<le> 0"
 "\<forall>x \<in> ((expr_6 \<circ> \<Phi>) ` J). x \<le> 0"
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

  have e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    using \<open>Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_2_conj one_add_one
    by (metis Sup_union_distrib add_left_mono le_sup_iff)
  have e3: "expr_3 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0\<close> 
one_add_one expr_3_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  from \<open>Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1\<close> have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) <= 1" 
    using SUP_image dual_order.trans mon_expr_1_pos_r 
    by metis 
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 1" 
    using \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close>
one_add_one expr_4_conj Sup_union_distrib add_left_mono le_sup_iff
    by (smt (verit) le_zero_eq max_def sup_enat_def)
  have e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1" 
    using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close> expr_5_conj 
    by (simp add: Sup_union_distrib)
  from \<open>Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0\<close> have "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def f2(6)
    by (metis eSuc_Sup image_comp image_is_empty nle_le one_eSuc zero_le) 
    hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0\<close> expr_6_conj 
    by (simp add: Sup_union_distrib)
  from e2 e3 e4 e5 e6 show ?case using less_eq_t.simps expr.simps 
    by (metis enat_ord_code(3))
qed

lemma expr_2_expr_3_restrict_positives:
  assumes "(expr_2 (hml_conj I J \<Phi>)) \<le> 2" "(expr_3 (hml_conj I J \<Phi>)) \<le> 1"
  shows "(\<forall>x \<in> (\<Phi> ` I). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
proof
  fix x
  assume "x \<in> \<Phi> ` I"
  hence "expr_2 x \<le> Sup (expr_2 ` \<Phi> ` I)"
    by (simp add: Sup_upper)
hence "expr_2 x \<le> Sup ((expr_2 \<circ> \<Phi>) ` I)"
  by (simp add: SUP_image)
  hence "expr_2 x \<le> Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)"
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
      hence "(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J)) \<ge> 2"
        using Sup_enat_def Sup_union_distrib
        by (metis sup.coboundedI1)
      hence "expr_3 (hml_conj I J \<Phi>) \<ge> 2"
        using expr_3_conj
        by force
      with assms(2) have False 
        by (meson numeral_le_one_iff order_trans semiring_norm(69))
      then show ?thesis by simp
    next
      case (hml_conj I' J' \<Phi>')
      hence "expr_2 (hml_conj I' J' \<Phi>') = expr_2 x"
        by (simp add: hml_pos)
      hence "expr_2 (hml_conj I' J' \<Phi>') \<le> 1"
        using \<open>expr_2 x \<le> 1\<close> 
        by presburger
      hence "(\<Phi>' ` I') = {}" 
        "(\<Phi>' ` J') = {}" 
        using expr_2_le_1 
        by blast+
      thus ?thesis using hml_conj TT_like.simps
        by fastforce
    qed    
    then show ?thesis
      using hml_pos by blast
  next
    case (hml_conj x31 x32 x33)
    with \<open>expr_2 x \<le> 1\<close> have "(x33 ` x31) = {}" "(x33 ` x32) = {}" 
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
  case (hml_conj I J \<Phi>)
  hence pos:"(\<forall>x \<in> (\<Phi> ` I). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    using expr.simps less_eq_t.simps expr_2_expr_3_restrict_positives
    by metis
  have neg: "(\<forall>j \<in> J. (TT_like (\<Phi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Phi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
    using hml_conj(2) expr_2_expr_5_restrict_negations expr.simps less_eq_t.simps
    by metis
  then show ?case using pos read_conj Un_iff image_iff 
    by (smt (verit))
qed

lemma readiness_lemma:
  shows "(HML_readiness \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))"
  using readiness_left readiness_right by blast

lemma alt_readiness_def_implies_readiness_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_readiness \<phi>"
  shows "\<exists>\<psi>. HML_readiness \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case read_tt
  then show ?case 
    using HML_readiness.read_tt by blast
next
  case (read_pos \<phi> \<alpha>)
  then show ?case 
    using HML_readiness.read_pos by fastforce
next
  case (read_conj I \<Phi> J)
  hence "HML_readiness (hml_conj I J \<Phi>)" 
    using HML_readiness.read_conj TT_like.simps 
    by (smt (verit, ccfv_threshold) UnE image_iff)
  then show ?case by blast
qed

lemma readiness_def_implies_alt_readiness_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_readiness \<phi>"
  shows "\<exists>\<psi>. hml_readiness \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case read_tt
  then show ?case 
    using hml_readiness.read_tt by blast
next
  case (read_pos \<phi> \<alpha>)
  then obtain \<psi> where "hml_readiness \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "hml_readiness (hml_pos \<alpha> \<psi>) \<and> (\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))"
    by (simp add: hml_readiness.read_pos)
  then show ?case by blast
next
  case (read_conj \<Phi> I J)
  then consider "\<Phi> ` I \<inter> \<Phi> ` J = {} \<and> (\<forall>x \<in> (\<Phi> ` J). (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    | "\<Phi> ` I \<inter> \<Phi> ` J \<noteq> {} \<or> (\<exists>x \<in>\<Phi>` J. (TT_like x))" 
    by blast
  then show ?case proof(cases)
    case 1
    hence "\<forall>j \<in> J. (\<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)" 
      by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if (\<exists>\<alpha> \<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)
                          then (hml_pos (SOME \<alpha>. \<exists>\<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) TT)::('a, 's)hml 
                          else undefined))"
    hence "\<forall>\<psi> \<in> \<Psi> ` J. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT"
      by (simp add: \<open>\<forall>j\<in>J. \<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>\<close>)
    define I' where "I' \<equiv> {i. i \<in> I \<and> ((\<exists>\<alpha> \<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))}"
    have "\<forall>\<psi> \<in> \<Psi> ` I'. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT"
      unfolding I'_def \<Psi>_def
      by force
    hence "\<forall>j \<in> (J \<union> I'). \<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi> \<and> \<Psi> j = hml_pos \<alpha> TT" 
      using \<Psi>_def \<open>\<forall>j \<in> J. (\<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)\<close> 
      unfolding \<Psi>_def I'_def
      by force
    hence "(\<forall>s. \<forall>j \<in> J \<union> I'. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))" 
      using HML_true_TT_like HML_true_def 
      by (metis hml_sem_pos hml_sem_tt)
    have "\<forall>x \<in> (I - I'). TT_like (\<Phi> x)"
      using read_conj 1
      unfolding I'_def
      by auto
    hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Phi>)))"
      using HML_true_TT_like read_conj 1
      unfolding I'_def HML_true_def 
      by (smt (verit, del_insts) Diff_iff hml_sem_conj mem_Collect_eq)
    hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Psi>)))"
      using \<open>(\<forall>s. \<forall>j \<in> J \<union> I'. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))\<close>
      by simp
    have "hml_readiness (hml_conj I' J \<Psi>)" 
      using \<Psi>_def I'_def
      using hml_readiness.simps Un_iff \<open>\<forall>\<psi>\<in>\<Psi> ` I'. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT\<close> \<open>\<forall>\<psi>\<in>\<Psi> ` J. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT\<close> image_Un
      using \<open>\<forall>j\<in>J. \<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>\<close> by fastforce
    then show ?thesis 
      using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Psi>))\<close> by blast
  next
    case 2
    hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
      using HML_true_TT_like HML_true_def by fastforce 
    obtain \<phi> i_\<phi> where "\<phi> \<in> \<Phi> ` I \<inter> \<Phi> ` J \<or> (\<phi> \<in> \<Phi> ` J \<and> TT_like \<phi>)" "\<Phi> i_\<phi> = \<phi>"
      using 2 by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
    have "hml_readiness (hml_conj {} {i_\<phi>} \<Psi>)" 
      by (simp add: \<Psi>_def hml_readiness.read_conj)
    have "\<forall>s. \<not>s \<Turnstile> (hml_conj {} {i_\<phi>} \<Psi>)" 
      by (simp add: \<Psi>_def)
    then show ?thesis 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> \<open>hml_readiness (hml_conj {} {i_\<phi>} \<Psi>)\<close> by blast
  qed
qed

lemma readiness_definitions_equivalent: 
  "\<forall>\<phi>. (HML_readiness \<phi> \<longrightarrow> (\<exists>\<psi>. hml_readiness \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  "\<forall>\<phi>. (hml_readiness \<phi> \<longrightarrow> (\<exists>\<psi>. HML_readiness \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  using readiness_def_implies_alt_readiness_def alt_readiness_def_implies_readiness_def by blast+


end
end