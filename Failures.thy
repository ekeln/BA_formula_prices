(*<*)
theory Failures
imports Transition_Systems HML formula_prices_list HML_list Traces
begin
(*>*)

section \<open>Failures semantics\<close>

text \<open>We can imagine the observer not only observing all traces of a system but also identifying scenarios where specific behavior is not possible. 
For Failures in particular, the observer can distinguish between step-sequences based on what actions are possible in the resulting state. 
Another way to think about Failures is that the process autonomously chooses an execution path, but only using a set of free allowed actions.
We want the failure formulas to represent either a trace (of the form $\langle a_1 \rangle\langle a_2\rangle\ldots\langle a_n \rangle\textsf{T}$)
or a failure pair, where some set of actions is not possible (of the form $\langle a_1 \rangle\langle a_2\rangle\ldots\langle a_n \rangle\bigwedge \langle a_i\rangle\textsf{T}$).
\<close>
subsubsection \<open>Definition 3.2.1\<close>
text \<open>\textit{The \textnormal{modal characterization of failures semantics} $\mathcal{O}_F$ is defined recursively:}
\begin{align*}
&\langle a \rangle \varphi \text{ if } \varphi \in \mathcal{O}_F\\
&\bigwedge_{i\in I}\lnot\langle a \rangle \textsf{T}
\end{align*}\<close>

inductive hml_failure :: "('a, 'i)hml \<Rightarrow> bool"
  where
failure_tt: "hml_failure TT" |
failure_pos: "hml_failure (hml_pos \<alpha> \<phi>)" if "hml_failure \<phi>" |
failure_conj: "hml_failure (hml_conj I J \<psi>s)" 
if "I = {}" "(\<forall>j \<in> J. (\<exists>\<alpha>. ((\<psi>s j) = hml_pos \<alpha> TT)) \<or> \<psi>s j = TT)" 

definition hml_failure_formulas
  where
"hml_failure_formulas \<equiv> {\<phi>. hml_failure \<phi>}"

text \<open>The processes $p_1$ and $q_1$ of Figure 2.1 are an example of two processes that are trace equivalent but not failures equivalent. The formula $\langle a \rangle\bigwedge{\lnot\langle b \rangle}$ distinguishes $p_1$ from $q_1$ and is in $\mathcal{O}_F$.\<close>

text \<open>The syntactic features of failures formulas or those of trace formulas, extended by a possible conjunction over negated actions at the end of the sequence of observations. 
This increases the bound for nesting depth of conjunctions, the depth of negations and the modal depth of negative clauses by one.
As a result, the price coordinate is $(\infty, 2, 0, 0, 1, 1)$.\<close>
text \<open>We define the sublanguage $\mathcal{O}_{e_F}$ as the set of formulas $\varphi$ with prices less than or equal to $(\infty, 2, 0, 0, 1, 1)$.\<close>
definition expr_failure
  where
"expr_failure = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))}"
       
context lts
begin

text \<open>We define the equivalences accordingly. Two processes $p$ $q$ are considered Failures equivalent $\sim_F$ iff there is no formula in $\mathcal{O}_F$ that distinguishes them.\<close>

definition hml_failure_equivalent
  where
"hml_failure_equivalent p q \<equiv> HML_subset_equivalent hml_failure_formulas p q"

text \<open>$p$ and $q$ are to be considered equivalent iff there is no formula in $\mathcal{L}_F$ that distinguishes them.\<close>
definition expr_failure_equivalent 
  where
"expr_failure_equivalent p q \<equiv> HML_subset_equivalent expr_failure p q"
end

subsubsection \<open>Proposition 3.2.2\<close>
text \<open>$p \sim_F q \longleftrightarrow p \sim_{e_F} q$. \\
The language of formulas with prices below $(\infty, 2, 0, 0, 1, 1)$ characterizes trace equivalence.

\textit{Proof.} We derivive the modal-logical definition of $\mathcal{O}_{e_F}$. Due to the characteristics of the \textsf{expr} function, 
this definition differs from $\mathcal{O}_F$. Then we show the actual equivalence by... .

According to the definition of \textsf{expr}, we have: \textsf{expr}$(\bigwedge_{i\in I} \psi_i)\in\mathcal{O}_{e_F} \leq (\infty, 2, 0, 0, 1, 1)$. This holds true if

1. For all $\psi_i$ where $i\in$ Pos:
   \begin{itemize}
     \item $\textsf{expr}_1(\psi_i) \leq 0$ 
     \item $\textsf{expr}_2(\psi_i) \leq 1$
   \end{itemize}
   
   This implies that the modal depth is 0 and the conjunction depth is also 0. Consequently, every $\psi_i$ has the form \textsf{T}.

2. For all $\psi_i$ where $i\in$ Neg:
   \begin{itemize}
     \item $\textsf{expr}_1(\psi_i) \leq 1$ 
     \item $\textsf{expr}_2(\psi_i) \leq 1$
   \end{itemize}
   
   This implies that the maximal modal depth is 1 and the conjunction depth is also 1. Consequently, every $\psi_i$ has the form \textsf{T} or $\langle a \rangle$\textsf{T}.
\<close>

(*<*)
text \<open>
\begin{equation*}
\begin{pmatrix}
\sup\left(\{\text{expr}_1(\psi_i) \,|\, i \in I\}\right) \\
1 + \sup\left(\{\text{expr}_2(\psi_i) \,|\, i \in I\}\right) \\
\sup\left(\{\text{expr}_3(\psi_i) \,|\, i \in I\} \cup \{\text{expr}_1(\psi_i) \,|\, i \in \text{Pos}\}\right) \\
\sup\left(\{\text{expr}_4(\psi_i) \,|\, i \in I\} \cup \{\text{expr}_1(\psi_i) \,|\, i \in \text{Pos}\setminus\mathcal{R}\}\right) \\
\sup\left(\{\text{expr}_5(\psi_i) \,|\, i \in I\} \cup \{\text{expr}_1(\psi_i) \,|\, i \in \text{Neg}\}\right) \\
\sup\left(\{1 + \text{expr}_6(\phi_i) \,|\, i \in I\} \cup \{\text{expr}_6(\psi_i) \,|\, i \in \text{Pos}\}\right)
\end{pmatrix}
\leq
\begin{pmatrix}
\infty\\
2\\
0\\
0\\
1\\
1
\end{pmatrix}
\end{equation*}
\<close>
(*>*)


inductive TT_like :: "('a, 'i) hml \<Rightarrow> bool"
  where
"TT_like TT" |
"TT_like (hml_conj I J \<Phi>)" if "(\<Phi> `I) = {}" "(\<Phi> ` J) = {}"

lemma expr_TT:
  assumes "TT_like \<chi>"
  shows "expr \<chi> = (0, 1, 0, 0, 0, 0)"
using assms
proof (induction \<chi>)
  case 1
  then show ?case by simp
next
  case (2 \<Phi> I J)
  then show ?case using expr.simps Sup_enat_def by force+
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

context lts begin
lemma HML_true_TT_like:
  assumes "TT_like \<phi>"
  shows "HML_true \<phi>"
  using assms
  unfolding HML_true_def
  apply (induction \<phi> rule: TT_like.induct)
  by simp+
end

inductive HML_failure :: "('a, 's)hml \<Rightarrow> bool"
  where
failure_tt: "HML_failure TT" |
failure_pos: "HML_failure (hml_pos \<alpha> \<phi>)" if "HML_failure \<phi>" |
failure_conj: "HML_failure (hml_conj I J \<psi>s)" 
if "(\<forall>i \<in> I. TT_like (\<psi>s i)) \<and> (\<forall>j \<in> J. (TT_like (\<psi>s j)) \<or> (\<exists>\<alpha> \<chi>. ((\<psi>s j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))" 

lemma mon_expr_1_pos_r: 
  "Sup (expr_1 ` (pos_r xs)) \<le> Sup (expr_1 ` xs)"
  by (simp add: Sup_subset_mono image_mono)

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
  case (failure_conj I \<Phi> J)
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

  from failure_conj have e1_neg: "\<forall>j \<in> J. expr_1 (\<Phi> j) \<le> 1"
and e2_neg: "\<forall>j \<in> J. expr_2 (\<Phi> j) = 1"
and e3_neg: "\<forall>j \<in> J. expr_3 (\<Phi> j) = 0"
and e4_neg: "\<forall>j \<in> J. expr_4 (\<Phi> j) = 0"
and e5_neg: "\<forall>j \<in> J. expr_5 (\<Phi> j) = 0"
and e6_neg: "\<forall>j \<in> J. expr_6 (\<Phi> j) = 0"
    using e1_tt e5_tt e2_tt e3_tt e4_tt e6_tt
    by fastforce+
  hence "(Sup ((expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) \<le> 1"
    using Sup_enat_def
    by (smt (verit, del_insts) Sup_le_iff Un_iff comp_apply image_iff nle_le not_one_le_zero)
  hence e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1"
    using expr_5_conj expr_\<psi>s e5_2 
    by (simp add: Sup_union_distrib)
  from e2_2 e2_neg failure_conj have "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 1"
    by (simp add: Sup_le_iff Sup_union_distrib)
  hence e2: "expr_2 (hml_conj I J \<Phi>) \<le> 2" 
    using expr_2_conj one_add_one
    by (metis add_left_mono)
  from e1_2 e3_2 have "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J) \<le> 0"
    by (metis (no_types, lifting) SUP_bot_conv(2) Sup_union_distrib bot_enat_def comp_apply e3_neg le_zero_eq sup.orderE)
  hence e3: "expr_3 (hml_conj I J \<Phi>) \<le> 0" 
    using expr_3_conj
    by auto
  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    by (metis SUP_image e1_2 le_zero_eq mon_expr_1_pos_r)
  hence "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) \<le> 0"
    using e4_2 failure_conj Sup_union_distrib bot_enat_def comp_apply e4_neg
    by (metis (no_types, lifting) SUP_bot_conv(2) le_zero_eq max_def sup_max) 
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0" 
    using expr_4_conj
    by auto
  from failure_conj e6_2 e6_neg have "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    by (metis (mono_tags, lifting) SUP_least comp_apply le_zero_eq)
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def comp_apply
    by (metis eSuc_Sup image_comp image_empty le_zero_eq nle_le one_eSuc) 
  with failure_conj e6_2 e6_tt have "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) \<le> 1"
    using one_eSuc e6_neg image_cong le_sup_iff bot.extremum_uniqueI bot_enat_def comp_apply
    by (simp add: Sup_union_distrib)
  hence e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using expr_6_conj
    by auto
  from e2 e3 e4 e5 e6 show ?case
    using less_eq_t.simps expr.simps 
    by fastforce
qed

lemma failure_pos_tt_like:
  assumes "less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, 2, 0, 0, 1, 1)"
shows "(\<forall>i \<in> I. TT_like (\<Phi> i))"
proof(rule ccontr)
  assume "\<not> (\<forall>i\<in>I. TT_like (\<Phi> i))"
  then obtain x where "x \<in> (\<Phi> ` I)" "\<not> TT_like x"
    using ex_in_conv 
    by fastforce 
  have "expr_2 x \<ge> 1"
    using expr_2_lb
    by blast
  from assms have "expr_2 (hml_conj I J \<Phi>) \<le> 2"
    by simp
  hence "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 2"
    using expr_2_conj
    by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 1"
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
    hence "expr_3 (hml_conj I J \<Phi>) \<ge> 1"
      using expr_3_conj \<open>x \<in> \<Phi> ` I\<close>
      by (smt (verit, del_insts) SUP_bot_conv(2) Sup_union_distrib bot_enat_def comp_apply 
iless_eSuc0 image_iff linorder_not_le one_eSuc sup_eq_bot_iff)
    with assms show False 
      using expr_3.simps
      by auto
  next
    case (hml_conj x31 x32 x33)
    with \<open>expr_2 x \<le> 1\<close> have "expr_2 (hml_conj x31 x32 x33) \<le> 1"
      by blast
    from hml_conj have "(\<not>(x33 ` x31) = {} \<or> \<not>(x33 ` x32) = {})"
      using TT_like.intros(2) \<open>\<not> TT_like x\<close> 
      by auto
    then show False
    proof
      assume "x33 ` x32 \<noteq> {}"
      then obtain y where "y \<in> (x33 ` x32)" 
        by blast
      from expr_2_lb have "expr_2 y \<ge> 1"
        by blast
      hence "expr_2 (hml_conj x31 x32 x33) \<ge> 2"
        using expr_2_conj \<open>y \<in> (x33 ` x32)\<close> 
        by (smt (verit) SUP_bot_conv(2) SUP_image Sup_union_distrib add_left_mono bot_enat_def 
iless_eSuc0 linorder_not_le one_add_one one_eSuc sup_eq_bot_iff)
      then show False using \<open>expr_2 (hml_conj x31 x32 x33) \<le> 1\<close>
        by simp
    next
      assume "x33 ` x31 \<noteq> {}"
then obtain y where "y \<in> (x33 ` x31)" 
        by blast
      from expr_2_lb have "expr_2 y \<ge> 1"
        by blast
      hence "expr_2 (hml_conj x31 x32 x33) \<ge> 2"
        using expr_2_conj \<open>y \<in> (x33 ` x31)\<close> 
        by (smt (verit) SUP_bot_conv(2) SUP_image Sup_union_distrib add_left_mono bot_enat_def 
iless_eSuc0 linorder_not_le one_add_one one_eSuc sup_eq_bot_iff)
      then show False using \<open>expr_2 (hml_conj x31 x32 x33) \<le> 1\<close>
        by simp
    qed
  qed
qed

lemma expr_2_le_1:  
  assumes "expr_2 (hml_conj I J \<Phi>) \<le> 1"
  shows "\<Phi> ` I = {}" "\<Phi> ` J = {}"
proof-
  from assms have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)  \<le> 1"
    using expr_2_conj
    by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 0"
    by fastforce
  hence "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J). x \<le> 0"
    using Sup_le_iff    
    by metis
  with expr_2_lb have "(expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J = {}"
    using all_not_in_conv comp_apply imageI image_empty not_one_le_zero
    by (metis Orderings.order_eq_iff UnI2 Un_empty_right all_not_in_conv zero_le)
  then show "\<Phi> ` I = {}" "\<Phi> ` J = {}"
    by fastforce+
qed

lemma expr_2_expr_5_restrict_negations: 
  assumes "expr_2 (hml_conj I J \<Phi>) \<le> 2" "expr_5 (hml_conj I J \<Phi>) \<le> 1"
  shows "(\<forall>j \<in> J. (TT_like (\<Phi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Phi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
proof
  fix j 
  assume "j \<in> J"
  then obtain \<psi> where "\<psi> = (\<Phi> j)"
    by blast
  hence "\<psi> \<in> (\<Phi> ` J)"
    using \<open>j \<in> J\<close> 
    by blast
  from assms(1) have "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 2"
    using expr_2_conj by simp
  hence "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 1"
    using one_add_one enat_add_left_cancel_le
    by (metis infinity_ne_i1)
  hence e2_\<psi>: "expr_2 \<psi> \<le> 1"
    by (simp add: Sup_le_iff \<open>\<psi> = \<Phi> j\<close> \<open>j \<in> J\<close>)
  show "TT_like (\<Phi> j) \<or> (\<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)"
  proof(cases \<psi>)
    case TT
    then show ?thesis
      by (simp add: TT_like.intros(1) \<open>\<psi> = \<Phi> j\<close>)
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
      hence "Sup ((expr_1 \<circ> \<Phi>) ` J) \<ge> 2"
        using \<open>\<psi> = \<Phi> j\<close> \<open>j \<in> J\<close> SUP_image
        by (metis Sup_upper2 imageI)
      hence "expr_5 (hml_conj I J \<Phi>) \<ge> 2"
        using expr_5_conj
        by (smt (verit, del_insts) Sup_union_distrib le_sup_iff nle_le)
      with assms(2) have False       
        by (meson numeral_le_one_iff order_trans semiring_norm(69))
      then show ?thesis by simp
    next
      case (hml_conj x31 x32 x33)
      hence "expr_2 \<chi> = expr_2 \<psi>"
        using hml_pos expr_2_pos
        by fastforce
      with e2_\<psi> hml_pos have "x33 ` x31 = {}" "x33 ` x32 = {}"
        using expr_2_le_1
        by (metis hml_conj)+
      then show ?thesis 
        using TT_like.simps hml_conj 
        by fastforce
    qed
    then show ?thesis
      using \<open>\<psi> = \<Phi> j\<close> hml_pos by blast
  next
    case (hml_conj x31 x32 x33)
    then show ?thesis using e2_\<psi> expr_2_le_1 TT_like.simps
      by (metis \<open>\<psi> = \<Phi> j\<close>)
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
  case (hml_conj I J \<Phi>)
  with failure_pos_tt_like have "\<forall>i \<in>I. TT_like (\<Phi> i)"
    by blast
  have "(\<forall>j \<in> J. (TT_like (\<Phi> j)) \<or> (\<exists>\<alpha> \<chi>. ((\<Phi> j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))"
    using expr_2_expr_5_restrict_negations hml_conj(2) less_eq_t.simps expr.simps
    by metis
  then show ?case using \<open>\<forall>i \<in>I. TT_like (\<Phi> i)\<close> failure_conj 
    by blast
qed

lemma failure_lemma:
  shows "(HML_failure \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 2, 0, 0, 1, 1))"
  using failure_left failure_right by blast

context lts begin 
lemma "hml_failure_equivalent p q \<longleftrightarrow> expr_failure_equivalent p q"  oops


text \<open>Failure Pairs\<close>

abbreviation failure_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a set) set\<close>
  where
\<open>failure_pairs p \<equiv> {(xs, F)|xs F. \<exists>p'. p \<mapsto>$ xs p' \<and> (initial_actions p' \<inter> F = {})}\<close>

text \<open>Failure preorder and -equivalence\<close>

definition failure_preordered (infix \<open>\<lesssim>F\<close> 60) where
\<open>p \<lesssim>F q \<equiv> failure_pairs p \<subseteq> failure_pairs q\<close>

abbreviation failure_equivalent (infix \<open>\<simeq>F\<close> 60) where
\<open> p \<simeq>F q \<equiv> p \<lesssim>F q \<and> q \<lesssim>F p\<close>
end
end