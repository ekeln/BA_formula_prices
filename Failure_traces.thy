theory Failure_traces
  imports Failures Transition_Systems HML formula_prices_list Expr_helper
begin

section \<open>Failure trace semantics\<close>
text \<open>In failure trace semantics, the observer not only identifies processes based on which actions are blocked in the final state of an execution 
but also analyzes the sets of actions that were not possible throughout the entire execution of the system. 
This allows the observer to not only distinguish processes based on blocked behavior at the end of an execution but also to impose limitations on the behavior of each process over time.
Example:...\<close>

subsubsection \<open>Definition 3.3.1\<close>
text \<open>\textit{The \textnormal{modal characterization of failure trace semantics} $\mathcal{O}_FT$ is defined recursively:}
\begin{align*}
&\langle a \rangle \varphi \text{ if } \varphi \in \mathcal{O}_F\\
&\bigwedge_{i\in I} \lnot\langle a \rangle \textsf{T}
\end{align*}
\<close>
inductive hml_failure_trace :: "('a, 's)hml \<Rightarrow> bool" where
"hml_failure_trace TT" |
"hml_failure_trace (hml_pos \<alpha> \<phi>)" if "hml_failure_trace \<phi>" |
"hml_failure_trace (hml_conj I J \<Phi>)" 
  if "(\<Phi> ` I) = {} \<or> (\<exists>i \<in> \<Phi> ` I. \<Phi> ` I = {i} \<and> hml_failure_trace i)"
     "\<forall>j \<in> \<Phi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT) \<or> j = TT" 

definition hml_failure_trace_formulas
  where
"hml_failure_trace_formulas \<equiv> {\<phi>. hml_failure_trace \<phi>}"

text \<open>
\begin{figure}[htbp]
    \centering
    \begin{tikzpicture}[auto,node distance=1.5cm]
        \coordinate (p1) at (-3,0);
        \node at (-3, 0.2) {$p_1$}; 
        \node[below left of=p1] (p2) {$p_2$};
        \node[below right of=p1] (p3) {$p_3$};
        \node[below left of=p2] (p4) {$p_4$};
        \node[below of=p2] (p5) {$p_5$};
        \node[below of=p3] (p6) {$p_6$};
        \node[below right of=p3] (p7) {$p_7$};
        \node[below of=p5] (p8) {$p_8$};
        \node[below of=p6] (p9) {$p_9$};
        
        \draw[->] (p1) -- node[above] {a} (p2);
        \draw[->] (p1) -- node[above] {a} (p3);
        \draw[->] (p2) -- node[left] {b} (p4);
        \draw[->] (p2) -- node[right] {c} (p5);
        \draw[->] (p3) -- node[left] {c} (p6);
        \draw[->] (p3) -- node[left] {f} (p7);
        \draw[->] (p5) -- node[left] {d} (p8);
        \draw[->] (p6) -- node[left] {e} (p9);
        
        \coordinate (q1) at (3,0);
        \node at (3, 0.2) {$q_1$}; 
        \node[below left of=q1] (q2) {$q_2$};
        \node[below right of=q1] (q3) {$q_3$};
        \node[below left of=q2] (q4) {$q_4$};
        \node[below of=q2] (q5) {$q_5$};
        \node[below of=q3] (q6) {$q_6$};
        \node[below right of=q3] (q7) {$q_7$};
        \node[below of=q5] (q8) {$q_8$};
        \node[below of=q6] (q9) {$q_9$};
        
        \draw[->] (q1) -- node[left] {a} (q2);
        \draw[->] (q1) -- node[above] {a} (q3);
        \draw[->] (q2) -- node[right] {b} (q4);
        \draw[->] (q2) -- node[right] {c} (q5);
        \draw[->] (q3) -- node[right] {c} (q6);
        \draw[->] (q3) -- node[right] {f} (q7);
        \draw[->] (q5) -- node[right] {e} (q8);
        \draw[->] (q6) -- node[right] {d} (q9);
    \end{tikzpicture}
    \caption{Graphs $p$ and $q$}
    \label{fig:graphs}
\end{figure}
\<close>

definition expr_failure_trace
  where
"expr_failure_trace = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))}"

context lts
begin

definition expr_failure_trace_equivalent 
  where
"expr_failure_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_failure_trace \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"
end

text \<open>\textbf{Proposition.} $p \sim_{\text{FT}} q \longleftrightarrow p \sim_{e_{\text{FT}}}$

\textit{Proof.} \\
We first establish the modal characterization of $\mathcal{O}_{e_{\text{FT}}}$.

Since \textsf{expr}$(\langle a \rangle) = (1, 0, 0, 0, 0, 0) + \textsf{expr}(\varphi)$, $\langle a \rangle \varphi$ belongs to $\mathcal{O}_{e_{\text{FT}}}$ if $\varphi$ is in $\mathcal{O}_{e_{\text{FT}}}$.

For $\bigwedge_{i\in I}\psi_i$, we investigate the syntactic constraints the price bound imposes onto each $\psi_i$.

Since $\textsf{expr}_1$ is unbounded, $\textsf{expr}_3$ and $\textsf{expr}_4$ together uniquely determine the modal depth of the positive conjuncts. 
One positive conjunct may contain arbitrary observations in its syntax tree. The modal depth of the others is bounded by 0, indicating that they consist solely of nested conjunctions.
The other dimensions of the positive conjunctions are limited by the same bounds $\bigwedge_{i\in I}\psi_i$ is limited by.

The nesting depth of negations $\textsf{expr}_6$ of $\bigwedge_{i\in I}\psi_i$ is bounded by one. Since the negative conjuncts $\psi_i$ take the form $\neg \varphi$, the corresponding $\varphi$'s must not have any negations.
Consequently, no conjunction within $\varphi$ can include any negative conjuncts. $\textsf{expr}_5$ bounds the modal depth of the negative conjuncts by 1. 

In summary, we have one positive conjunct $r$ with $\textsf{expr}(r) \leq (\infty, \infty, \infty, 0, 1, 1)$, while all other positive conjuncts $\psi_i$ are bounded by $\textsf{expr}(\psi_i) \leq (0, \infty, 0, 0, 0, 1)$. The negative conjuncts $\psi_j$ are bounded by $\textsf{expr}(\psi_i) \leq (1, \infty, 1, 0, 0, 0)$.

These bounds give rise to subsets themselves, and we derive their modal characterization in a similar manner.

The recursive definition of the modal characterization is given by:\\
$\mathcal{O}_{FT_{x_1}}$:\\
\begin{align*}
&\bigwedge_{i\in I} \varphi_i\text{ with }\varphi_i\in\mathcal{O}_{FT_x}
\end{align*}
$\mathcal{O}_{FT_{x_2}}$:\\
\begin{align*}
&\bigwedge_{i\in I} \psi_i\\
&\psi_i \coloneqq \varphi \text{ with }\varphi\in\mathcal{O}_{FT_{x_2}}\,|\,\lnot\varphi\text{ with }\varphi\in\mathcal{O}_{FT_{x_1}}
\end{align*}

\begin{align*}
& \text{For any } \alpha, \varphi: \quad \text{if } \mathcal{O}_{e_{\text{FT}}}(\varphi) \text{ then } \mathcal{O}_{e_{\text{FT}}}(\text{hml\_pos } \alpha \varphi) \\
& \text{For any } I, J, \Phi: \\
& \quad \text{if } \left( \exists \psi \in (\Phi \circ I). \left( \mathcal{O}_{e_{\text{FT}}}(\psi) \land \forall y \in (\Phi \circ I). \psi \neq y \Rightarrow \text{ nested\_empty\_conj } y \right) \right. \\
& \quad \quad \quad \quad \quad \quad \quad \quad \quad \left. \lor \left( \forall y \in (\Phi \circ I). \text{ nested\_empty\_conj } y \right) \right) \\
& \quad \quad \land \left( \forall y \in (\Phi \circ J). \text{ stacked\_pos\_conj\_pos } y \right) \\
& \quad \text{then } \mathcal{O}_{e_{\text{FT}}}(\text{hml\_conj } I J \Phi)
\end{align*}\<close>



inductive nested_empty_pos_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where
"nested_empty_pos_conj TT" |
"nested_empty_pos_conj (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> `I). nested_empty_pos_conj x" "(\<Phi> ` J) = {}"

inductive nested_empty_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where
"nested_empty_conj TT" |
"nested_empty_conj (hml_conj I J \<Phi>)"
if "\<forall>x \<in> (\<Phi> `I). nested_empty_conj x" "\<forall>x \<in> (\<Phi> `J). nested_empty_pos_conj x"

inductive stacked_pos_conj_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"stacked_pos_conj_pos TT" |
"stacked_pos_conj_pos (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"stacked_pos_conj_pos (hml_conj I J \<Phi>)"
if "((\<exists>\<phi> \<in> (\<Phi> ` I). ((stacked_pos_conj_pos \<phi>) \<and> 
                     (\<forall>\<psi> \<in> (\<Phi> ` I). \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>))) \<or>
   (\<forall>\<psi> \<in> (\<Phi> ` I). nested_empty_pos_conj \<psi>))"
"(\<Phi> ` J) = {}"

inductive HML_failure_trace :: "('a, 's)hml \<Rightarrow> bool"
  where
f_trace_tt: "HML_failure_trace TT" |
f_trace_pos: "HML_failure_trace (hml_pos \<alpha> \<phi>)" if "HML_failure_trace \<phi>"|
f_trace_conj: "HML_failure_trace (hml_conj I J \<Phi>)"
if "((\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_conj y)) \<and>
(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_pos y)"

lemma expr_nested_empty_pos_conj:
  assumes "nested_empty_pos_conj \<phi>"
  shows "less_eq_t (expr \<phi>) (0, \<infinity>, 0, 0, 0, 0)"
  using assms
proof(induction \<phi> rule: nested_empty_pos_conj.induct)
  case 1
  then show ?case 
    using expr.simps less_eq_t.simps
    by auto
next
  case (2 \<Phi> I J)
  have pos: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
 "Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
    using 2(1) less_eq_t.simps expr.simps Sup_enat_def
    by (metis SUP_image SUP_least)+
  from this(1) have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using mon_expr_1_pos_r ile0_eq
    by (metis SUP_image)
  hence "expr_1 (hml_conj I J \<Phi>) \<le> 0"
and"expr_3 (hml_conj I J \<Phi>) \<le> 0"
and "expr_4 (hml_conj I J \<Phi>) \<le> 0"
and "expr_6 (hml_conj I J \<Phi>) \<le> 0"
and "expr_5 (hml_conj I J \<Phi>) \<le> 0"
    using 2 expr_4_conj prefer 3 apply (simp add: Sup_union_distrib)
    using 2 expr_6_conj expr_5_conj pos expr_4_conj
    by simp+
  thus "less_eq_t (expr (hml_conj I J \<Phi>)) (0, \<infinity>, 0, 0, 0, 0)"
    by (metis enat_ord_code(3) expr.simps less_eq_t.simps)
qed

context lts begin
lemma HML_true_nested_empty_pos_conj:
  assumes "nested_empty_pos_conj \<phi>"
  shows "HML_true \<phi>"
  using assms
  unfolding HML_true_def
  apply (induction \<phi> rule: nested_empty_pos_conj.induct)
  by (simp, force)
end

lemma expr_nested_empty_conj:
  assumes "nested_empty_conj \<phi>"
  shows "less_eq_t (expr \<phi>) (0, \<infinity>, 0, 0, 0, 1)"
  using assms
proof(induction rule: nested_empty_conj.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 \<Phi> I J)
  hence fa_\<psi>: "\<forall>x\<in>\<Phi> ` J. 
        expr_1 x \<le> 0 \<and> expr_2 x \<le> \<infinity> \<and> expr_3 x \<le> 0 \<and> expr_4 x \<le> 0 \<and> expr_5 x \<le> 0 \<and> expr_6 x \<le> 0"
    using expr_nested_empty_pos_conj less_eq_t.simps expr.simps 
    by auto
  have sup_\<psi>: "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> \<infinity>"
"Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using fa_\<psi> 
    by (metis SUP_image SUP_least)+
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    using eSuc_def 
    by (smt (verit, best) SUP_le_iff comp_apply dual_order.eq_iff le_zero_eq one_eSuc)
  from 2 have fa_\<psi>: "\<forall>x\<in>\<Phi> ` I. expr_1 x \<le> 0 \<and> expr_2 x \<le> \<infinity> \<and> expr_3 x \<le> 0 \<and>
              expr_4 x \<le> 0 \<and> expr_5 x \<le> 0 \<and> expr_6 x \<le> 1"
    using less_eq_t.simps expr.simps
    by force
  have sup_\<phi>: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> \<infinity>"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
    using fa_\<psi>
    by (metis SUP_image SUP_least)+
  hence "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    using mon_expr_1_pos_r
    by (metis image_comp le_zero_eq mon_expr_1_pos_r)
  then show ?case using sup_\<psi> sup_\<phi> Sup_union_distrib
expr_1_conj expr_2_conj expr_3_conj expr_4_conj expr_5_conj formula_prices_list.expr_6_conj
less_eq_t.simps expr.simps \<open>Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1\<close> enat_ord_code(3) sup.bounded_iff
    by (smt (z3))
qed

lemma expr_stacked_pos_conj_pos:
  assumes "stacked_pos_conj_pos \<phi>"
  shows "less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0)"
  using assms
proof(induction \<phi> rule: stacked_pos_conj_pos.induct)
  case 1
  then show ?case 
    by simp
next
  case (2 \<psi> uu)
  then show ?case 
    using expr_nested_empty_pos_conj by fastforce
next
  case (3 \<Phi> I J)
  from 3 have fa_\<psi>: "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 0"
 "Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> 0"
 "Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 0"
 "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
 "Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0"
 "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using "3.hyps" Sup_enat_def by force+
  have case_pos: "(\<exists>\<phi>\<in>\<Phi> ` I.
           (stacked_pos_conj_pos \<phi> \<and> less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0)) \<and>
           (\<forall>\<psi> \<in> \<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>)) \<longrightarrow> 
less_eq_t (expr (hml_conj I J \<Phi>)) (1, \<infinity>, 1, 0, 0, 0)"
  proof
  assume "(\<exists>\<phi>\<in>\<Phi> ` I.
           (stacked_pos_conj_pos \<phi> \<and> less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0)) \<and>
           (\<forall>\<psi> \<in> \<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>))"
  with 3 obtain \<phi> where "\<phi> \<in> \<Phi> ` I" 
"(stacked_pos_conj_pos \<phi> \<and> less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0))"
    "(\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>)"
    by blast
  have expr_\<phi>: "expr_1 \<phi> \<le> 1"
"expr_2 \<phi> \<le> \<infinity>"
"expr_3 \<phi> \<le> 1"
"expr_4 \<phi> \<le> 0"
"expr_5 \<phi> \<le> 0"
"expr_6 \<phi> \<le> 0"
    using expr_nested_empty_pos_conj
    using \<open>stacked_pos_conj_pos \<phi> \<and> less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0)\<close> one_eSuc by fastforce+
  have expr_\<psi>: "(\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> 
expr_1 \<psi> \<le> 0 \<and> expr_1 \<psi> \<le> \<infinity> \<and> expr_3 \<psi> \<le> 0 \<and> expr_4 \<psi> \<le> 0 \<and> expr_5 \<psi> \<le> 0 \<and> expr_6 \<psi> \<le> 0)"
    using expr_nested_empty_pos_conj
    using \<open>\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>\<close> by auto
  hence fa_\<psi>: "\<forall>\<psi>\<in> (\<Phi> ` I) - {\<phi>}.
expr_1 \<psi> \<le> 0 \<and> expr_1 \<psi> \<le> \<infinity> \<and> expr_3 \<psi> \<le> 0 \<and> expr_4 \<psi> \<le> 0 \<and> expr_5 \<psi> \<le> 0 \<and> expr_6 \<psi> \<le> 0"
    by blast

  have expr_1_pos_r: "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
  proof(cases "expr_1 \<phi> \<ge> 1")
    case True
    hence "pos_r (\<Phi> ` I) = (\<Phi> ` I) - {\<phi>}"
  proof-
    have "\<forall>x\<in> (\<Phi> ` I) - {\<phi>}. expr_1 x < expr_1 \<phi>"
      using expr_\<psi> expr_\<phi> \<open>\<phi> \<in> \<Phi> ` I\<close> fa_\<psi>
      using \<open>stacked_pos_conj_pos \<phi> \<and> less_eq_t (expr \<phi>) (1, \<infinity>, 1, 0, 0, 0)\<close> iless_eSuc0
      by (metis True dual_order.strict_trans1 le_zero_eq one_eSuc)
    then show ?thesis 
      using pos_r_del_max \<open>\<phi> \<in> \<Phi> ` I\<close>
      by (metis (no_types, opaque_lifting) Un_insert_right insert_Diff_single insert_absorb sup_bot_right)
  qed
  then show ?thesis
    using expr_\<psi> 
    by (metis Diff_iff SUP_least singletonI)
  next
    case False
    hence "\<forall>\<psi> \<in>(\<Phi> ` I). expr_1 \<psi> \<le> 0"
      using fa_\<psi> 
      using iless_eSuc0 one_eSuc by fastforce
    then show ?thesis 
      by (meson SUP_least mon_expr_1_pos_r order.trans)
  qed

  have fa_\<phi>: "\<forall>\<phi> \<in> \<Phi> ` I. 
expr_1 \<phi> \<le> 1 \<and> expr_2 \<phi> \<le> \<infinity> \<and> expr_3 \<phi> \<le> 1 \<and> expr_4 \<phi> \<le> 0 \<and> expr_5 \<phi> \<le> 0 \<and> expr_6 \<phi> \<le> 0"
    using expr_\<phi> expr_\<psi>
    by auto
  hence sup_\<phi>: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> \<infinity>"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 1"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
         apply (simp add: Sup_le_iff)
    using Sup_le_iff
    using enat_ord_code(3) apply presburger
         apply (simp add: Sup_le_iff)
    apply auto
    by (metis (mono_tags, lifting) SUP_bot_conv(2) bot_enat_def fa_\<phi> image_eqI le_zero_eq)+

  hence "expr_1 (hml_conj I J \<Phi>) \<le> 1"
"expr_2 (hml_conj I J \<Phi>) \<le> \<infinity>"
"expr_3 (hml_conj I J \<Phi>) \<le> 1"
"expr_4 (hml_conj I J \<Phi>) \<le> 0"
"expr_5 (hml_conj I J \<Phi>) \<le> 0"
"expr_6 (hml_conj I J \<Phi>) \<le> 0"

      prefer 3
  using expr_3_conj fa_\<psi> "3.hyps" SUP_least sup_\<phi> SUP_image Sup_union_distrib bot.extremum_uniqueI
bot_enat_def le_sup_iff zero_less_one_class.zero_le_one
  apply (smt (verit, del_insts) image_is_empty sup_bot_right)
    prefer 3
using expr_4_conj fa_\<psi> "3.hyps" SUP_least sup_\<phi> SUP_image Sup_union_distrib bot.extremum_uniqueI
bot_enat_def le_sup_iff zero_less_one_class.zero_le_one expr_1_pos_r

  apply (smt (verit, del_insts) image_is_empty sup_bot_right)

  using expr_1_conj fa_\<psi> "3.hyps" SUP_image Sup_union_distrib bot.extremum_uniqueI
expr_2_conj sup_\<phi> expr_1_pos_r expr_4_conj
  by force+

  then show "less_eq_t (expr (hml_conj I J \<Phi>)) (1, \<infinity>, 1, 0, 0, 0)"
    using expr.simps less_eq_t.simps
    by metis
qed

  have case_nested: "(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi>) \<longrightarrow> 
  less_eq_t (expr (hml_conj I J \<Phi>)) (1, \<infinity>, 1, 0, 0, 0)"
  proof
    assume "(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi>)"
    hence sup_\<phi>: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_2 \<circ> \<Phi>) ` I) \<le> \<infinity>"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 0"
      using expr_nested_empty_pos_conj
      using fa_\<psi>(1) 
      by (metis SUP_image SUP_least expr.simps less_eq_t.simps)+

      have "expr_1 (hml_conj I J \<Phi>) \<le> 0"
"expr_2 (hml_conj I J \<Phi>) \<le> \<infinity>"
"expr_3 (hml_conj I J \<Phi>) \<le> 0"
"expr_4 (hml_conj I J \<Phi>) \<le> 0"
"expr_5 (hml_conj I J \<Phi>) \<le> 0"
"expr_6 (hml_conj I J \<Phi>) \<le> 0"
        prefer 2
        using enat_ord_code(3) apply blast
        using fa_\<psi> sup_\<phi> Sup_union_distrib
        apply (smt (verit) complete_linorder_sup_max expr_1_conj max_def)
        using fa_\<psi> sup_\<phi> Sup_union_distrib
           apply (smt (verit) expr_3_conj max_def sup_max)
        using fa_\<psi> sup_\<phi> Sup_union_distrib expr_4_conj mon_expr_1_pos_r
          apply (metis (no_types, lifting) SUP_image le_zero_eq sup.absorb2)
        using fa_\<psi> sup_\<phi> Sup_union_distrib
         apply (smt (verit) expr_5_conj max_def sup_max)
        using fa_\<psi> sup_\<phi> Sup_union_distrib expr_6.expr_6_conj 
        using "3.hyps" by force

        then show "less_eq_t (expr (hml_conj I J \<Phi>)) (1, \<infinity>, 1, 0, 0, 0)"
          using "3.hyps" 
          by force
      qed
      with case_pos show ?case
        using "3.hyps" 
        using "3.IH" by fastforce
    qed

lemma failure_trace_right:
  assumes "(HML_failure_trace \<phi>)"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  using assms
proof(induction \<phi>)
  case f_trace_tt
  then show ?case by simp
next
  case (f_trace_pos \<phi> \<alpha>)
  then show ?case 
    by simp
next
  case (f_trace_conj \<Phi> I J)

have fa_neg: "\<forall>y\<in>\<Phi> ` J. expr_1 y \<le> 1" 
 "\<forall>y\<in>\<Phi> ` J. expr_2 y \<le> \<infinity>" 
 "\<forall>y\<in>\<Phi> ` J. expr_3 y \<le> 1" 
 "\<forall>y\<in>\<Phi> ` J. expr_4 y \<le> 0" 
 "\<forall>y\<in>\<Phi> ` J. expr_5 y \<le> 0" 
 "\<forall>y\<in>\<Phi> ` J. expr_6 y \<le> 0" 
  using expr_stacked_pos_conj_pos expr.simps f_trace_conj
    by fastforce+
  have "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1"
and "Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> \<infinity>"
and "Sup ((expr_3 \<circ> \<Phi>) ` J) \<le> 1"
and "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0"
and "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> 0"
    using fa_neg
    by (metis SUP_image SUP_least)+
  hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1"
    by (metis SUP_image dual_order.eq_iff eSuc_Sup i0_lb image_empty one_eSuc)

  have case_ft: "(\<exists>\<psi>\<in>\<Phi> ` I.
         (HML_failure_trace \<psi> \<and> less_eq_t (expr \<psi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and>
         (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y))
\<longrightarrow> less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  proof
    assume case_ft: "(\<exists>\<psi>\<in>\<Phi> ` I.
       (HML_failure_trace \<psi> \<and> less_eq_t (expr \<psi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)) \<and>
       (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y))"
    then obtain \<psi> where "\<psi> \<in> \<Phi> ` I" and
\<psi>_ft: "(HML_failure_trace \<psi> \<and> less_eq_t (expr \<psi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
"(\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
      by blast
    hence "expr_4 \<psi> \<le> 0" "expr_5 \<psi> \<le> 1" "expr_6 \<psi> \<le> 1"
      by simp+
    have fa_y: "(\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> less_eq_t (expr y) (0, \<infinity>, 0, 0, 0, 1))"
      using expr_nested_empty_conj
      using \<psi>_ft(2) by blast
    hence "(\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> expr_1 y \<le> 0)"
      by simp 
    hence expr_1_y :"(\<forall>y\<in>(\<Phi> ` I) - {\<psi>}. expr_1 y \<le> 0)"
      by auto
    have sup_wo_\<psi>: "Sup (expr_1 ` ((\<Phi> ` I) - {\<psi>})) \<le> 0"
"Sup (expr_2 ` ((\<Phi> ` I) - {\<psi>})) \<le> \<infinity>"
"Sup (expr_3 ` ((\<Phi> ` I) - {\<psi>})) \<le> 0"
"Sup (expr_4 ` ((\<Phi> ` I) - {\<psi>})) \<le> 0"
"Sup (expr_5 ` ((\<Phi> ` I) - {\<psi>})) \<le> 0"
"Sup (expr_6 ` ((\<Phi> ` I) - {\<psi>})) \<le> 1"
using fa_y
  by (metis Diff_iff SUP_least expr.simps insertCI less_eq_t.simps)+

  hence "Sup (expr_5 ` (\<Phi> ` I)) \<le> 1"
"Sup (expr_6 ` (\<Phi> ` I)) \<le> 1"
    using sup_wo_\<psi>(5) \<open>\<psi> \<in> \<Phi> ` I\<close> \<open>expr_5 \<psi> \<le> 1\<close>
     apply (metis Sup_insert bot.extremum_uniqueI iless_eSuc0 image_insert insert_Diff 
linorder_le_cases linorder_not_le sup_bot.right_neutral)
    using \<open>expr_6 \<psi> \<le> 1\<close> sup_wo_\<psi>(6)  \<open>\<psi> \<in> \<Phi> ` I\<close>
    by (metis (no_types, lifting) SUP_least Sup_le_iff image_eqI insert_Diff insert_iff)


  have "Sup (expr_1 ` (pos_r (\<Phi> ` I))) \<le> 0"
    proof(cases "expr_1 \<psi> \<ge> 1")
      case True
      have "pos_r (\<Phi> ` I) = (\<Phi> ` I) - {\<psi>}"
      proof-
        have "\<forall>x\<in> (\<Phi> ` I) - {\<psi>}. expr_1 x < expr_1 \<psi>"
          using expr_1_y iless_eSuc0 True
          by (metis dual_order.strict_trans1 le_zero_eq less_numeral_extra(1))
        then show ?thesis 
          using pos_r_del_max \<open>\<psi> \<in> \<Phi> ` I\<close>
          by (metis (no_types, opaque_lifting) Un_insert_right insert_Diff_single insert_absorb sup_bot_right)
      qed
      then show ?thesis using sup_wo_\<psi>(1) 
        by presburger
    next
      case False
      then have "expr_1 \<psi> \<le> 0"
        using iless_eSuc0 one_eSuc by fastforce
      then show ?thesis using sup_wo_\<psi>  \<open>\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> expr_1 y \<le> 0\<close>
        by (metis (no_types, lifting) DiffD1 SUP_least pos_r.simps)
    qed
    have "Sup (expr_4 ` (\<Phi> ` I)) \<le> 0"
      using  \<open>\<psi> \<in> \<Phi> ` I\<close> \<open>expr_4 \<psi> \<le> 0\<close>
      by (metis Sup_insert ile0_eq image_insert insert_Diff sup.orderE sup_wo_\<psi>(4))
    hence "expr_4 (hml_conj I J \<Phi>) \<le> 0"
      using \<open>Sup (expr_1 ` pos_r (\<Phi> ` I)) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close>
      by (simp add: SUP_image Sup_union_distrib)
    have "expr_5 (hml_conj I J \<Phi>) \<le> 1"
      using \<open>Sup (expr_5 ` (\<Phi> ` I)) \<le> 1\<close> \<open>Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close>
      by (simp add: SUP_image Sup_union_distrib)
    have "expr_6 (hml_conj I J \<Phi>) \<le> 1"
      using \<open>Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1\<close> \<open>Sup (expr_6 ` (\<Phi> ` I)) \<le> 1\<close>
      by (simp add: SUP_image Sup_union_distrib)
    then show ?case using \<open>expr_5 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_4 (hml_conj I J \<Phi>) \<le> 0\<close>
      by simp
  qed

  have case_empty: " (\<forall>y\<in>\<Phi> ` I. nested_empty_conj y) \<longrightarrow> less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1)"
  proof
    assume "\<forall>y\<in>\<Phi> ` I. nested_empty_conj y"
    hence fa_y: "\<forall>y\<in>\<Phi> ` I. expr_1 y \<le> 0"
"\<forall>y\<in>\<Phi> ` I. expr_3 y \<le> 0"
"\<forall>y\<in>\<Phi> ` I. expr_4 y \<le> 0"
"\<forall>y\<in>\<Phi> ` I. expr_5 y \<le> 0"
"\<forall>y\<in>\<Phi> ` I. expr_6 y \<le> 1"
      using expr_nested_empty_conj less_eq_t.simps expr.simps
      by force+

    hence "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_3 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0"
"Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1"
      prefer 5
      using expr_nested_empty_pos_conj
      apply (simp add: SUP_least)
      using fa_y
      by (metis SUP_image SUP_least)+

    hence "Sup (expr_1 ` pos_r (\<Phi> ` I)) \<le> 0"
      by (metis SUP_image le_zero_eq mon_expr_1_pos_r)

    hence "expr_4 (hml_conj I J \<Phi>) \<le> 0"
      using \<open>Sup (expr_1 ` pos_r (\<Phi> ` I)) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> 0\<close>
      by (simp add: SUP_image Sup_union_distrib)
    have "expr_5 (hml_conj I J \<Phi>) \<le> 1"
      using \<open>Sup ((expr_5 \<circ> \<Phi>) ` I) \<le> 0\<close> \<open>Sup ((expr_5 \<circ> \<Phi>) ` J) \<le> 0\<close> \<open>Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> 1\<close>
      by (simp add: SUP_image Sup_union_distrib)
    have "expr_6 (hml_conj I J \<Phi>) \<le> 1"
      using \<open>Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> 1\<close> \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> 1\<close>
      by (simp add: SUP_image Sup_union_distrib)
    then show ?case using \<open>expr_5 (hml_conj I J \<Phi>) \<le> 1\<close> \<open>expr_4 (hml_conj I J \<Phi>) \<le> 0\<close>
      by simp
  qed
  then show ?case using case_ft f_trace_conj
    by linarith
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

lemma failure_trace_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))"
  shows "(HML_failure_trace \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using f_trace_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case
    using f_trace_pos by fastforce
next
  case (hml_conj I J \<Phi>)
  hence e4: "expr_4 (hml_conj I J \<Phi>) \<le> 0"
and e5: "expr_5 (hml_conj I J \<Phi>) \<le> 1"
and e6: "expr_6 (hml_conj I J \<Phi>) \<le> 1"
    using expr.simps less_eq_t.simps
    by metis+
  hence "\<forall>y\<in>\<Phi> ` J. stacked_pos_conj_pos y"
    using expr_5_restrict_negations
    by blast
  from hml_conj have "\<forall>x2a \<in> (\<Phi> ` I). HML_failure_trace x2a"
    using mon_conj(1) 
    by (metis (mono_tags, lifting) image_iff rangeI)
  then have "(\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_conj y)"
    using expr_4_expr_6_ft_to_recursive_ft e4 e5 e6
        by metis
  then show ?case using \<open>\<forall>y\<in>\<Phi> ` J. stacked_pos_conj_pos y\<close>
    by (simp add: f_trace_conj)
qed

lemma ft_lemma: 
  shows "(HML_failure_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))" 
  using failure_trace_left failure_trace_right by blast

text \<open>BlaBla... Dann Induktion über die Formeln und für jede formel äquivalente formel erstellen.\<close>

context lts begin
lemma \<^marker>\<open>tag (proof) visible\<close> alt_failure_trace_def_implies_failure_trace_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_failure_trace \<phi>"
  shows "\<exists>\<psi>. HML_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case 1
  then show ?case
    using f_trace_tt by blast
next
  case (2 \<phi> \<alpha>)
  then obtain \<psi> where "HML_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "HML_failure_trace (hml_pos \<alpha> \<psi>)" 
    by (simp add: f_trace_pos)
  have "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" 
    by (simp add: \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
  then show ?case 
    using \<open>HML_failure_trace (hml_pos \<alpha> \<psi>)\<close> by blast
next
  case (3 \<Phi> I J)
  hence neg_case: "\<forall>j\<in>\<Phi> ` J. stacked_pos_conj_pos j" 
    using stacked_pos_conj_pos.simps nested_empty_pos_conj.intros(1) by auto
  consider "\<Phi> ` I = {}"
| "(\<exists>i\<in>\<Phi> ` I.
        \<Phi> ` I = {i} \<and> hml_failure_trace i \<and> (\<exists>\<psi>. HML_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>))))
\<and> (\<forall>j\<in>\<Phi> ` J. \<exists>\<alpha>. j = hml_pos \<alpha> TT \<or> j = TT) \<and> I \<inter> J = {}"
| "(\<exists>i\<in>\<Phi> ` I.
        \<Phi> ` I = {i} \<and> hml_failure_trace i \<and> (\<exists>\<psi>. HML_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>))))
\<and> (\<forall>j\<in>\<Phi> ` J. \<exists>\<alpha>. j = hml_pos \<alpha> TT \<or> j = TT) \<and> I \<inter> J \<noteq> {}"
    using 3 by linarith
then show ?case proof(cases)
  case 1
  hence "HML_failure_trace (hml_conj I J \<Phi>) \<and> (\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Phi>)))"
    using neg_case 
    by (simp add: f_trace_conj)
  then show ?thesis by blast
next
  case 2
  then obtain i \<psi> where IH: "i\<in>\<Phi> ` I" "\<Phi> ` I = {i}" "hml_failure_trace i" "HML_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>))"
    by auto
  define \<Psi> where  \<Psi>_def: "\<Psi> = (\<lambda>x. if x \<in> I then \<psi> else (if x \<in> J then \<Phi> x else undefined))"
  have "\<Psi> ` I = {\<psi>}" unfolding \<Psi>_def using \<open>\<Phi> ` I = {i}\<close> by auto
  hence pos: "(\<exists>\<psi> \<in> (\<Psi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Psi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y))"
    by (simp add: \<open>HML_failure_trace \<psi>\<close>)
  have "\<forall>\<psi> \<in> \<Psi> ` J. stacked_pos_conj_pos \<psi>"
    unfolding \<Psi>_def
    using neg_case 2
    by auto
  hence "HML_failure_trace (hml_conj I J \<Psi>)" using pos 
    by (simp add: f_trace_conj)
  from \<Psi>_def have "(\<forall>s. \<forall>j \<in> J. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))" using IH 
    by auto
  from \<Psi>_def have "(\<forall>s. \<forall>i \<in> I. (\<not>(s \<Turnstile> (\<Psi> i)) = (\<not>(s \<Turnstile> (\<Phi> i)))))" using IH 
    by (metis emptyE imageI insertE)
  have "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Psi>)))" using IH hml_sem_conj \<Psi>_def 
    using \<open>\<forall>s. \<forall>i\<in>I. (s \<Turnstile> \<Psi> i) \<noteq> (\<not> s \<Turnstile> \<Phi> i)\<close> by auto
  then show ?thesis using \<open>HML_failure_trace (hml_conj I J \<Psi>)\<close> by blast
next
  case 3
  then obtain i \<psi> where IH: "i\<in>\<Phi> ` I" "\<Phi> ` I = {i}" "hml_failure_trace i" "HML_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>))"
    by blast
  then obtain j where "j \<in> I \<inter> J" 
    using "3" by auto 
  from 3 have "(\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>))"
    using index_sets_conj_disjunct 
    by presburger
  define \<Psi> where "\<Psi> = (\<lambda>x. if x \<in> (I \<inter> J) then TT::('a, 's) hml else undefined)"
  with \<open>j \<in> I \<inter> J\<close> have "\<Psi> ` (I \<inter> J) = {TT}" 
    by auto
  have "stacked_pos_conj_pos TT" 
    using stacked_pos_conj_pos.intros(1) by blast
  hence "(\<forall>y \<in> (\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" using \<Psi>_def \<open>j \<in> I \<inter> J\<close> 
    using \<open>\<Psi> ` (I \<inter> J) = {TT}\<close> by fastforce
  have "(\<forall>y \<in> (\<Psi> ` {}). nested_empty_conj y) \<and> (\<forall>y \<in> (\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" 
    using neg_case 
    using \<open>\<forall>y\<in>\<Psi> ` (I \<inter> J). stacked_pos_conj_pos y\<close> by blast
  hence f_trace: "((\<exists>\<psi>\<in>(\<Psi> ` ({}::'s set)). HML_failure_trace \<psi> \<and> (\<forall>y\<in>(\<Psi> ` ({}::'s set)). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or>
 (\<forall>y\<in>(\<Psi> ` ({}::'s set)). nested_empty_conj y)) \<and>
(\<forall>y\<in>(\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" 
    by fastforce 
  define \<psi> where "\<psi> \<equiv> (hml_conj ({}::'s set) (I \<inter> J) \<Psi>)"
  have "HML_failure_trace \<psi>" unfolding \<psi>_def using f_trace_conj f_trace 
    by fastforce
  have "\<forall>s. \<not> s \<Turnstile> \<psi>" 
    using \<Psi>_def \<open>j \<in> I \<inter> J\<close> \<psi>_def by auto
  then show ?thesis using \<open>HML_failure_trace \<psi>\<close> 
    using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> by blast
  qed
qed

lemma \<^marker>\<open>tag (proof) visible\<close> stacked_pos_rewriting:
  assumes "stacked_pos_conj_pos \<phi>" "\<not>HML_true \<phi>"
  shows "\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
  using assms proof(induction \<phi>)
  case 1
  then show ?case 
    unfolding HML_true_def
    using TT_like.intros(1) HML_true_TT_like by simp
next
  case (2 \<psi> uu)
  then show ?case 
    using HML_true_def HML_true_nested_empty_pos_conj by auto
next
  case (3 \<Phi> I J)
  have "(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>)" 
    using lts.HML_true_nested_empty_pos_conj by blast
  have "((\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi>) \<and> \<Phi> ` J = {}) \<longrightarrow> HML_true (hml_conj I J \<Phi>)"
    by (simp add: lts.HML_true_nested_empty_pos_conj nested_empty_pos_conj.intros(2))
  with 3 obtain \<phi> where "\<phi>\<in>\<Phi> ` I"
        "stacked_pos_conj_pos \<phi>" "(\<not> HML_true \<phi> \<longrightarrow> (\<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)))"
        "(\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>)"
    by meson
  then have "\<not> HML_true \<phi>" using 3(3) \<open>(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>)\<close>
    by (smt (verit, ccfv_threshold) "3.hyps" HML_true_def ball_imageD empty_iff empty_is_image hml_sem_conj)
  then obtain \<alpha> where "\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)" 
    using \<open>\<not> HML_true \<phi> \<longrightarrow> (\<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT))\<close> by blast
  have "\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_pos \<alpha> TT)" 
    using "3.hyps" "3.prems" HML_true_def \<open>\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>\<close> \<open>\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>\<close> \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)\<close> by fastforce
  then show ?case by blast
qed

lemma \<^marker>\<open>tag (proof) visible\<close> nested_empty_conj_TT_or_FF:
  assumes "nested_empty_conj \<phi>"
  shows "(\<forall>s. (s \<Turnstile> \<phi>)) \<or> (\<forall>s. \<not>(s \<Turnstile> \<phi>))"
  using assms HML_true_nested_empty_pos_conj
  unfolding HML_true_def
  by(induction, simp, fastforce)

lemma \<^marker>\<open>tag (proof) visible\<close> failure_trace_def_implies_alt_failure_trace_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_failure_trace \<phi>"
  shows "\<exists>\<psi>. hml_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case f_trace_tt
  then show ?case 
    using hml_failure_trace.intros(1) by blast
next
  case (f_trace_pos \<phi> \<alpha>)
  then obtain \<psi> where "hml_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  have "hml_failure_trace (hml_pos \<alpha> \<psi>)" 
    using \<open>hml_failure_trace \<psi>\<close> hml_failure_trace.simps by blast
  have "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" 
    by (simp add: \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
  then show ?case 
    using \<open>hml_failure_trace (hml_pos \<alpha> \<psi>)\<close> by blast
next
  case (f_trace_conj \<Phi> I J)
  hence neg_case: "\<forall>j\<in>\<Phi> ` J. stacked_pos_conj_pos j" 
    using stacked_pos_conj_pos.simps nested_empty_pos_conj.intros(1) by auto
  from f_trace_conj have IH: "((\<exists>\<psi>\<in>\<Phi> ` I.
            (HML_failure_trace \<psi> \<and> (\<exists>\<psi>'. hml_failure_trace \<psi>' \<and> (\<forall>s. (s \<Turnstile> \<psi>) = (s \<Turnstile> \<psi>')))) \<and>
            (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or>
        (\<forall>y\<in>\<Phi> ` I. nested_empty_conj y))" 
    by blast
  from IH show ?case proof(rule disjE)
    assume "\<exists>\<psi>\<in>\<Phi> ` I.
       (HML_failure_trace \<psi> \<and> (\<exists>\<psi>'. hml_failure_trace \<psi>' \<and> (\<forall>s. (s \<Turnstile> \<psi>) = (s \<Turnstile> \<psi>')))) \<and>
       (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
    then obtain \<phi> \<psi> where "\<phi>\<in>\<Phi> ` I" "HML_failure_trace \<phi>" "hml_failure_trace \<psi>" 
                          "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
      by meson
    then obtain i_\<phi> where "\<Phi> i_\<phi> = \<phi>" 
      by blast
    consider "\<exists>y \<in> \<Phi>`I. \<phi> \<noteq> y \<and> (\<forall>s. \<not>(s \<Turnstile> y))" | "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> HML_true y)"
      unfolding HML_true_def
      using nested_empty_conj_TT_or_FF
      using \<open>\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> nested_empty_conj y\<close> by blast
    then show "\<exists>\<psi>. hml_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> \<psi>))"
    proof(cases)
      case 1
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)"
        using hml_sem_conj by blast
      obtain y where "y \<in> \<Phi>`I" "\<phi> \<noteq> y \<and> (\<forall>s. \<not> s \<Turnstile> y)" 
        using "1" by blast
      define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> I then (TT::('a, 's)hml) else undefined))"
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} I \<Psi>)" 
        using \<open>y \<in> \<Phi> ` I\<close> by auto
      have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` I. j = TT" 
         apply blast
        unfolding \<Psi>_def 
        using \<open>y \<in> \<Phi>`I\<close> 
        by simp
      hence "hml_failure_trace (hml_conj {} I \<Psi>)" 
        by (meson hml_failure_trace.intros(3))
      then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} I \<Psi>\<close> by blast
    next
      case 2
      consider "\<forall>y \<in> \<Phi>`J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" | "(\<exists>y\<in>\<Phi> ` J. HML_true y)"
        unfolding HML_true_def
        using stacked_pos_rewriting neg_case
        using that(2) by blast
      then show ?thesis proof(cases)
        case 1
        show ?thesis proof(cases "\<Phi> ` I \<inter> \<Phi> ` J = {}")
          case True
          hence "I \<inter> J = {}"
            by blast
          from 2 have "\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> (\<forall>s. s \<Turnstile> y)"
            unfolding HML_true_def 
            by blast
          hence "\<forall>s. (\<forall>i \<in> I. s \<Turnstile> (\<Phi> i)) \<longleftrightarrow> s \<Turnstile> \<phi>"
            using \<open>\<phi> \<in> \<Phi> ` I\<close> by auto
          define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then \<psi> 
                                    else (if i \<in> J then (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)  
                                                else undefined)))"
          have "\<phi> \<notin> \<Phi> ` J"
            using True \<open>\<phi> \<in> \<Phi> ` I\<close> 
            by blast
          hence "\<forall>i \<in> J. \<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)"
            using True "1" \<Psi>_def  
            using \<open>\<Phi> i_\<phi> = \<phi>\<close> by auto
          have "\<forall>j \<in> J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
            using neg_case stacked_pos_rewriting "1" by blast
          hence "\<forall>j \<in> J. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> \<Psi> j))"
            using True \<open>\<forall>i \<in> J. \<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)\<close>
            by (smt (verit, ccfv_threshold) tfl_some)
          have "\<forall>i \<in> I. \<Phi> i \<noteq> \<phi> \<longrightarrow> (\<forall>s. s \<Turnstile> \<Phi> i)"
            by (simp add: \<open>\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> (\<forall>s. s \<Turnstile> y)\<close>) 
          have "\<Psi> ` {i_\<phi>} = {\<psi>}" 
            using \<Psi>_def \<open>\<phi>\<in>\<Phi> ` I\<close> \<open>\<phi> \<notin> \<Phi> ` J\<close> \<open>I \<inter> J = {}\<close>
            by simp
          hence "\<forall>s. (\<forall>i \<in> {i_\<phi>}. s \<Turnstile> (\<Psi> i)) \<longleftrightarrow> s \<Turnstile> \<psi>" 
            using \<open>\<phi> \<in> \<Phi> ` I\<close> \<Psi>_def \<open>\<Phi> i_\<phi> = \<phi>\<close> by auto
          hence "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {i_\<phi>} J \<Psi>)"
            using \<open>\<forall>j \<in> J. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> \<Psi> j))\<close>
            by (simp add: \<open>\<forall>s. (\<forall>i\<in>I. s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<phi>)\<close> \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
          have "\<forall>j \<in> \<Psi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT)" 
            using \<open>\<forall>i\<in>J. \<Psi> i = hml_pos (SOME \<alpha>. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> hml_pos \<alpha> TT)) TT\<close> by blast
          have "(\<exists>i \<in> \<Psi> ` {i_\<phi>}. \<Psi> ` {i_\<phi>} = {i} \<and> hml_failure_trace i)"
            using \<Psi>_def
            using \<open>\<Psi> ` {i_\<phi>} = {\<psi>}\<close> \<open>hml_failure_trace \<psi>\<close> by auto
          have "hml_failure_trace (hml_conj {i_\<phi>} J \<Psi>)"
            by (meson \<open>\<exists>i\<in>\<Psi> ` {i_\<phi>}. \<Psi> ` {i_\<phi>} = {i} \<and> hml_failure_trace i\<close> \<open>\<forall>j\<in>\<Psi> ` J. \<exists>\<alpha>. j = hml_pos \<alpha> TT\<close> hml_failure_trace.intros(3))
          then show ?thesis using \<open>\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {i_\<phi>} J \<Psi>)\<close>
            by blast
        next
          case False
          hence "\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>)" 
            by fastforce
          then obtain \<phi> i_\<phi> where "\<phi> \<in> \<Phi> ` I \<inter> \<Phi> ` J" "\<Phi> i_\<phi> = \<phi>" 
            using False by blast
          define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
          hence "\<forall>s. \<not>(s \<Turnstile> hml_conj {} {i_\<phi>} \<Psi>)" 
            by simp
          have "hml_failure_trace (hml_conj {} {i_\<phi>} \<Psi>)" 
            by (simp add: \<Psi>_def hml_failure_trace.intros(3))
          then show ?thesis using \<open>\<forall>s. \<not>(s \<Turnstile> hml_conj {} {i_\<phi>} \<Psi>)\<close> \<open>\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>)\<close> 
            by blast
        qed
      next
        case 2
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
          unfolding HML_true_def 
          by fastforce
        obtain y where "y \<in> \<Phi>`J" "(\<forall>s. s \<Turnstile> y)" 
          using "2"
          unfolding HML_true_def 
          by blast
      define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> J then (TT::('a, 's)hml) else undefined))"
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} J \<Psi>)" 
        using \<open>y \<in> \<Phi> ` J\<close> by auto
      have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` J. j = TT" 
         apply blast
        unfolding \<Psi>_def 
        using \<open>y \<in> \<Phi>`J\<close> 
        by simp
      hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
        by (meson hml_failure_trace.intros(3))
      then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} J \<Psi>\<close> by blast
    qed
  qed
next
    assume "\<forall>y\<in>\<Phi> ` I. nested_empty_conj y"
    then show ?thesis proof(cases "\<exists>i\<in>I. (\<forall>s. (\<not>(s \<Turnstile> (\<Phi> i))))")
      case True
      hence "\<forall>s. (\<not>(s \<Turnstile> hml_conj I J \<Phi>))" 
        using hml_sem_conj by blast
      define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> I then TT:: ('a, 's) hml else undefined))"
      have "\<forall>j \<in> \<Psi> ` I. j = TT" 
        using \<Psi>_def by force
      hence "hml_failure_trace (hml_conj {} I \<Psi>)" using hml_failure_trace.intros(3)
        by (metis image_empty)
      have "\<forall>s. (\<not>(s \<Turnstile> hml_conj {} I \<Psi>))" 
        using True \<Psi>_def by force
      then show ?thesis using \<open>hml_failure_trace (hml_conj {} I \<Psi>)\<close> \<open>\<forall>s. (\<not>(s \<Turnstile> hml_conj I J \<Phi>))\<close>
        by blast
    next
      case False
      consider "\<forall>y \<in> \<Phi>`J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" | "(\<exists>y\<in>\<Phi> ` J. HML_true y)"
        using neg_case stacked_pos_rewriting by blast
      then show ?thesis proof(cases)
        case 1
        from False have "\<forall>i \<in> I. (\<forall>s. (s \<Turnstile> (\<Phi> i)))"
        using nested_empty_conj_TT_or_FF \<open>\<forall>y\<in>\<Phi> ` I. nested_empty_conj y\<close> by blast 
        have "\<forall>i \<in> {}. (\<forall>s. (s \<Turnstile> (\<Phi> i)))" by blast
        define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J 
              then (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> (\<Phi> i)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT:: ('a, 's) hml) 
              else undefined))"
      have "\<forall>j\<in>\<Phi> ` J. (\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT))))" 
        using stacked_pos_rewriting neg_case 1 by blast
      hence "\<forall>j \<in> J. (\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT))))" 
        by blast
      hence "\<forall>j \<in> J. \<exists>\<alpha> .\<Psi> j = (hml_pos \<alpha> TT) \<and> (\<forall>s. (s \<Turnstile> (\<Phi> j)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
      proof(safe)
        fix j
        assume "\<forall>j\<in>J. \<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT)" "j \<in> J"
        then obtain \<alpha> where "\<Psi> j = hml_pos \<alpha> TT" 
          using \<Psi>_def by fastforce
        hence "(\<forall>s. (s \<Turnstile> (\<Phi> j)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" unfolding \<Psi>_def using \<open>j \<in> J\<close> 
          by (smt (verit, best) \<open>\<forall>j\<in>J. \<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT)\<close> tfl_some)
        then show "\<exists>\<alpha>. \<Psi> j = hml_pos \<alpha> TT \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT))"
          using \<open>\<Psi> j = hml_pos \<alpha> TT\<close> by blast
      qed
      hence "\<forall>j \<in> J. \<forall>s. s \<Turnstile> (\<Psi> j) \<longleftrightarrow> s \<Turnstile> (\<Phi> j)" using \<Psi>_def 
        by metis
      hence "\<forall>j \<in> J. \<forall>s. \<not>s \<Turnstile> (\<Psi> j) \<longleftrightarrow> \<not>s \<Turnstile> (\<Phi> j)" by blast
      hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj {} J \<Psi>))"
        using \<open>\<forall>i \<in> I. (\<forall>s. (s \<Turnstile> (\<Phi> i)))\<close> \<open>\<forall>i \<in> {}. (\<forall>s. (s \<Turnstile> (\<Phi> i)))\<close> 
        by simp
      have "\<forall>j \<in> \<Psi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT)" 
        by (simp add: \<Psi>_def)
      hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
        by (simp add: hml_failure_trace.intros(3))
      then show ?thesis
        using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj {} J \<Psi>)\<close> by blast
      next
        case 2
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
          unfolding HML_true_def 
          by fastforce
        obtain y where "y \<in> \<Phi>`J" "(\<forall>s. s \<Turnstile> y)" 
          using "2"
          unfolding HML_true_def 
          by blast
        define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> J then (TT::('a, 's)hml) else undefined))"
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} J \<Psi>)" 
          using \<open>y \<in> \<Phi> ` J\<close> by auto
        have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` J. j = TT" 
           apply blast
          unfolding \<Psi>_def 
          using \<open>y \<in> \<Phi>`J\<close> 
          by simp
        hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
          by (meson hml_failure_trace.intros(3))
        then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
          using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} J \<Psi>\<close> by blast
      qed
    qed
  qed 
qed
end
end