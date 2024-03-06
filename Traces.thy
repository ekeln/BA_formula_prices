(*<*)
theory Traces
imports Transition_Systems HML formula_prices_list HML_list
begin    
(*>*)

section \<open>Trace semantics\<close>

text \<open>As discussed, trace semantics identifies two processes as equivalent if they allow for the same set of observations, or sequences of actions.\<close>

subsubsection \<open>Definition 3.1.1\<close>

text \<open>\textit{The \textnormal{modal-characterization of trace semantics} is given by the set $\mathcal{O}_T$ of trace formulas over Act, recursively defined by:}
\begin{align*}
&\langle a \rangle\varphi\in\mathcal{O}_T \text{ if } \varphi\in \mathcal{O}_T \text{ and }a\in\Act\\
&\bigwedge\varnothing\in \mathcal{O}_T
\end{align*}\<close>
inductive hml_trace :: "('a, 's)hml \<Rightarrow> bool" where
trace_tt: "hml_trace TT" |
trace_conj: "hml_trace (hml_conj {} {} \<psi>s)"|
trace_pos: "hml_trace (hml_pos \<alpha> \<phi>)" if "hml_trace \<phi>"

definition hml_trace_formulas
  where
"hml_trace_formulas \<equiv> {\<phi>. hml_trace \<phi>}"
text \<open>This definition allows for the construction of traces such as $\langle a_1 \rangle \langle a_2 \rangle \ldots \langle a_n \rangle \textsf{T}$, which represents action sequences or traces.
Two processes $p$ and $q$ are considered trace-equivalent if they satisfy the same formulas in $\mathcal{O}_T$, namely 
$$p \sim_T q \longleftrightarrow \forall\varphi\in\mathcal{O}_T. p\models\varphi \longleftrightarrow q\models\varphi$$\<close>

context lts
begin

definition hml_trace_equivalent where
"hml_trace_equivalent p q \<equiv> HML_subset_equivalent hml_trace_formulas p q"

text \<open>The subset $\mathcal{O}_X$ only allows for finite sequences of actions, without the use of conjunctions or negations. 
Therefore, the complexity of a trace formula is limited by its modal depth (and one conjunction for \textsf{T}). 
As a result, the language derivied from the price coordinate $(\infty, 1, 0, 0, 0, 0)$ encompasses all trace formulas. 
We refer to this HML-sublanguage as $\mathcal{O}{e_T}$.\<close>

definition expr_traces
  where
"expr_traces = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))}"

definition expr_trace_equivalent 
  where
"expr_trace_equivalent p q \<equiv> HML_subset_equivalent expr_traces p q"
end
subsubsection \<open>Proposition 3.1.2\<close>
text \<open>The language of formulas with prices below $(\infty, 1, 0, 0, 0, 0)$ characterizes trace equivalence. That is, for two processes $p$ and $q$, $p \sim_T q \longleftrightarrow p \sim_{e_T} q$. Explicitly: \\

\[
\forall \varphi \in \mathcal{O}_T. p \models \varphi \longleftrightarrow q \models \varphi \longleftrightarrow \forall \varphi \in \mathcal{O}_{e_T}. p \models \varphi \longleftrightarrow q \models \varphi
\]\<close>

text \<open>\textit{Proof.} We show that $\mathcal{O}_T$ and $\mathcal{O}_{e_T}$ capture the same set of formulas. We do this for both sides by induction over the structure of \textsf{HML}[$\Sigma$].

First, we show that if $\varphi \in \mathcal{O}_\text{T}$, then \textsf{expr}$(\varphi) \leq (\infty, 1, 0, 0, 0, 0)$:
\begin{align*}
&\textit{(Base) Case $\bigwedge\varnothing$:} &&\parbox[t]{0.8\textwidth}{We can easily derive that $\bigwedge\varnothing = (0, 1, 0, 0, 0, 0)$ and thus $\bigwedge\varnothing \leq (\infty, 1, 0, 0, 0, 0)$.}\\
&\textit{Case $\langle a \rangle \varphi$:} &&\parbox[t]{0.8\textwidth}{Since $\langle a \rangle$ only adds to $\textsf{expr}_1$, we can easily show that if $\textsf{expr}(\varphi) \leq (\infty, 1, 0, 0, 0, 0)$, then $\langle a \rangle\varphi \leq (\infty, 1, 0, 0, 0, 0)$.}
\end{align*}
\<close>
text \<open>Next, we show that if $\textsf{expr}(\varphi) \leq (\infty, 1, 0, 0, 0, 0)$, then $\varphi \in \mathcal{O}_\text{X}$:
\begin{align*}
&\textit{Case $\bigwedge_{i\in I}(\psi_i)$:} &&\parbox[t]{0.8\textwidth}{Since every formula ends with \textsf{T}, and $\textsf{expr}_2$ denotes the depth of a conjunction, $\textsf{expr}_2(\bigwedge_{i\in I}(\psi_i)) \geq 2$ if $I\neq\varnothing$. Therefore, $I$ must be empty.} \\
&\textit{Case $\langle a \rangle\varphi$:} &&\parbox[t]{0.8\textwidth}{From the induction hypothesis and the monotonicity attribute, we have that $\varphi\in\mathcal{O}_T$. With the definition of $\mathcal{O}_T$, we have that $\langle a \rangle\varphi\in\mathcal{O}_T$.}
\end{align*}
\<close>
(*<*)
lemma \<^marker>\<open>tag (proof) visible\<close> expr_2_lb: 
  shows "expr_2 f \<ge> 1"
  by ((induction f), simp+)
(*>*)

lemma trace_right: 
  assumes "hml_trace \<phi>"
  shows "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using assms
proof(induct \<phi> rule:hml_trace.induct)
  case trace_tt
  then show ?case by simp
next
  case (trace_conj \<psi>s)
  have "(expr_4 (hml_conj {} {} \<psi>s)) = 0"
    using expr_4.simps Sup_enat_def by auto
  then show ?case by auto
next
  case (trace_pos \<phi> \<alpha>)
  then show ?case by simp
qed

lemma HML_trace_conj_empty:
  assumes A1: "less_eq_t (expr (hml_conj I J \<Phi>)) (\<infinity>, 1, 0, 0, 0, 0)" 
  shows "I = {} \<and> J = {}"
proof-
  have "expr_2 (hml_conj I J \<Phi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)"
    using formula_prices_list.expr_2_conj by blast
  with assms have "... \<le> 1"
    using expr.simps less_eq_t.simps
    by simp
  hence le_0: "Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) \<le> 0"
    by simp
  hence le_0: "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<le> 0" "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` J). x \<le> 0"
    using Sup_le_iff UnCI
    by metis+
  have "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` I). x \<ge> 1" 
    "\<forall>x \<in> ((expr_2 \<circ> \<Phi>) ` J). x \<ge> 1" using expr_2_lb
    by fastforce+
  with le_0 show ?thesis using imageI 
    by simp
qed

lemma trace_left:
  assumes "(less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  shows "(hml_trace \<phi>)"
  using assms
proof(induction \<phi>)
  case TT
  then show ?case
    using trace_tt by blast
next
  case (hml_pos \<alpha> \<phi>)
  then show ?case 
    using trace_pos by simp
next
  case (hml_conj I J \<Phi>)
  then show ?case using HML_trace_conj_empty trace_conj
    by metis
qed

(*<*)
lemma \<^marker>\<open>tag (proof) visible\<close> HML_trace_lemma: 
"(hml_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using trace_left trace_right by blast
(*>*)

context lts begin

lemma "hml_trace_equivalent p q \<longleftrightarrow> expr_trace_equivalent p q"
  unfolding hml_trace_equivalent_def HML_subset_equivalent_def expr_trace_equivalent_def expr_traces_def hml_trace_formulas_def
  using HML_trace_lemma 
  by blast

end

text \<open>On Infinity...\<close>


(*APPENDIX? (Bei HM-trace-theorem)*)
(*<*)
text \<open>In classical concurrency theory, trace semantics are not defined in terms of modal-logical characterizations but instead using trace sets.
$\sigma \in \Act^*$ is a \textit{trace} of a process $p$ if there is a process $q$ such that $p\xrightarrow{\sigma}^*q$.
Let $T(p)$ denote the set of traces of $p$.\<close>
context lts begin

abbreviation traces :: \<open>'s \<Rightarrow> 'a list set\<close>
  where \<open>traces p \<equiv> {tr. \<exists>p'. p \<mapsto>$ tr p'}\<close>

text \<open>Every process has the empty trace\<close>

lemma empty_trace_trivial:
  fixes p
  shows \<open>[] \<in> traces p\<close>
  using step_sequence.intros by blast

text \<open>We say that $p$ is trace preordered by $q$ iff $T(p) \subset T(q)$.\<close>

definition trace_preordered (infix \<open>\<lesssim>T\<close> 60) where
  \<open>p \<lesssim>T q \<equiv> traces p \<subseteq> traces q\<close>

text \<open>We can define trace equivalence as mutual preorder, which means that $p \sim_T q$ iff $T(p) = T(q)$.\<close>

abbreviation trace_equivalent (infix \<open>\<simeq>T\<close> 60) where
  \<open>p \<simeq>T q \<equiv> p \<lesssim>T q \<and> q \<lesssim>T p\<close>

text \<open>Trace preorder is transitive.\<close>
lemma trace_preorder_transitive:
  shows \<open>transp (\<lesssim>T)\<close>
  unfolding transp_def trace_preordered_def by blast

lemma \<open>equivp (\<simeq>T)\<close>
proof (rule equivpI)
  show \<open>reflp (\<simeq>T)\<close>
    unfolding reflp_def trace_preordered_def by blast
  show \<open>symp (\<simeq>T)\<close>
    unfolding symp_def by blast
  show \<open>transp (\<simeq>T)\<close>
    unfolding transp_def trace_preordered_def by blast
qed
(*>*)

end
end