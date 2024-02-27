(*<*)
theory Traces
imports Transition_Systems HML formula_prices_list HML_list
begin    
(*>*)

subsection \<open>Trace semantics\<close>

context lts
begin

text \<open>As discussed, trace semantics identifies two processes as equal if they can perform the same set of action sequences.
$\sigma \in \Act^* is a \textit{trace} of a process $p$ if there is a process $q$ such that $p\xrightarrow{\sigma}^*q$.
Let $T(p)$ denote the set of traces of $p$.\<close>
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

text \<open>\textbf{Definition} The set $\mathcal{L}_T$ of trace formulas over Act is recursively defined by:
\begin{align*}
\bigwedge\varnothing\in \mathcal{L}_T\\
\text{If } \varphi\in \mathcal{L}_T \text{ and }a\in\Act\text{ then } \langle a \rangle\varphi\in\mathcal{L}_T
\end{align*}\<close>
inductive hml_trace :: "('a, 's)hml \<Rightarrow> bool" where
trace_tt: "hml_trace TT" |
trace_conj: "hml_trace (hml_conj {} {} \<psi>s)"|
trace_pos: "hml_trace (hml_pos \<alpha> \<phi>)" if "hml_trace \<phi>"

definition hml_trace_formulas
  where
"hml_trace_formulas \<equiv> {\<phi>. hml_trace \<phi>}"

text \<open>Two processes $p$ and $q$ are trace-equivalent, if they satisfy the same formulas in $\mathcal{L}_T$\<close>

definition hml_trace_equivalent where
"hml_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> hml_trace_formulas \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

text \<open>This definition allows for the construction of trace such as $(\langle a_1 \rangle \langle a_2 \rangle \ldots \langle a_n \rangle \textsf{T})$, which represents action sequences or traces.\<close>

text \<open>\textbf{Proposition} The language of formulas with prices below $(\infty, 1, 0, 0, 0, 0)$ characterizes trace equivalence, that is
for two processes $p$, $q$: 
$(\forall\varphi \in \mathcal{O}_T. p \models \varphi \longleftrightarrow q \models \varphi) \longleftrightarrow (\forall\varphi \in \mathcal{L}_T. p \models \varphi \longleftrightarrow q \models \varphi)$\<close>

definition expr_traces
  where
"expr_traces = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))}"

definition expr_trace_equivalent 
  where
"expr_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_traces \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

lemma expr_2_lb: "expr_2 f \<ge> 1"
  by ((induction f), simp+)

subsection \<open>The set of formulas with prices less then or equal to (\infty, 1, 0, 0, 0, 0) is a subset of the HML trace subset\<close>

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

subsection \<open>The HML trace set is a subset of the set of formulas with prices less then or equal to 
(\<infinity>, 1, 0, 0, 0, 0)\<close>

\<comment> \<open>The set induced by the coordinates (\<infinity>, 1, 0, 0, 0, 0) only includes empty conjunctions\<close>
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

lemma HML_trace_lemma: 
"(hml_trace \<phi>) = (less_eq_t (expr \<phi>) (\<infinity>, 1, 0, 0, 0, 0))"
  using trace_left trace_right by blast

lemma "hml_trace_equivalent p q \<longleftrightarrow> expr_trace_equivalent p q"
  unfolding hml_trace_equivalent_def expr_trace_equivalent_def expr_traces_def hml_trace_formulas_def
  using HML_trace_lemma 
  by blast

text \<open>On Infinity...\<close>
end
end