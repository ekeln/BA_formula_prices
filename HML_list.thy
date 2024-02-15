(*<*)
theory HML_list
  imports
 Main
 Transition_Systems

begin
(*>*)
subsection \<open>Hennessy--Milner logic\<close>
text \<open>Hennessy--Milner logic, first introduced by Matthew Hennessy and Robin Milner (citation), is a modal logic for expressing properties of systems described by LTS.
Intuitively, HML describes observations on an LTS and two processes are considered equivalent under HML when there exists no observation that distinguishes between them.
(citation) defined the modal-logical language as consisting of (finite) conjunctions, negations and a (modal) possibility operator:
$$\varphi ::= t\!t \mid \varphi_1 \;\wedge\; \varphi_2 \mid \neg\varphi \mid \langle\alpha\rangle\varphi$$
(where $\alpha$ ranges over the set of actions. The paper also proves that this characterization of strong bisimilarity
corresponds to a relational definition that is effectively the same as in (...). Their result can be expressed as follows:
for image-finite LTSs, two processes are strongly bisimilar iff they satisfy the same set of HML formulas. We call this the modal characterisation of
strong bisimilarity. By allowing for conjunction of arbitrary width (infinitary HML), the modal characterization of strong bisimilarity can be proved for arbitrary LTS. This is done in (...)\<close>

text \<open>\textbf{Hennessy--Milner logic}
The syntax of Hennessy--Milner logic over a set $\Sigma$ of actions, (HML) - richtige font!!!!![$\Sigma$], is defined by the grammar:
\begin{align*}
    \varphi &::= \langle a \rangle \varphi && \text{with } a \in \Sigma \\
            &\quad | \, \bigwedge_{i \in I} \psi_i \\
    \psi &::= \neg \varphi \, | \, \varphi.
\end{align*}\<close>

text \<open>The data type \<open>('a, 'i)hml\<close> formalizes the definition of HML formulas above. It is parameterized by the type of actions \<open>'a\<close> for $\Sigma$
and an index type \<open>'i\<close>. We use an index sets of arbitrary type \<open>I :: 'i set\<close> and a mapping \<open>F :: 'i \<Rightarrow> ('a, 'i) hml\<close> to formalize
conjunctions so that each element of \<open>I\<close> is mapped to a formula%
\footnote{Note that the formalization via an arbitrary set (...) does not yield a valid type, since \<open>set\<close> is not a bounded natural functor.}%.
\<close>

datatype ('a, 'i)hml =
TT |
hml_pos \<open>'a\<close> \<open>('a, 'i)hml\<close> |
hml_conj "'i set" "'i set" "'i \<Rightarrow> ('a, 'i) hml" 

text \<open>Note that in canonical definitions of HML @{term "TT"} is not usually part of the syntax,
but is instead synonymous to \<open>\<And>{}\<close>.
We include @{term "TT"} in the definition to enable Isabelle to infer that the type @{term "hml"} is not empty..
This formalization allows for conjunctions of arbitrary - even of infinite - width and has been
taken from \cite{Pohlmann2021ReducingReactive} (Appendix B).\<close>

inductive TT_like :: "('a, 'i) hml \<Rightarrow> bool"
  where
"TT_like TT" |
"TT_like (hml_conj I J \<Phi>)" if "(\<Phi> `I) = {}" "(\<Phi> ` J) = {}"

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

inductive stacked_pos_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where 
"stacked_pos_conj TT" |
"stacked_pos_conj (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"stacked_pos_conj (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). ((stacked_pos_conj \<phi>) \<or> nested_empty_conj \<phi>)"
"(\<forall>\<psi> \<in> (\<Phi> ` J). nested_empty_conj \<psi>)"

inductive stacked_pos_conj_J_empty :: "('a, 'i) hml \<Rightarrow> bool"
  where
"stacked_pos_conj_J_empty TT" |
"stacked_pos_conj_J_empty (hml_pos _ \<psi>)" if "stacked_pos_conj_J_empty \<psi>" |
"stacked_pos_conj_J_empty (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). (stacked_pos_conj_J_empty \<phi>)" "\<Phi> ` J = {}"

inductive single_pos_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"single_pos_pos TT" |
"single_pos_pos (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"single_pos_pos (hml_conj I J \<Phi>)" if 
"(\<forall>\<phi> \<in> (\<Phi> `I). (single_pos_pos \<phi>))"
"(\<Phi> ` J) = {}"

inductive single_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"single_pos TT" |
"single_pos (hml_pos _ \<psi>)" if "nested_empty_conj \<psi>" |
"single_pos (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` I). (single_pos \<phi>)"
"\<forall>\<phi> \<in> (\<Phi> ` J). single_pos_pos \<phi>"

context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I J \<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i)) \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (\<psi>s j))))\<close>

lemma index_sets_conj_disjunct:
  assumes "I \<inter> J \<noteq> {}"
  shows "\<forall>s. \<not> (s \<Turnstile> (hml_conj I J \<Phi>))"
proof(safe)
  fix s
  assume "s \<Turnstile> hml_conj I J \<Phi>"
  from assms obtain i where "i \<in> I \<inter> J" by blast
  with \<open>s \<Turnstile> hml_conj I J \<Phi>\<close> have "((s \<Turnstile> (\<Phi> i)) \<and> (\<not>(s \<Turnstile> (\<Phi> i))))"
    by auto
  then show False by blast
qed

definition HML_true where
"HML_true \<phi> \<equiv> \<forall>s. s \<Turnstile> \<phi>"

lemma 
  fixes s::'s
  assumes "HML_true (hml_conj I J \<Phi>)"
  shows "\<forall>\<phi> \<in> \<Phi> ` I. HML_true \<phi>"
  using HML_true_def assms by auto

lemma HML_true_TT_like:
  assumes "TT_like \<phi>"
  shows "HML_true \<phi>"
  using assms
  unfolding HML_true_def
  apply (induction \<phi> rule: TT_like.induct)
  by simp+

lemma HML_true_nested_empty_pos_conj:
  assumes "nested_empty_pos_conj \<phi>"
  shows "HML_true \<phi>"
  using assms
  unfolding HML_true_def
  apply (induction \<phi> rule: nested_empty_pos_conj.induct)
  by (simp, force)


text \<open>Two states are HML equivalent if they satisfy the same formula.\<close>
definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>HML_equivalent p q \<equiv> (\<forall> \<phi>::('a, 's) hml. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

text \<open> An HML formula \<open>\<phi>l\<close> implies another (\<open>\<phi>r\<close>) if the fact that some process \<open>p\<close> satisfies \<open>\<phi>l\<close>
implies that \<open>p\<close> must also satisfy \<open>\<phi>r\<close>, no matter the process \<open>p\<close>. \<close>

definition hml_impl :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Rrightarrow>" 60)  where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"

lemma hml_impl_iffI: "\<phi>l \<Rrightarrow> \<phi>r = (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"
  using hml_impl_def by force

subsection \<open> Equivalence \<close>

text \<open>
A HML formula \<open>\<phi>l\<close> is said to be equivalent to some other HML formula \<open>\<phi>r\<close> (written \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>)
iff process \<open>p\<close> satisfies \<open>\<phi>l\<close> iff it also satisfies \<open>\<phi>r\<close>, no matter the process \<open>p\<close>.

We have chosen to define this equivalence by appealing to HML formula implication (c.f. pre-order).
\<close>

definition hml_formula_eq :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Lleftarrow>\<Rrightarrow>" 60)  where
  "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

text \<open> \<open>\<Lleftarrow>\<Rrightarrow>\<close> is truly an equivalence relation. \<close>
lemma hml_eq_equiv: "equivp (\<Lleftarrow>\<Rrightarrow>)"
  by (smt (verit, del_insts) equivpI hml_formula_eq_def hml_impl_def reflpI sympI transpI)

lemma equiv_der:
  assumes "HML_equivalent p q" "\<exists>p'. p \<mapsto>\<alpha> p'"
  shows "\<exists>p' q'. (HML_equivalent p' q') \<and> q \<mapsto>\<alpha> q'"
  using assms hml_semantics.simps
  unfolding HML_equivalent_def 
  by metis


lemma equiv_trans: "transp HML_equivalent"
  by (simp add: HML_equivalent_def transp_def)

text \<open>
  A formula distinguishes one state from another if its true for the
  first and false for the second.
\<close>
abbreviation distinguishes ::  \<open>('a, 's) hml \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
   \<open>distinguishes \<phi> p q \<equiv> p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>

lemma hml_equiv_sym:
  shows \<open>symp HML_equivalent\<close>
unfolding HML_equivalent_def symp_def by simp

text \<open>
  If two states are not HML equivalent then there must be a
  distinguishing formula.
\<close>
(*assumes that lts is not empty, kann evtl auch aus \<not> HML_equivalent p q gezeigt werden*)
lemma hml_distinctions:
  fixes state::"'s"
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists>\<phi>. distinguishes \<phi> p q\<close>
proof-
  from assms have "\<not> (\<forall> \<phi>::('a, 's) hml. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))" 
    unfolding HML_equivalent_def by blast
  then obtain \<phi>::"('a, 's) hml" where "(p \<Turnstile> \<phi>) \<noteq> (q \<Turnstile> \<phi>)" by blast
  then have "((p \<Turnstile> \<phi>) \<and> \<not>(q \<Turnstile> \<phi>)) \<or> (\<not>(p \<Turnstile> \<phi>) \<and> (q \<Turnstile> \<phi>))"
    by blast
  then show ?thesis
  proof
    show "distinguishes \<phi> p q \<Longrightarrow> \<exists>\<phi>. distinguishes \<phi> p q" by blast
  next
    assume assm: "\<not> p \<Turnstile> \<phi> \<and> q \<Turnstile> \<phi>"
    define n\<phi> where "n\<phi> \<equiv>(hml_conj ({}::'s set) 
                          {state} 
                          (\<lambda>j. if j = state then \<phi> else undefined))"
    have "p \<Turnstile> n\<phi> \<and> \<not> q \<Turnstile> n\<phi>" 
      unfolding n\<phi>_def
      using hml_semantics.simps assm
      by force
    then show ?thesis
      by blast
  qed
qed

end (* context lts *)

(*Trace equiv: T \<in> trace, wenn \<phi> dann auch <a>\<phi>.*)
(*(\<infinity>, 1, 0, 0, 0, 0)*)
inductive HML_trace :: "('a, 's)hml \<Rightarrow> bool"
  where
trace_tt : "HML_trace TT" |
trace_conj: "HML_trace (hml_conj {} {} \<psi>s)"|
trace_pos: "HML_trace (hml_pos \<alpha> \<phi>)" if "HML_trace \<phi>"

definition HML_trace_formulas where
"HML_trace_formulas \<equiv> {\<phi>. HML_trace \<phi>}"

text \<open>translation of a trace to a formula\<close>

fun trace_to_formula :: "'a list \<Rightarrow> ('a, 's)hml"
  where
"trace_to_formula [] = TT" |
"trace_to_formula (a#xs) = hml_pos a (trace_to_formula xs)"

inductive HML_failure :: "('a, 's)hml \<Rightarrow> bool"
  where
failure_tt: "HML_failure TT" |
failure_pos: "HML_failure (hml_pos \<alpha> \<phi>)" if "HML_failure \<phi>" |
failure_conj: "HML_failure (hml_conj I J \<psi>s)" 
if "(\<forall>i \<in> I. TT_like (\<psi>s i)) \<and> (\<forall>j \<in> J. (TT_like (\<psi>s j)) \<or> (\<exists>\<alpha> \<chi>. ((\<psi>s j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))" 

inductive HML_simulation :: "('a, 's)hml \<Rightarrow> bool"
  where
sim_tt: "HML_simulation TT" |
sim_pos: "HML_simulation (hml_pos \<alpha> \<phi>)" if "HML_simulation \<phi>"|
sim_conj: "HML_simulation (hml_conj I J \<psi>s) " 
if "(\<forall>x \<in> (\<psi>s ` I). HML_simulation x) \<and> (\<psi>s ` J = {})"

definition HML_simulation_formulas where
"HML_simulation_formulas \<equiv> {\<phi>. HML_simulation \<phi>}"

inductive HML_readiness :: "('a, 's)hml \<Rightarrow> bool"
  where
read_tt: "HML_readiness TT" |
read_pos: "HML_readiness (hml_pos \<alpha> \<phi>)" if "HML_readiness \<phi>"|
read_conj: "HML_readiness (hml_conj I J \<Phi>)" 
if "(\<forall>x \<in> (\<Phi> ` (I \<union> J)). TT_like x \<or> (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"

inductive HML_impossible_futures ::  "('a, 's)hml \<Rightarrow> bool"
  where
  if_tt: "HML_impossible_futures TT" |
  if_pos: "HML_impossible_futures (hml_pos \<alpha> \<phi>)" if "HML_impossible_futures \<phi>" |
if_conj: "HML_impossible_futures (hml_conj I J \<Phi>)"
if "\<forall>x \<in> (\<Phi> ` I). TT_like x" "\<forall>x \<in> (\<Phi> ` J). (HML_trace x)"

inductive HML_possible_futures :: "('a, 's)hml \<Rightarrow> bool"
  where
pf_tt: "HML_possible_futures TT" |
pf_pos: "HML_possible_futures (hml_pos \<alpha> \<phi>)" if "HML_possible_futures \<phi>" |
pf_conj: "HML_possible_futures (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> ` (I\<union> J)). (HML_trace x)"

definition HML_possible_futures_formulas where
"HML_possible_futures_formulas \<equiv> {\<phi>. HML_possible_futures \<phi>}"

inductive HML_failure_trace :: "('a, 's)hml \<Rightarrow> bool"
  where
f_trace_tt: "HML_failure_trace TT" |
f_trace_pos: "HML_failure_trace (hml_pos \<alpha> \<phi>)" if "HML_failure_trace \<phi>"|
f_trace_conj: "HML_failure_trace (hml_conj I J \<Phi>)"
if "((\<exists>\<psi> \<in> (\<Phi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Phi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or> 
(\<forall>y \<in> (\<Phi> ` I). nested_empty_conj y)) \<and>
(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_pos y)"

(*TODO: überprüfen*)
inductive HML_ready_trace :: "('a, 's)hml \<Rightarrow> bool"
  where
r_trace_tt: "HML_ready_trace TT" |
r_trace_pos: "HML_ready_trace (hml_pos \<alpha> \<phi>)" if "HML_ready_trace \<phi>"|
r_trace_conj: "HML_ready_trace (hml_conj I J \<Phi>)" 
if "(\<exists>x \<in> (\<Phi> ` I). HML_ready_trace x \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> single_pos y))
\<or> (\<forall>y \<in> (\<Phi> ` I).single_pos y)"
"(\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"

inductive HML_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"HML_ready_sim TT" |
"HML_ready_sim (hml_pos \<alpha> \<phi>)" if "HML_ready_sim \<phi>" |
"HML_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). HML_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). single_pos_pos y)"

inductive HML_2_nested_sim :: "('a, 's) hml \<Rightarrow> bool" 
  where
"HML_2_nested_sim TT" |
"HML_2_nested_sim (hml_pos \<alpha> \<phi>)" if "HML_2_nested_sim \<phi>" |
"HML_2_nested_sim (hml_conj I J \<Phi>)" 
if "(\<forall>x \<in> (\<Phi> ` I). HML_2_nested_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). HML_simulation y)"
                                                                
inductive HML_revivals :: "('a, 's) hml \<Rightarrow> bool" 
  where
revivals_tt: "HML_revivals TT" |
revivals_pos: "HML_revivals (hml_pos \<alpha> \<phi>)" if "HML_revivals \<phi>" |
revivals_conj: "HML_revivals (hml_conj I J \<Phi>)" if "(\<forall>x \<in> (\<Phi> ` I). \<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>)"
"(\<forall>x \<in> (\<Phi> ` J). \<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>)"

end