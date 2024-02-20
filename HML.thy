(*<*)
theory HML
imports Main Transition_Systems
begin
(*>*)

section \<open>Hennessy--Milner logic\<close>
text \<open>For the purpose of this thesis, we focus on the modal-logical characterizations of equivalences, using Hennessy--Milner logic (HML). 
First introduced by Matthew Hennessy and Robin Milner (citation), HML is a modal logic for expressing properties of systems described by LTS.
Intuitively, HML describes observations on an LTS and two processes are considered equivalent under HML when there exists no observation that distinguishes between them.
(citation) defined the modal-logical language as consisting of (finite) conjunctions, negations and a (modal) possibility operator:
$$\varphi ::= t\!t \mid \varphi_1 \;\wedge\; \varphi_2 \mid \neg\varphi \mid \langle\alpha\rangle\varphi$$
(where $\alpha$ ranges over the set of actions. The paper also proves that this characterization of strong bisimilarity
corresponds to a relational definition that is effectively the same as in (...). Their result can be expressed as follows:
for image-finite LTSs, two processes are strongly bisimilar iff they satisfy the same set of HML formulas. We call this the modal characterisation of
strong bisimilarity. By allowing for conjunction of arbitrary width (infinitary HML), the modal characterization of strong bisimilarity can be proved for arbitrary LTS. This is done in (...)\<close>


text \<open>Mention: HML to capture equivalences (Spectrum, HM theorem)\<close>
subsubsection \<open>Hennessy--Milner logic\<close>
text \<open>The syntax of Hennessy--Milner logic over a set $\Sigma$ of actions, (HML) - richtige font!!!!![$\Sigma$], is defined by the grammar:
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

context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I J \<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i)) \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (\<psi>s j))))\<close>

definition HML_true where
"HML_true \<phi> \<equiv> \<forall>s. s \<Turnstile> \<phi>"

lemma 
  fixes s::'s
  assumes "HML_true (hml_conj I J \<Phi>)"
  shows "\<forall>\<phi> \<in> \<Phi> ` I. HML_true \<phi>"
  using HML_true_def assms by auto

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
  distinguishing formula.\<close>

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
end