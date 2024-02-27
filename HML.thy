(*<*)
theory HML
imports Main Transition_Systems
begin
(*>*)

section \<open>Hennessy--Milner logic\<close>
(*Viele dopplungen mit introduction*)
text \<open>For the purpose of this thesis, we focus on the modal-logical characterizations of equivalences, using Hennessy--Milner logic (HML). 
First introduced by Matthew Hennessy and Robin Milner (citation), HML is a modal logic for expressing properties of systems described by LTS.
Intuitively, HML describes observations on an LTS and two processes are considered equivalent under HML if there exists no observation that distinguishes between them.
(citation) defined the modal-logical language as consisting of (finite) conjunctions, negations and a (modal) possibility operator:
$$\varphi ::= t\!t \mid \varphi_1 \;\wedge\; \varphi_2 \mid \neg\varphi \mid \langle\alpha\rangle\varphi$$
(where $\alpha$ ranges over the set of actions.) The paper also proves that this language characterizes a relation that is effectively the same as bisimilarity. 
Thsi theorem is called the Hennessy--Milner Theorem and can be expressed as follows: for image-finite LTSs, two processes are bisimilar iff they satisfy the same set of HML formulas. We call this the modal characterisation of
bisimilarity. (Infinitary) Hennessy--Milner logic extends the original definition by allowing for conjunction of arbitrary width. 
This yields the modal characterization of bisimilarity for arbitrary LTS (cite). In (Section Bisimilarity) provide an intuition of the proof along with the Isabelle proof.
In the following sections we mean the infinitary version when talking about HML.\<close>

subsubsection \<open>Definition 2.2.1 (Hennessy--Milner logic)\<close>
text \<open>\textbf{Syntax} The syntax of Hennessy--Milner logic over a set $\Sigma$ of actions HML[$\Sigma$] is defined by the grammar:
\begin{align*}
    \varphi &::= \langle a \rangle \varphi && \text{with } a \in \Sigma \\
            &\quad | \, \bigwedge_{i \in I} \psi_i \\
    \psi &::= \neg \varphi \, | \, \varphi.
\end{align*}
Where $I$ denotes an index set.\<close>

text \<open>The data type \<open>('a, 'i)hml\<close> formalizes the definition of HML formulas above. It is parameterized by the type of actions \<open>'a\<close> for $\Sigma$
and an index type \<open>'i\<close>. We use an index sets of arbitrary type \<open>I :: 'i set\<close> and a mapping \<open>F :: 'i \<Rightarrow> ('a, 'i) hml\<close> to formalize
conjunctions so that each element of \<open>I\<close> is mapped to a formula%
\footnote{Note that the formalization via an arbitrary set, i.e. \<open>hml_conj \<open>('a)hml set\<close>\<close> does not yield a valid type, since \<open>set\<close> is not a bounded natural functor.}%.
\<close>
datatype ('a, 'i)hml =
TT |
hml_pos \<open>'a\<close> \<open>('a, 'i)hml\<close> |
hml_conj \<open>'i set\<close> \<open>'i set\<close> \<open>'i \<Rightarrow> ('a, 'i) hml\<close> 

text \<open>Note that in canonical definitions of HML @{term "TT"} is not usually part of the syntax,
but is instead synonymous to \<open>\<And>{}\<close>.
We include @{term "TT"} in the definition to enable Isabelle to infer that the type @{term "hml"} is not empty..
Corresponding to the mathematical definition, this formalization allows for conjunctions of arbitrary - even of infinite - width.\<close>

text \<open>- $\langle a \rangle$: a transition Conjunction: (checking) for (possible) branching of system execution?

\textbf{Semantics} The semantics of HML parametrized by $\Sigma$ (on LTS processes) are given by the relation $\models$ : $(\Proc, \text{HML}[\Sigma])$:
\begin{align*}
  p &\models \langle \alpha \rangle\varphi && \text{if there exists } q \text{ such that } q\in\mathit{Der}(p, \alpha) \text{ and } q \models\varphi \\
  p &\models \bigwedge_{i \in I} \psi_i && \text{if } p\models\psi_i \text{ for all } i\in I \\
  p &\models \lnot\varphi && \text{if } p\not\models\varphi
\end{align*}
\<close>
context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I J \<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i)) \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (\<psi>s j))))\<close>

text \<open>A formula that is true for all processes in a LTS can be considered a property that holds universally for the system, akin to a tautology in classical logic.\<close>
definition HML_true where
"HML_true \<phi> \<equiv> \<forall>s. s \<Turnstile> \<phi>"

(*<*)
lemma 
  fixes s::'s
  assumes "HML_true (hml_conj I J \<Phi>)"
  shows "\<forall>\<phi> \<in> \<Phi> ` I. HML_true \<phi>"
  using HML_true_def assms by auto
(*>*)

text \<open>Two states are HML-equivalent if they satisfy the same formula.\<close>
definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>HML_equivalent p q \<equiv> (\<forall> \<phi>::('a, 's) hml. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

(*<*)
lemma equiv_der:
  assumes "HML_equivalent p q" "\<exists>p'. p \<mapsto>\<alpha> p'"
  shows "\<exists>p' q'. (HML_equivalent p' q') \<and> q \<mapsto>\<alpha> q'"
  using assms hml_semantics.simps
  unfolding HML_equivalent_def 
  by metis
(*>*)

text \<open>HML-equivalence is reflexive, symmetrical and transitive and therefore a valid equivalence.\<close>

lemma equiv_refl: "reflp HML_equivalent"
  by (simp add: HML_equivalent_def reflpI)

lemma equiv_trans: "transp HML_equivalent"
  by (simp add: HML_equivalent_def transp_def)

lemma hml_equiv_sym:
  shows \<open>symp HML_equivalent\<close>
  unfolding HML_equivalent_def symp_def by simp

text \<open>A formula distinguishes one state from another if its true for the first and false for the second.
\<close>
abbreviation distinguishes ::  \<open>('a, 's) hml \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
   \<open>distinguishes \<phi> p q \<equiv> p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>

text \<open>
  If two states are not HML equivalent then there must be a
  distinguishing formula.\<close>

lemma hml_distinctions:
  fixes state:: 's
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

text \<open>We can now use HML to capture differences between $p_1$ and $q_1$ of (ref Example 1). The formula
$\langle a \rangle\bigwedge\{\lnot\langle c \rangle\}$ distinguishes $p_1$ from $q_1$ and $\langle a \rangle\bigwedge\{\langle c \rangle\}$ distinguishes
$q_1$ from $p_1$. From the Hennessy--Milner Theorem follows that knowing a distinguishing formula means that $p_1$ and $q_1$ are not bisimilar.\<close>

(*<*)
text \<open>Rest im Appendix? Brauche ich formel äquivalenz noch? (Nur für modallogik-relational correspondenz)\<close>

text \<open> An HML formula \<open>\<phi>l\<close> implies another (\<open>\<phi>r\<close>) if the fact that some process \<open>p\<close> satisfies \<open>\<phi>l\<close>
implies that \<open>p\<close> must also satisfy \<open>\<phi>r\<close>, no matter the process \<open>p\<close>. \<close>

definition hml_impl :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Rrightarrow>" 60)  where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"

lemma hml_impl_iffI: "\<phi>l \<Rrightarrow> \<phi>r = (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"
  using hml_impl_def by force

subsubsection \<open> Equivalence \<close>

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

(*>*)

end (* context lts *)

(*<*)
end
(*>*)