(*<*)
theory HML
imports Main Transition_Systems
begin
(*>*)

section \<open>Hennessy--Milner logic\<close>
text \<open>For the purpose of this thesis, we focus on the modal-logical characterizations of equivalences, using Hennessy--Milner logic (HML). 
First introduced by Matthew Hennessy and Robin Milner \cite{hm85}, HML is a modal logic for expressing properties of systems described by LTS.
Intuitively, HML describes observations on an LTS and two processes are considered equivalent under HML if there exists no observation that distinguishes between them.
In their seminal paper, Matthew Hennessy and Robin Milner defined the modal-logical language as consisting of (finite) conjunctions, negations and a (modal) possibility operator:
$$\varphi ::= t\!t \mid \varphi_1 \;\wedge\; \varphi_2 \mid \neg\varphi \mid \langle\alpha\rangle\varphi \quad\text{with }\alpha\in\Sigma$$
The paper also proves that this language characterizes a relation that is effectively the same as bisimilarity. 
This theorem is called the Hennessy--Milner Theorem and can be expressed as follows: for image-finite LTSs, two processes are bisimilar iff they satisfy the same set of HML formulas. We call this the modal characterization of
bisimilarity. (Infinitary) Hennessy--Milner logic extends the original definition by allowing for conjunctions of arbitrary width. 
This yields the modal characterization of bisimilarity for arbitrary LTS and is proven in (Appendix). In the following sections we always mean the infinitary version when talking about HML.\<close>

subsubsection \<open>Definition 2.2.1 (Hennessy--Milner logic)\<close>
text \<open>\textbf{Syntax} \textit{The \textnormal{syntax of Hennessy--Milner logic} over a set $\Sigma$ of actions HML[$\Sigma$] is defined by the grammar:
\begin{align*}
    \varphi &::= \langle a \rangle \varphi && \text{with } a \in \Sigma \\
            &\quad | \, \bigwedge_{i \in I} \psi_i \\
    \psi &::= \neg \varphi \, | \, \varphi.
\end{align*}
Where $I$ denotes an index set. The empty conjunction \textsf{T} $\coloneqq \bigwedge\varnothing$ is usually omitted in writing.}

\textbf{Semantics} \textit{The \textnormal{semantics of HML} parametrized by $\Sigma$ (on LTS processes) are given by the relation $\models$ : $(\Proc, \text{HML}[\Sigma])$:
\begin{align*}
  p &\models \langle \alpha \rangle\varphi && \text{if there exists } q \text{ such that } q\in\mathit{Der}(p, \alpha) \text{ and } q \models\varphi \\
  p &\models \bigwedge_{i \in I} \psi_i && \text{if } p\models\psi_i \text{ for all } i\in I \\
  p &\models \lnot\varphi && \text{if } p\not\models\varphi
\end{align*}}\<close>

text \<open>$\langle a \rangle$ captures the observation of an $a$-transition by the system. 
Similar to propositional logic, conjunctions are used to describe multiple properties of a state that must hold simultaneously. Each conjunct represents a possible branching or execution path of the system. $\lnot\varphi$ indicates the absence of behavior represented by the subformula $\varphi$. 
\<close>

text \<open>The data type \<open>('a, 'i)hml\<close> formalizes the definition of HML formulas above. It is parameterized by the type of actions \<open>'a\<close> for $\Sigma$
and an index type \<open>'i\<close>. We include the constructor @{term "TT"} for the formula \textsf{T} as part of the Isabelle syntax. This is to enable Isabelle to infer that the type \<open>('a, 'i)hml\<close> is not empty. The constructor @{term "hml_pos"} corresponds directly to the possibility operator. 
Conjunctions are formalized using the constructor @{term "hml_conj"}. The constructor has two index sets of arbitrary type \<open>'i set\<close> and a mapping \<open>F :: 'i \<Rightarrow> ('a, 'i) hml\<close> as type variables. The first variable is used to denote the positive conjuncts and the second denotes the negative conjuncts. 
The term \<open>(hml_conj I J \<Phi>)\<close> corresponds to $\bigwedge \left( \bigcup_{i \in I} \{(\Phi\; i)\} \cup \bigcup_{i \in J} \{\lnot (\Phi\; i)\} \right)$.
We decided to formalize HML without the explicit $\psi$ to avoid using mutual recursion, since it is harder to handle especially in proofs using induction over the data type.
Note that the formalization via an arbitrary set, i.e. \<open>hml_conj \<open>('a)hml set\<close>\<close> does not yield a valid type, since \<open>set\<close> is not a bounded natural functor.
Corresponding to the mathematical definition, this formalization allows for conjunctions of arbitrary---even of infinite---width.
\<close>
datatype ('a, 'i)hml =
TT |
hml_pos \<open>'a\<close> \<open>('a, 'i)hml\<close> |
hml_conj \<open>'i set\<close> \<open>'i set\<close> \<open>'i \<Rightarrow> ('a, 'i) hml\<close> 

text \<open>The semantic models-relation is formalized in Isabelle in the context of LTS. This means that the index type \<open>'i\<close> is replaced by the type of processes \<open>'s\<close>. Since this modal-logically characterizes bisimilarity, we can conclude that it suffices for the cardinality of the indexsets to be equal to the cardinality of the set of processes.\<close>

context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists>q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I J \<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i))
                                          \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (\<psi>s j))))\<close>

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
subsubsection \<open>Definition 2.2.2\<close>
text \<open>
\textit{
\begin{itemize}
    \item As discussed, equivalences in LTS can be defined in terms of \textsf{HML} subsets. Two processes are \textnormal{X-equivalent} regarding a subset of Hennessy--Milner logic, $\mathcal{O}_X \subseteq \textnormal{HML}[\Sigma]$, if they satisfy the same formulas of that subset. 
    \item A subset provides a \textnormal{modal-logical characterization} of an equivalence X if, according to that subset, the same processes are considered equivalent as they are under the colloquial definition of that equivalence.
    \item A formula $\varphi \in \textnormal{HML}[\Sigma]$ \textnormal{distinguishes} one state from another if it is true for the former and false for the latter.
\end{itemize}
}\<close>

text \<open>We do not introduce the modal-logical characterizations of all equivalences here, but one by one in chapter (ref). However, since the modal-logical characterization of Bisimulation is the entirety of HML formulas, we include \<open>HML_equivalent p q\<close> as the definition of \<open>p\<close> and \<open>q\<close> are bisimilar.\<close>
definition HML_subset_equivalent :: \<open>('a, 's)hml set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>HML_subset_equivalent X p q \<equiv> (\<forall>\<phi> \<in> X. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

definition HML_equivalent :: "'s \<Rightarrow> 's \<Rightarrow> bool" where
  "HML_equivalent p q \<equiv> HML_subset_equivalent {\<phi>. True} p q"

abbreviation distinguishes ::  \<open>('a, 's) hml \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
   \<open>distinguishes \<phi> p q \<equiv> p \<Turnstile> \<phi> \<and> \<not>q \<Turnstile> \<phi>\<close>

text \<open>
For the purposes of this thesis, we consider the modal-logical characterizations, similar to those presented in (van Glaabbeck), as synonymous with the characterization of the equivalences.
\textnormal{X-equivalence} of two processes $p$ and $q$ is denoted by $p \sim_X q$. If they are equivalent for every formula in \textnormal{HML}[\Sigma], they are bisimilar, denoted as $p \sim_B q$.
\<close>

text \<open>Next we show some properties to better talk about these definitions. We show that $\cdot \sim_X \cdot$ is an equivalence relation. 
Also, the equivalence is preserved under transitions, meaning that the X-equivalence is maintained when processes transition to new states.
Finally, we show that if two states are not HML equivalent, there must be a distinguishing formula.\<close>

(*<*)
lemma \<^marker>\<open>tag (proof) visible\<close> subs_equiv_refl: "reflp (HML_subset_equivalent X)"
  using reflpI HML_subset_equivalent_def
  by metis

lemma \<^marker>\<open>tag (proof) visible\<close> subs_equiv_trans: "transp (HML_subset_equivalent X)"
  using HML_subset_equivalent_def transp_def
  by force

lemma \<^marker>\<open>tag (proof) visible\<close> subs_equiv_sym:
  shows "symp (HML_subset_equivalent X)"
  unfolding HML_subset_equivalent_def symp_def 
  by blast
(*>*)

lemma \<open>equivp (HML_subset_equivalent X)\<close>
  using subs_equiv_trans subs_equiv_sym subs_equiv_refl equivpI
  by blast

lemma \<^marker>\<open>tag (proof) visible\<close> equiv_der:
  assumes "HML_equivalent p q" "\<exists>p'. p \<mapsto>\<alpha> p'"
  shows "\<exists>p' q'. (HML_equivalent p' q') \<and> q \<mapsto>\<alpha> q'"
  using assms hml_semantics.simps
  unfolding HML_equivalent_def HML_subset_equivalent_def
  by (metis UNIV_def iso_tuple_UNIV_I)

lemma hml_distinctions:
  fixes state:: 's
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists>\<phi>. distinguishes \<phi> p q\<close>
proof-
  from assms have "\<not> (\<forall> \<phi>::('a, 's) hml. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))" 
    unfolding HML_equivalent_def HML_subset_equivalent_def by blast
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

text \<open>\textit{Example 1.} We can now use HML to capture differences between $p_1$ and $q_1$ of Figure \ref{fig:2_1}. The formula
$\varphi_1 :=\langle a \rangle\bigwedge\{\lnot\langle c \rangle\}$ distinguishes $p_1$ from $q_1$ and $\varphi_2 := \bigwedge\{\lnot\langle a \rangle\bigwedge\{\lnot\langle c \rangle\}\}$ distinguishes
$q_1$ from $p_1$. The Hennessy--Milner Theorem implies that if a distinguishing formula exists, then $p_1$ and $q_1$ cannot be bisimilar.\<close>

end \<comment> \<open>of context lts\<close>

(*<*)
context lts begin
text \<open>Rest im Appendix? Brauche ich formel äquivalenz noch? (Nur für modallogik-relational correspondenz)\<close>

text \<open> An HML formula \<open>\<phi>l\<close> implies another (\<open>\<phi>r\<close>) if the fact that some process \<open>p\<close> satisfies \<open>\<phi>l\<close>
implies that \<open>p\<close> must also satisfy \<open>\<phi>r\<close>, no matter the process \<open>p\<close>. \<close>

definition hml_impl :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Rrightarrow>" 60)  where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"

lemma \<^marker>\<open>tag (proof) visible\<close> hml_impl_iffI: "\<phi>l \<Rrightarrow> \<phi>r = (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"
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
lemma \<^marker>\<open>tag (proof) visible\<close> hml_eq_equiv: "equivp (\<Lleftarrow>\<Rrightarrow>)"
  by (smt (verit, del_insts) equivpI hml_formula_eq_def hml_impl_def reflpI sympI transpI)
end
(*>*)

(*<*)
end
(*>*)