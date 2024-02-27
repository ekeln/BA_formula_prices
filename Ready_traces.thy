theory Ready_traces
imports Transition_Systems HML formula_prices_list
begin

subsection \<open>Failures semantics\<close>

text \<open>We can imagine the observer not only observing all traces of a system but also identifying scenarios where specific behavior is not possible. 
For Failures in particular, the observer can distinguish between step-sequences based on what actions are possible in the resulting state. 
Another way to think about Failures is that the process autonomously chooses an execution path, but only using a set of free are allowed actions.
We want the failure formulas to represent either a trace (of the form $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\textsf{T}$)
or a failure pair, where some set of actions is not possible (so $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\bigwedge \Phi$ with $$)\<close>

text \<open>\textbf{Definition} The language $\mathcal{O}_F$ of failure-formulas is defined recursively:
$$\langle a \rangle \varphi if \varphi \in \mathcal[O}_F | \bigwedge_{i\inI}\lnot\langle a \rangle \textsf{T}$$\<close>

inductive hml_readiness :: "('a, 's)hml \<Rightarrow> bool"
  where
read_tt: "hml_readiness TT" |
read_pos: "hml_readiness (hml_pos \<alpha> \<phi>)" if "hml_readiness \<phi>"|
read_conj: "hml_readiness (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> ` (I \<union> J)). (\<exists>\<alpha>. x = (hml_pos \<alpha> TT::('a, 's)hml)) \<or> x = TT"

definition hml_readiness_formulas
  where
"hml_readiness_formulas \<equiv> {\<phi>. hml_readiness \<phi>}"

definition expr_readiness
  where
"expr_readiness = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, 1, 1, 1, 1))}"

context lts
begin

definition expr_readiness_equivalent 
  where
"expr_readiness_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_readiness \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

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