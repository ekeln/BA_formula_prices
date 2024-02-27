theory Possible_futures
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

inductive hml_possible_futures :: "('a, 's)hml \<Rightarrow> bool"
  where
pf_tt: "hml_possible_futures TT" |
pf_pos: "hml_possible_futures (hml_pos \<alpha> \<phi>)" if "hml_possible_futures \<phi>" |
pf_conj: "hml_possible_futures (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> ` (I\<union> J)). (hml_trace x)"

definition hml_possible_futures_formulas where
"hml_possible_futures_formulas \<equiv> {\<phi>. hml_possible_futures \<phi>}"

definition expr_possible_futures
  where
"expr_possible_futures = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, 2, \<infinity>, \<infinity>, \<infinity>, 1))}"

context lts
begin

definition expr_possible_futures_equivalent 
  where
"expr_possible_futures_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_possible_futures \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

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