theory Failure_traces
  imports Failures Transition_Systems HML formula_prices_list
begin

subsection \<open>Failure trace semantics\<close>

text \<open>We can imagine the observer not only observing all traces of a system but also identifying scenarios where specific behavior is not possible. 
For Failures in particular, the observer can distinguish between step-sequences based on what actions are possible in the resulting state. 
Another way to think about Failures is that the process autonomously chooses an execution path, but only using a set of free are allowed actions.
We want the failure formulas to represent either a trace (of the form $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\textsf{T}$)
or a failure pair, where some set of actions is not possible (so $\langle a_1 \rangle\langle a_2\rangle...\langle a_n \rangle\bigwedge \Phi$ with $$)\<close>

text \<open>\textbf{Definition} The language $\mathcal{O}_F$ of failure-formulas is defined recursively:
$$\langle a \rangle \varphi if \varphi \in \mathcal[O}_F | \bigwedge_{i\inI}\lnot\langle a \rangle \textsf{T}$$\<close>

inductive hml_failure_trace :: "('a, 's)hml \<Rightarrow> bool" where
"hml_failure_trace TT" |
"hml_failure_trace (hml_pos \<alpha> \<phi>)" if "hml_failure_trace \<phi>" |
"hml_failure_trace (hml_conj I J \<Phi>)" 
  if "(\<Phi> ` I) = {} \<or> (\<exists>i \<in> \<Phi> ` I. \<Phi> ` I = {i} \<and> hml_failure_trace i)"
     "\<forall>j \<in> \<Phi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT) \<or> j = TT" 

definition hml_failure_trace_formulas
  where
"hml_failure_trace_formulas \<equiv> {\<phi>. hml_failure_trace \<phi>}"

definition expr_failure_trace
  where
"expr_failure_trace = {\<phi>. (less_eq_t (expr \<phi>) (\<infinity>, \<infinity>, \<infinity>, 0, 1, 1))}"

context lts
begin

definition expr_failure_trace_equivalent 
  where
"expr_failure_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> expr_failure_trace \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

end
end