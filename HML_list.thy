(*<*)
theory HML_list
  imports
 Main
 Transition_Systems
 HML

begin
(*>*)
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
revivals_conj: "HML_revivals (hml_conj I J \<Phi>)" if "(\<exists>x \<in> (\<Phi> ` I). (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>) \<and> (\<forall>y \<in> (\<Phi> ` I). x \<noteq> y \<longrightarrow> TT_like y))
\<or> (\<forall>y \<in> (\<Phi> ` I).TT_like y)"
"(\<forall>x \<in> (\<Phi> ` J). TT_like x \<or> (\<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>))"

end