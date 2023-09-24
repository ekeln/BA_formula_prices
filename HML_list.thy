theory HML_list
  imports
 Main
 Transition_Systems

begin
datatype ('a)formula_list =
HML_conj \<open>('a)formula_list list\<close>  \<open>('a)formula_list list\<close>
| HML_poss \<open>'a\<close> \<open>('a)formula_list\<close>

context lts begin


fun HML_semantics :: \<open>'s \<Rightarrow> ('a)formula_list \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
HML_sem_conj: \<open>(p \<Turnstile> HML_conj \<Phi> \<Psi>) = 
(\<forall>\<phi>. (\<phi> \<in> set \<Phi> \<longrightarrow> HML_semantics p  \<phi>) \<and> (\<phi> \<in> set \<Psi> \<longrightarrow> \<not>(HML_semantics p \<phi>)))\<close>
| HML_sem_poss: \<open>(HML_semantics p (HML_poss \<alpha> \<phi>)) = (\<exists> q. (p \<longmapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close>
end

(*TODO*)
(*Trace equiv: T \<in> trace, wenn \<phi> dann auch <a>\<phi>.*)
(*(\<infinity>, 1, 0, 0, 0, 0)*)
inductive HML_trace :: "('a)formula_list \<Rightarrow> bool"
  where
trace_conj: "HML_trace (HML_conj [] [])"|
trace_pos: "HML_trace (HML_poss \<alpha> \<phi>)" if "HML_trace \<phi>"

inductive HML_failure :: "('a)formula_list \<Rightarrow> bool"
  where
trace: "HML_failure (HML_poss \<alpha> \<phi>)" if "HML_failure \<phi>" |
empty_conj: "HML_failure (HML_conj [] [])" |
neg: "HML_failure (HML_conj [] x2)" if "\<forall>y \<in> (set x2). \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] [])" 

inductive HML_simulation :: "('a)formula_list \<Rightarrow> bool"
  where
sim_pos: "HML_simulation (HML_poss \<alpha> \<phi>)" if "HML_simulation \<phi>"|
sim_conj: "HML_simulation (HML_conj xs [])" if "\<forall>x \<in> (set xs). HML_simulation x"

inductive HML_readiness :: "('a)formula_list \<Rightarrow> bool"
  where
read_pos: "HML_readiness (HML_poss \<alpha> \<phi>)" if "HML_readiness \<phi>"|
read_conj: "HML_readiness (HML_conj xs ys)" 
if "(\<forall>x \<in> set xs. x = HML_poss \<alpha> (HML_conj [] [])) \<and> (\<forall> y \<in> set ys. y = HML_poss \<alpha> (HML_conj [] []))"


inductive HML_failure_trace :: "('a)formula_list \<Rightarrow> bool"
  where
f_trace_pos: "HML_failure_trace (HML_poss \<alpha> \<phi>)" if "HML_failure_trace \<phi>"|
f_trace_e_conj : "HML_failure_trace (HML_conj [] [])" |
f_trace_conj: "HML_failure_trace (HML_conj xs ys)" if "\<exists>x \<in> set xs. (HML_failure_trace x \<and> (\<forall>y. y \<in> set xs \<longrightarrow> y = x))
 \<and> (\<forall> y \<in> set ys. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] [])))"

end