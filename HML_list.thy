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
| HML_sem_poss: \<open>(HML_semantics p (HML_poss \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close>

find_theorems HML_semantics

text \<open>Two states are HML equivalent if they satisfy the same formula.\<close>
definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>HML_equivalent p q \<equiv> (\<forall> \<phi>::('a) formula_list. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

text \<open>
  A formula distinguishes one state from another if its true for the
  first and false for the second.
\<close>
abbreviation distinguishes ::  \<open>('a) formula_list \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool\<close> where
   \<open>distinguishes \<phi> p q \<equiv> p \<Turnstile> \<phi> \<and> \<not> q \<Turnstile> \<phi>\<close>

lemma hml_equiv_sym:
  shows \<open>symp HML_equivalent\<close>
unfolding HML_equivalent_def symp_def by simp

text \<open>
  If two states are not HML equivalent then there must be a
  distinguishing formula.
\<close>
lemma hml_distinctions:
  assumes \<open>\<not> HML_equivalent p q\<close>
  shows \<open>\<exists>\<phi>. distinguishes \<phi> p q\<close>
proof-
  from assms have "\<not> (\<forall> \<phi>::('a) formula_list. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))" 
    unfolding HML_equivalent_def by blast
  then obtain \<phi>::"('a) formula_list" where "(p \<Turnstile> \<phi>) \<noteq> (q \<Turnstile> \<phi>)" by blast
  then have "((p \<Turnstile> \<phi>) \<and> \<not>(q \<Turnstile> \<phi>)) \<or> (\<not>(p \<Turnstile> \<phi>) \<and> (q \<Turnstile> \<phi>))"
    by blast
  then show ?thesis
  proof
    show "distinguishes \<phi> p q \<Longrightarrow> \<exists>\<phi>. distinguishes \<phi> p q" by blast
  next
    assume assm: "\<not> p \<Turnstile> \<phi> \<and> q \<Turnstile> \<phi>"
    show "\<exists>\<phi>. distinguishes \<phi> p q"
    proof
      from assm show "(p \<Turnstile> (HML_conj [] [\<phi>])) \<and> \<not> q \<Turnstile>(HML_conj [] [\<phi>])" using HML_semantics.simps
        by simp
    qed
  qed
qed

end

(*Trace equiv: T \<in> trace, wenn \<phi> dann auch <a>\<phi>.*)
(*(\<infinity>, 1, 0, 0, 0, 0)*)
inductive HML_trace :: "('a)formula_list \<Rightarrow> bool"
  where
trace_conj: "HML_trace (HML_conj [] [])"|
trace_pos: "HML_trace (HML_poss \<alpha> \<phi>)" if "HML_trace \<phi>"

definition HML_trace_formulas where
"HML_trace_formulas \<equiv> {\<phi>. HML_trace \<phi>}"

text \<open>translation of a trace to a formula\<close>

fun trace_to_formula :: "'a list \<Rightarrow> ('a)formula_list"
  where
"trace_to_formula [] = HML_conj [] []" |
"trace_to_formula (a#xs) = HML_poss a (trace_to_formula xs)"

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
if "(\<forall>x \<in> set xs. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] [])) \<and> (\<forall> y \<in> set ys. \<exists>\<alpha>. y = HML_poss \<alpha> (HML_conj [] []))"

inductive HML_impossible_futures :: "('a)formula_list \<Rightarrow> bool"
  where
  if_pos: "HML_impossible_futures (HML_poss \<alpha> \<phi>)" if "HML_impossible_futures \<phi>" |
if_conj: "HML_impossible_futures (HML_conj ([]:: 'a formula_list list) ys)"
if "\<forall>x \<in> set ys. (HML_trace x)"

inductive HML_possible_futures :: "('a)formula_list \<Rightarrow> bool"
  where
pf_pos: "HML_possible_futures (HML_poss \<alpha> \<phi>)" if "HML_possible_futures \<phi>" |
pf_conj: "HML_possible_futures (HML_conj xs ys)" if "(\<forall>x \<in> set xs. (HML_trace x)) \<and> (\<forall>y \<in> set ys. (HML_trace y))"

inductive HML_failure_trace :: "('a)formula_list \<Rightarrow> bool"
  where
f_trace_pos: "HML_failure_trace (HML_poss \<alpha> \<phi>)" if "HML_failure_trace \<phi>"|
f_trace_conj: "HML_failure_trace (HML_conj xs ys)" 
if "(xs = [] \<or> (\<exists>x xs2. xs = (x#xs2) \<and> (HML_failure_trace x \<and> (\<forall>y \<in> set xs2. y = x)))) \<and> 
(\<forall>y \<in> set ys. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] [])))"

inductive HML_ready_trace :: "('a)formula_list \<Rightarrow> bool"
where
r_trace_pos: "HML_ready_trace (HML_poss \<alpha> \<phi>)" if "HML_ready_trace \<phi>"|
r_trace_conj: "HML_ready_trace (HML_conj xs ys)" 
if "(\<forall>x \<in> set xs. \<forall>y \<in> set xs. (\<exists>\<alpha> \<beta>. x \<noteq> HML_poss \<alpha> (HML_conj [] []) \<and> y \<noteq> HML_poss \<beta> (HML_conj [] [])) \<longrightarrow> (x = y \<and> HML_ready_trace x))
\<and> (\<forall>y \<in> set ys. \<exists>\<alpha>. (y = HML_poss \<alpha> (HML_conj [] [])))"

inductive HML_ready_sim :: "('a) formula_list \<Rightarrow> bool"
  where
"HML_ready_sim (HML_poss \<alpha> \<phi>)" if "HML_ready_sim \<phi>" |
"HML_ready_sim (HML_conj xs ys)" if 
"(\<forall>x \<in> set xs. HML_ready_sim x) \<and> (\<forall>y \<in> set ys. \<exists>\<alpha>. y = (HML_poss \<alpha> (HML_conj [] [])))" 

inductive HML_2_nested_sim :: "('a) formula_list \<Rightarrow> bool" 
  where
"HML_2_nested_sim (HML_poss \<alpha> \<phi>)" if "HML_2_nested_sim \<phi>" |
"HML_2_nested_sim (HML_conj xs ys)" if "(\<forall>x \<in> set xs. HML_2_nested_sim x) \<and> (\<forall>y \<in> set ys. HML_simulation y)"

(*TODO: überprüfen*)
inductive HML_revivals :: "('a) formula_list \<Rightarrow> bool" 
  where
revivals_pos: "HML_revivals (HML_poss \<alpha> \<phi>)" if "HML_revivals \<phi>" |
revivals_conj: "HML_revivals (HML_conj xs ys)" if "\<exists>\<alpha>. \<forall>x \<in> set xs. x = HML_poss \<alpha> (HML_conj [] []) \<and>
(\<forall>x \<in> set ys. \<exists>\<alpha>. x = HML_poss \<alpha> (HML_conj [] []))"

end