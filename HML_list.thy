theory HML_list
  imports
 Main
 Transition_Systems

begin
datatype ('a, 'i)hml =
TT |
hml_pos \<open>'a\<close> \<open>('a, 'i)hml\<close> |
hml_conj "'i set" "'i \<Rightarrow> ('a, 'i) hml" "'i set" "'i \<Rightarrow> ('a, 'i) hml" 


context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I \<psi>s J n\<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i)) \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (n\<psi>s j))))\<close>


text \<open>Two states are HML equivalent if they satisfy the same formula.\<close>
definition HML_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>HML_equivalent p q \<equiv> (\<forall> \<phi>::('a, 's) hml. (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))\<close>

lemma equiv_der:
  assumes "HML_equivalent p q" "\<exists>p'. p \<mapsto>\<alpha> p'"
  shows "\<exists>p' q'. (HML_equivalent p' q') \<and> q \<mapsto>\<alpha> q'"
  using assms hml_semantics.simps
  unfolding HML_equivalent_def 
  by metis


text \<open>HML_equivalency is transitive\<close>
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
                          ((\<lambda>x. undefined):: 's \<Rightarrow> ('a, 's) hml) 
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
trace_conj: "HML_trace (hml_conj {} \<psi>s {} n\<psi>s)"|
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
failure_conj: "HML_failure (hml_conj I \<psi>s J n\<psi>s)" 
if "(\<psi>s ` I = {}) \<and> (\<forall>j \<in> J. \<exists>\<alpha>. ((n\<psi>s j) = hml_pos \<alpha> TT \<or> 
                                  (\<exists>K \<chi>s L n\<chi>s. (\<chi>s ` K = {}) \<and> (n\<chi>s ` L = {}) \<and> 
                                                  (n\<psi>s j) = hml_pos \<alpha> (hml_conj K \<chi>s L n\<chi>s))))" 

inductive HML_simulation :: "('a, 's)hml \<Rightarrow> bool"
  where
sim_tt: "HML_simulation TT" |
sim_pos: "HML_simulation (hml_pos \<alpha> \<phi>)" if "HML_simulation \<phi>"|
sim_conj: "HML_simulation (hml_conj I \<psi>s J n\<psi>s) " if "(\<forall>x \<in> (\<psi>s ` I). HML_simulation x) \<and> (n\<psi>s ` J = {})"

definition HML_simulation_formulas where
"HML_simulation_formulas \<equiv> {\<phi>. HML_simulation \<phi>}"

(*

inductive HML_readiness :: "('a, 's)hml \<Rightarrow> bool"
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

definition HML_possible_futures_formulas where
"HML_possible_futures_formulas \<equiv> {\<phi>. HML_possible_futures \<phi>}"

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
*)
end