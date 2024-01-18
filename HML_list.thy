theory HML_list
  imports
 Main
 Transition_Systems

begin
datatype ('a, 'i)hml =
TT |
hml_pos \<open>'a\<close> \<open>('a, 'i)hml\<close> |
hml_conj "'i set" "'i set" "'i \<Rightarrow> ('a, 'i) hml" 

inductive TT_like :: "('a, 'i) hml \<Rightarrow> bool"
  where
"TT_like TT" |
"TT_like (hml_conj I J \<Phi>)" if "(\<Phi> `I) = {}" "(\<Phi> ` J) = {}"

inductive nested_empty_pos_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where
"nested_empty_pos_conj TT" |
"nested_empty_pos_conj (hml_conj I J \<Phi>)" 
if "\<forall>x \<in> (\<Phi> `I). nested_empty_pos_conj x" "(\<Phi> ` J) = {}"

inductive nested_empty_conj :: "('a, 'i) hml \<Rightarrow> bool"
  where
"nested_empty_conj TT" |
"nested_empty_conj (hml_conj I J \<Phi>)"
if "\<forall>x \<in> (\<Phi> `I). nested_empty_conj x" "\<forall>x \<in> (\<Phi> `J). nested_empty_pos_conj x"

(*sanity check: nested_empty_conj ist equiv zu TT oder zu FF (nie true)*)

(*stack of Conjunctions, with hml_pos \<alpha> in the deepest one, for failure_trace ff.*)

inductive stacked_pos_conj_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"stacked_pos_conj_pos TT" |
"stacked_pos_conj_pos (hml_pos _ \<psi>)" if "nested_empty_pos_conj \<psi>" |
"stacked_pos_conj_pos (hml_conj I J \<Phi>)"
if "((\<exists>\<phi> \<in> (\<Phi> ` I). ((stacked_pos_conj_pos \<phi>) \<and> 
                     (\<forall>\<psi> \<in> (\<Phi> ` I). \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>))) \<or>
   (\<forall>\<psi> \<in> (\<Phi> ` I). nested_empty_pos_conj \<psi>))"
"(\<Phi> ` J) = {}"

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


inductive single_pos :: "('a, 'i) hml \<Rightarrow> bool"
  where
"single_pos TT" |
"single_pos (hml_pos _ \<psi>)" if "nested_empty_conj \<psi>" |
"single_pos (hml_conj I J \<Phi>)"
if "\<forall>\<phi> \<in> (\<Phi> ` (I \<union> J)). (single_pos \<phi>)"

(*primrec flatten*)
primrec flatten :: "('a, 'i) hml \<Rightarrow> ('a, 'i) hml" where
"flatten TT = TT" |
"flatten (hml_pos \<alpha> \<psi>) = (hml_pos \<alpha> (flatten \<psi>))" |
"flatten (hml_conj I J \<Phi>) = (hml_conj I J \<Phi>)"
(*|
"flatten (hml_conj I J \<Phi>) = (hml_conj I J 
                              (\<lambda>x. if x \<in> I then (if \<exists>\<alpha> \<psi>. (\<Phi> x) = hml_pos \<alpha> \<psi> 
                                                    then (hml_pos \<alpha> (flatten \<psi>)) 
                                                  else )
                                    else TT))"
TODO: wenn \<Phi> geändert werden soll müssen auch I und J geändert werden? Also zb \<And>\<And>{a} {b}
auf ... abbilde ändert auch I und J 
*)

(* (\<forall>x \<in> (\<Phi> ` I). ((\<exists>\<alpha> \<psi>. x = (hml_pos \<alpha> \<psi>) \<longrightarrow> flatten \<psi>)))"*)


(*benötigt?*)
inductive flattened :: "('a, 'i) hml \<Rightarrow> bool"
  where
"flattened TT" |
"flattened (hml_pos _ \<psi>)" if "flattened \<psi>"|
"flattened (hml_conj I J \<Phi>)"
if "\<forall>x \<in> (\<Phi> ` I). flattened x \<and> (\<exists>\<alpha> \<psi>. x = (hml_pos \<alpha> \<psi>))"
"\<forall>y \<in> (\<Phi> ` J). flattened y"

(*sanity checks?*)
(*f.a. \<phi> gibt es \<psi> mit flattened \<psi> und \<phi> \<equiv> \<psi>*)

context lts begin

primrec hml_semantics :: \<open>'s \<Rightarrow> ('a, 's)hml \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
where
hml_sem_tt: \<open>(_ \<Turnstile> TT) = True\<close> |
hml_sem_pos: \<open>(p \<Turnstile> (hml_pos \<alpha> \<phi>)) = (\<exists> q. (p \<mapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> |
hml_sem_conj: \<open>(p \<Turnstile> (hml_conj I J \<psi>s)) = ((\<forall>i \<in> I. p \<Turnstile> (\<psi>s i)) \<and> (\<forall>j \<in> J. \<not>(p \<Turnstile> (\<psi>s j))))\<close>

lemma 
  assumes "TT_like \<phi>"
  shows "p \<Turnstile> \<phi>"
  using assms
  apply (induction \<phi> rule: TT_like.induct)
  by simp+

lemma
  assumes "nested_empty_pos_conj \<phi>"
  shows "p \<Turnstile> \<phi>"
  using assms
  apply (induction \<phi> rule: nested_empty_pos_conj.induct)
  by (simp, force)

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
trace_conj: "HML_trace (hml_conj {} {} \<psi>s)"|
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
failure_conj: "HML_failure (hml_conj I J \<psi>s)" 
if "(\<forall>i \<in> I. TT_like (\<psi>s i)) \<and> (\<forall>j \<in> J. (TT_like (\<psi>s j)) \<or> (\<exists>\<alpha> \<chi>. ((\<psi>s j) = hml_pos \<alpha> \<chi> \<and> (TT_like \<chi>))))" 

inductive HML_simulation :: "('a, 's)hml \<Rightarrow> bool"
  where
sim_tt: "HML_simulation TT" |
sim_pos: "HML_simulation (hml_pos \<alpha> \<phi>)" if "HML_simulation \<phi>"|
sim_conj: "HML_simulation (hml_conj I J \<psi>s) " 
if "(\<forall>x \<in> (\<psi>s ` I). HML_simulation x) \<and> (\<psi>s ` J = {})"

definition HML_simulation_formulas where
"HML_simulation_formulas \<equiv> {\<phi>. HML_simulation \<phi>}"

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
"(\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj y)"

inductive HML_ready_sim :: "('a, 's) hml \<Rightarrow> bool"
  where
"HML_ready_sim TT" |
"HML_ready_sim (hml_pos \<alpha> \<phi>)" if "HML_ready_sim \<phi>" |
"HML_ready_sim (hml_conj I J \<Phi>)" if 
"(\<forall>x \<in> (\<Phi> ` I). HML_ready_sim x) \<and> (\<forall>y \<in> (\<Phi> ` J). stacked_pos_conj_J_empty y)"

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
revivals_conj: "HML_revivals (hml_conj I J \<Phi>)" if "(\<forall>x \<in> (\<Phi> ` I). \<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>)"
"(\<forall>x \<in> (\<Phi> ` J). \<exists>\<alpha> \<chi>. (x = hml_pos \<alpha> \<chi>) \<and> TT_like \<chi>)"

end