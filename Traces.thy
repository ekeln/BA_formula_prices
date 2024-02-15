theory Traces
imports Main Transition_Systems
begin

context lts
begin

inductive paths :: \<open>'s list \<Rightarrow> bool\<close> where
  \<open>paths [p, p]\<close> |
  \<open>paths (p#p'#ps)\<close> if \<open>\<exists>a. p \<mapsto> a p' \<and> paths (p'#ps)\<close>

lemma
  assumes \<open>paths (p # ps @ [p''])\<close>
  shows \<open>\<exists>tr. p \<mapsto>$ tr p''\<close>
  using assms
proof (induct ps arbitrary: p)
  case Nil
  hence \<open>paths [p, p'']\<close>
    by simp
  hence \<open>p = p''\<close>
    by (metis list.discI list.sel(1) list.sel(3) paths.cases)
  hence \<open>p \<mapsto>$ [] p''\<close>
    using step_sequence.intros(1) by blast
  then show ?case
    by blast
next
  case (Cons p' ps)
  obtain a where \<open>p \<mapsto> a p'\<close> \<open>paths (p' # ps @ [p''])\<close>
    using Cons.prems paths.simps[of \<open>p # (p' # ps) @ [p'']\<close>]
    by auto
  obtain tr where \<open>p' \<mapsto>$ tr p''\<close>
    using Cons.hyps \<open>paths (p' # ps @ [p''])\<close>
    by blast
  then show ?case
    using \<open>p \<mapsto> a p'\<close> step_sequence.intros(2)
    by blast
qed

lemma
  assumes \<open>p \<mapsto>$ tr p''\<close>
  shows \<open>\<exists>ps. paths (p # ps @ [p''])\<close>
  using assms
proof (induct rule:step_sequence.induct)
  case (1 p)
  have \<open>paths (p # [] @ [p])\<close>
    using paths.intros(1)
    by simp
  then show ?case by blast
next
  case (2 p a rt p'')
  then show ?case
    using paths.intros(2) append_Cons
    by metis
qed


abbreviation traces :: \<open>'s \<Rightarrow> 'a list set\<close>
  where \<open>traces p \<equiv> {tr. \<exists>p'. p \<mapsto>$ tr p'}\<close>

lemma empty_trace_trivial:
  fixes p
  shows \<open>[] \<in> traces p\<close>
  using step_sequence.intros by blast

text \<open>Trace preorder as inclusion of trace sets\<close>

definition trace_preordered (infix \<open>\<lesssim>T\<close> 60) where
  \<open>p \<lesssim>T q \<equiv> traces p \<subseteq> traces q\<close>

text \<open>Trace equivalence as mutual preorder\<close>

abbreviation trace_equivalent (infix \<open>\<simeq>T\<close> 60) where
  \<open>p \<simeq>T q \<equiv> p \<lesssim>T q \<and> q \<lesssim>T p\<close>

text \<open>Trace preorder is transitive\<close>
lemma trace_preorder_transitive:
  shows \<open>transp (\<lesssim>T)\<close>
  unfolding transp_def trace_preordered_def by blast

lemma \<open>equivp (\<simeq>T)\<close>
proof (rule equivpI)
  show \<open>reflp (\<simeq>T)\<close>
    unfolding reflp_def trace_preordered_def by blast
  show \<open>symp (\<simeq>T)\<close>
    unfolding symp_def by blast
  show \<open>transp (\<simeq>T)\<close>
    unfolding transp_def trace_preordered_def by blast
qed



end
end