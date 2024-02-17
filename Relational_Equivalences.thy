(*<*)
theory Relational_Equivalences
  imports Main
"HOL-Library.Countable_Set"
Transition_Systems
begin
(*>*)

context lts
begin
text \<open>Introduce these definitions later?\<close>

abbreviation traces :: \<open>'s \<Rightarrow> 'a list set\<close> where
\<open>traces p \<equiv> {tr. \<exists>p'. p \<mapsto>$ tr p'}\<close>

abbreviation all_traces :: "'a list set" where
"all_traces \<equiv>{tr. \<exists>p p'. p \<mapsto>$ tr p'}"

inductive paths:: \<open>'s \<Rightarrow> 's list \<Rightarrow> 's \<Rightarrow> bool\<close> where
\<open>paths p [] p\<close> |
\<open>paths p (a#as) p''\<close> if "\<exists>\<alpha>. p \<mapsto> \<alpha> a \<and> (paths a as p'')"

lemma path_implies_seq:
  assumes A1: "\<exists>xs. paths p xs p'"
  shows "\<exists>ys. p \<mapsto>$ ys p'"
proof-
  from A1 obtain xs where "paths p xs p'" by auto
  then show "\<exists>ys. p \<mapsto>$ ys p'"
proof (rule local.paths.induct)
  fix q
  have "q \<mapsto>$ [] q" using step_sequence.intros(1).
  then show "\<exists>ys. q \<mapsto>$ ys q" by (rule exI)
next
  fix p a as p''
  assume A1: "\<exists>\<alpha>. p \<mapsto>\<alpha> a \<and> paths a as p'' \<and> (\<exists>ys. a \<mapsto>$ ys p'')"
  then obtain ys \<alpha> where A2: "a \<mapsto>$ ys p''" and A3: "p \<mapsto>\<alpha> a"
    by blast
  then have "p \<mapsto>$ (\<alpha>#ys) p''" using step_sequence.intros(2)
    by blast
  then show "\<exists>ys. p \<mapsto>$ ys p''" by (rule exI)
  qed
qed

lemma seq_implies_path:
  assumes A1: "\<exists>ys. p \<mapsto>$ ys p'"
  shows "\<exists>xs. paths p xs p'"
proof-
  from A1 obtain ys where "p \<mapsto>$ ys p'" by auto
  then show "\<exists>xs. paths p xs p'"
  proof(rule step_sequence.induct)
    fix p
    have "paths p [] p" using paths.intros(1).
    then show "\<exists>xs. paths p xs p" by (rule exI)
  next
    fix p a rt p''
    assume "\<exists>p'. p \<mapsto>a p' \<and> p' \<mapsto>$ rt p'' \<and> (\<exists>xs. paths p' xs p'')"
    then obtain p' xs where "p \<mapsto>a p'" and "paths p' xs p''" by auto
    then have "paths p (p'#xs) p''" using paths.intros(2) by blast
    then show "\<exists>xs. paths p xs p''" by (rule exI)
  qed
qed

text \<open>Trace preorder as inclusion of trace sets\<close>

definition trace_preordered (infix \<open>\<lesssim>T\<close> 60)where
\<open>trace_preordered p q \<equiv> traces p \<subseteq> traces q\<close>

text \<open>Trace equivalence as mutual preorder\<close>

abbreviation trace_equivalent (infix \<open>\<simeq>T\<close> 60) where
\<open>p \<simeq>T q \<equiv> p \<lesssim>T q \<and> q \<lesssim>T p\<close>

text \<open>Trace preorder is transitive\<close>

lemma trace_preorder_transitive:
  shows \<open>transp (\<lesssim>T)\<close>
  unfolding transp_def trace_preordered_def by blast

lemma empty_trace_trivial:
  fixes p
  shows \<open>[] \<in> traces p\<close>
  using step_sequence.intros by blast

lemma \<open>equivp (\<simeq>T)\<close>
proof (rule equivpI)
  show \<open>reflp (\<simeq>T)\<close>
    unfolding reflp_def trace_preordered_def by blast
  show \<open>symp (\<simeq>T)\<close>
    unfolding symp_def by blast
  show \<open>transp (\<simeq>T)\<close>
    unfolding transp_def trace_preordered_def by blast
qed

text \<open>Failure Pairs\<close>

abbreviation failure_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a set) set\<close>
  where
\<open>failure_pairs p \<equiv> {(xs, F)|xs F. \<exists>p'. p \<mapsto>$ xs p' \<and> (initial_actions p' \<inter> F = {})}\<close>

text \<open>Failure preorder and -equivalence\<close>

definition failure_preordered (infix \<open>\<lesssim>F\<close> 60) where
\<open>p \<lesssim>F q \<equiv> failure_pairs p \<subseteq> failure_pairs q\<close>

abbreviation failure_equivalent (infix \<open>\<simeq>F\<close> 60) where
\<open> p \<simeq>F q \<equiv> p \<lesssim>F q \<and> q \<lesssim>F p\<close>

text \<open>Possible future sets\<close>

abbreviation possible_future_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a list set) set\<close>
  where
\<open>possible_future_pairs p \<equiv> {(xs, X)|xs X. \<exists>p'. p \<mapsto>$ xs p' \<and> traces p' = X}\<close>

definition possible_futures_preordered (infix \<open>\<lesssim>PF\<close> 60) where
\<open>p \<lesssim>PF q \<equiv> (possible_future_pairs p \<subseteq> possible_future_pairs q)\<close>

definition possible_futures_equivalent (infix \<open>\<simeq>PF\<close> 60) where
\<open>p \<simeq>PF q \<equiv> (possible_future_pairs p = possible_future_pairs q)\<close>

lemma PF_trans: "transp (\<simeq>PF)"
  unfolding possible_futures_equivalent_def
  by (simp add: transp_def)

lemma pf_implies_trace_preord:
  assumes \<open>p \<lesssim>PF q\<close>
  shows \<open>p \<lesssim>T q\<close>
  using assms unfolding trace_preordered_def
proof safe
  fix p'' tr
  assume \<open>p \<lesssim>PF q\<close> and \<open>p \<mapsto>$ tr p''\<close>
  thus \<open>\<exists>q'. q \<mapsto>$ tr q'\<close>
  proof (induct tr arbitrary: p q)
    case Nil
    show ?case using step_sequence.intros(1) by blast
  next
    case (Cons a tr)
    from Cons have "\<exists>q''. q \<mapsto>$ (a#tr) q''" using Cons(2) 
      unfolding possible_futures_preordered_def 
      by (smt (z3) Collect_mono_iff prod.inject)
    then show ?case 
      by blast
  qed
qed


text \<open>isomorphism\<close>

definition isomorphism :: \<open>('s \<Rightarrow> 's) \<Rightarrow> bool\<close> where
\<open>isomorphism f \<equiv> bij f \<and> (\<forall>p a p'. p \<mapsto> a p' \<longleftrightarrow> f p \<mapsto> a (f p'))\<close>

definition is_isomorphic :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>\<simeq>ISO\<close> 60) where
\<open>p \<simeq>ISO q \<equiv> \<exists>f. isomorphism f \<and> (f p) = q\<close>

text \<open>Two states are simulation preordered if they can be related by
  a simulation relation. (Implied by isometry.)\<close>

definition simulation
  where \<open>simulation R \<equiv>
    \<forall>p q a p'. p \<mapsto> a p' \<and> R p q \<longrightarrow> (\<exists>q'. q \<mapsto> a q' \<and> R p' q')\<close>

definition simulated_by (infix \<open>\<lesssim>S\<close> 60)
  where \<open>p \<lesssim>S q \<equiv> \<exists>R. R p q \<and> simulation R\<close>

text \<open>Simulation preorder implies trace preorder\<close>

lemma sim_implies_trace_preord:
  assumes \<open>p \<lesssim>S q\<close>
  shows \<open>p \<lesssim>T q\<close>
  using assms unfolding trace_preordered_def
proof safe
  fix p'' tr
  assume \<open>p \<lesssim>S q\<close> and \<open>p \<mapsto>$ tr p''\<close>
  thus \<open>\<exists>q'. q \<mapsto>$ tr q'\<close>
  proof (induct tr arbitrary: p q)
    case Nil
    show ?case using step_sequence.intros(1) by blast
  next
    case (Cons a tr)
    obtain p' where \<open>p \<mapsto> a p'\<close> \<open>p' \<mapsto>$ tr p''\<close>
      using Cons.prems(2) step_sequence.simps
      by blast
    obtain q' where \<open>q \<mapsto> a q'\<close> \<open>p' \<lesssim>S q'\<close>
      using Cons.prems(1) \<open>p \<mapsto> a p'\<close> unfolding simulated_by_def simulation_def
      by blast
    obtain q'' where \<open>q' \<mapsto>$ tr q''\<close>
      using Cons.hyps \<open>p' \<lesssim>S q'\<close> \<open>p' \<mapsto>$ tr p''\<close>
      by blast
    then show ?case
      using \<open>q \<mapsto> a q'\<close> step_sequence.intros(2)
      by blast
  qed
qed

text \<open>Two states are bisimilar if they can be related by a symmetric simulation.\<close>

definition bisimilar (infix \<open>\<simeq>B\<close> 80) where
  \<open>p \<simeq>B q \<equiv> \<exists>R. simulation R \<and> symp R \<and> R p q\<close>

text \<open>Bisimilarity is a simulation.\<close>

lemma bisim_sim:
  shows \<open>simulation (\<simeq>B)\<close>
  unfolding bisimilar_def simulation_def by blast


end
end