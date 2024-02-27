(*<*)
theory Relational_Equivalences
  imports Main
"HOL-Library.Stream"
Transition_Systems
Traces
begin
(*>*)

context lts
begin
text \<open>Introduce these definitions later?\<close>

abbreviation all_traces :: "'a list set" where
"all_traces \<equiv>{tr. \<exists>p p'. p \<mapsto>$ tr p'}"



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