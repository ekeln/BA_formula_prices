(*<*)
theory Transition_Systems
  imports Main
"HOL-Library.Countable_Set"
begin
(*>*)

subsection \<open>Labelled Transition Systems\<close>

text \<open>A Labelled Transition System (LTS) is a tuple S = (P, E, ->) where P is the set of processes, 
E is the set fo actions and -> $\subseteq \Proc \times \Act \times \Proc$ is the transition relation.\\

In concurrency theory it is customary that the semantics of Reactive Systems are given in terms of labelled transition systems.
The processes represent the states a reactive system can be in. A transition of one state into another, 
caused by performing an action, can be understood as moving along the corresponding edge in the transition relation. \\

\\
- Example?
\\

The $\alpha$-derivatives of a process are the processes that can be reached with one $\alpha$-transitions:

- examples (to reuse later?)???
- Definitions (w\o isabelle)?\<close>

subsection \<open>Isabelle\<close>

text \<open>Zustände: \<open>'s\<close> und Aktionen \<open>'a\<close>, Transitionsrelation ist locale trans. Ein LTS wird dann durch
seine Transitionsrelation definiert.\<close>
locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<mapsto>_ _" [70, 70, 70] 80)
begin

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close>
  where
\<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto>\<alpha> p'}\<close>

text \<open>Transition System is image-finite\<close>

definition image_finite where
\<open>image_finite \<equiv> (\<forall>p \<alpha>. finite (derivatives p \<alpha>))\<close>

definition image_countable :: \<open>bool\<close>
  where \<open>image_countable \<equiv> (\<forall> p \<alpha>. countable (derivatives p \<alpha>))\<close>

text \<open>stimmt definition? definition benötigt nach umstieg auf sets?\<close>
definition lts_finite where
\<open>lts_finite \<equiv> (finite (UNIV :: 's set))\<close>

abbreviation initial_actions:: \<open>'s \<Rightarrow> 'a set\<close>
  where
\<open>initial_actions p \<equiv> {\<alpha>|\<alpha>. (\<exists>p'. p \<mapsto>\<alpha> p')}\<close>

abbreviation deadlock :: \<open>'s \<Rightarrow> bool\<close> where
\<open>deadlock p \<equiv> (\<forall>a. derivatives p a = {})\<close>

text \<open>nötig?\<close>
abbreviation relevant_actions :: \<open>'a set\<close>
  where
\<open>relevant_actions \<equiv> {a. \<exists>p p'. p \<mapsto>a p'}\<close>

inductive step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$ _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$ [] p\<close> |
\<open>p \<mapsto>$ (a#rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close>

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

lemma T_trans:
  shows \<open>transp (\<lesssim>T)\<close>
  unfolding transp_def trace_preordered_def by blast

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

abbreviation possible_future_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a list list) set\<close>
  where
\<open>possible_future_pairs p \<equiv> {(xs, X)|xs X. \<exists>p'. p \<mapsto>$ xs p' \<and> traces p' = (set X)}\<close>

definition possible_futures_equivalent (infix \<open>\<simeq>PF\<close> 60) where
\<open>p \<simeq>PF q \<equiv> (possible_future_pairs p = possible_future_pairs q)\<close>

lemma PF_trans: "transp (\<simeq>PF)"
  unfolding possible_futures_equivalent_def
  by (simp add: transp_def)

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

text \<open>Two states are bisimilar if they can be related by a symmetric simulation.\<close>

definition bisimilar (infix \<open>\<simeq>B\<close> 80) where
  \<open>p \<simeq>B q \<equiv> \<exists>R. simulation R \<and> symp R \<and> R p q\<close>

text \<open>Bisimilarity is a simulation.\<close>

lemma bisim_sim:
  shows \<open>simulation (\<simeq>B)\<close>
  unfolding bisimilar_def simulation_def by blast


end
end