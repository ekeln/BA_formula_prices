theory Transition_Systems
imports Main
begin


(* Zustände: \<open>'s\<close> und Aktionen \<open>'a\<close>, Transitionsrelation ist locale trans. Ein LTS wird dann durch
seine Transitionsrelation definiert.*)
locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<mapsto>_ _" [70, 70, 70] 80)
(*    and S :: \<open>'s set\<close>
    and A :: \<open>'a set\<close> *)
begin

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close>
  where
\<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto>\<alpha> p'}\<close>

abbreviation initial_actions:: \<open>'s \<Rightarrow> 'a set\<close>
  where
\<open>initial_actions p \<equiv> {\<alpha>|\<alpha>. (\<exists>p'. p \<mapsto>\<alpha> p')}\<close>

abbreviation deadlock :: \<open>'s \<Rightarrow> bool\<close> where
\<open>deadlock p \<equiv> (\<forall>a. derivatives p a = {})\<close>

inductive step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$ _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$ [] p\<close> |
\<open>p \<mapsto>$ (a#rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close>

abbreviation traces :: \<open>'s \<Rightarrow> 'a list set\<close> where
\<open>traces p \<equiv> {tr. \<exists>p'. p \<mapsto>$ tr p'}\<close>

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

lemma
  shows \<open>transp (\<lesssim>T)\<close>
  unfolding transp_def trace_preordered_def by blast

text \<open>Failure Pairs\<close>

abbreviation failure_pairs :: \<open>'s \<Rightarrow> ('a list \<times> 'a set)\<close>
  where
\<open>failure_pairs p \<equiv> 
let T = traces p 
xs = (SOME x. x \<in> T) in
(xs, {})\<close>

text \<open>Failure preorder\<close>

(*traces p \<subseteq> traces q \<and> \<forall>p'. (\<exists>A F. p \<mapsto>$ A p' \<and> \<longrightarrow>*)
(*Wenn es für jeden trace von q und für jede Menge aus states, sodass es *)
definition failure_preordered (infix \<open>\<lesssim>F\<close> 60) where
\<open>failure_preordered p q \<equiv> traces p \<subseteq> traces q\<close>

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

(*TODO: relationale definition der anderen äquivalenzen*)


end
end