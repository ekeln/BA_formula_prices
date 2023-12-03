theory HM_Theorems
imports Main HML_list
begin

context lts
begin

section \<open>Hennessy-Milner Theorem of the Trace Modal Logic subset and Trace-equivalence\<close>

text \<open>HM-trace Theorem should follow from this:\<close>

lemma ttf:
  fixes p t
  shows "t \<in> traces p = (p \<Turnstile> trace_to_formula t)"
proof
  define \<phi> where "\<phi> = trace_to_formula t"
  assume "t \<in> traces p"
  show "p \<Turnstile> trace_to_formula t"
    using \<open>t \<in> traces p\<close>
  proof(induction t arbitrary: p)
    case Nil
    then show ?case by simp
  next
    case (Cons a t)
    from Cons obtain p'' p' where "p'' \<mapsto>$ t p'" "p \<mapsto>a p''" 
      using step_sequence.simps list.distinct(1) list.sel(1) list.sel(3)
      by (smt (verit) mem_Collect_eq)
    then show ?case using trace_to_formula.simps HML_semantics.cases Cons
      by fastforce
    qed
next
  assume "p \<Turnstile> trace_to_formula t"
  show "t \<in> traces p"
    using \<open>p \<Turnstile> trace_to_formula t\<close>
  proof(induction t arbitrary: p)
    case Nil
    then show ?case 
      using step_sequence.intros(1) by fastforce
  next
    case (Cons a t)
    from Cons obtain p' where p'sat: "p \<mapsto>a p'" "p' \<Turnstile> (trace_to_formula t)" by auto
    with Cons(1) have "t \<in> traces p'" by simp
    with \<open>p \<mapsto>a p'\<close> show ?case
      using step_sequence.intros(2) by fastforce
  qed
qed

lemma ttf_in_HML_trace:
  fixes t
  shows "(trace_to_formula t) \<in> HML_trace_formulas"
 proof(induction t)
  case Nil
  then show ?case 
    by (simp add: HML_trace_formulas_def trace_conj)
next
  case (Cons a t)
  then show ?case
    by (simp add: HML_trace_formulas_def trace_pos)
qed

lemma HM_trace_aux_theorem:
  fixes p \<phi>
  assumes "(\<phi> \<in> HML_trace_formulas \<and> (p \<Turnstile> \<phi>))"  
  shows "\<exists>t. t \<in> traces p \<and> (\<phi> = (trace_to_formula t))"
  using assms
proof(induction \<phi> arbitrary: p)
  case (HML_conj x1 x2)
  then have "x1 = [] \<and> x2 = []"
    using HML_trace.simps HML_trace_formulas_def formula_list.simps(4) by blast
  then show ?case
    using step_sequence.intros(1) by fastforce
next
  case (HML_poss \<alpha> \<phi>)  
  then have \<phi>_trace: "\<phi> \<in> HML_trace_formulas"
    using HML_trace.simps HML_trace_formulas_def by fastforce
  from HML_poss HML_sem_poss obtain q where "p \<mapsto>\<alpha> q \<and> q \<Turnstile> \<phi>"
    by blast
  with HML_poss \<phi>_trace have "\<exists>t. t \<in> traces q \<and> \<phi> = trace_to_formula t" by blast
  then show ?case 
    using \<open>p \<mapsto>\<alpha> q \<and> q \<Turnstile> \<phi>\<close> step_sequence.intros(2) by fastforce
qed

lemma state_satisfies_trace:
  fixes p t
  assumes "t \<in> traces p"
  shows "p \<Turnstile> trace_to_formula t"
  using \<open>t \<in> traces p\<close>
proof(induction t arbitrary: p)
  case Nil
  then show ?case
    by simp
next
  case (Cons a t)
  with trace_to_formula.simps(2) show ?case
    by (smt (verit, best) formula_list.distinct(1) list.inject local.HML_sem_poss mem_Collect_eq step_sequence.cases trace_to_formula.simps(1))
qed

text \<open>HM Theorem for Traces\<close>

lemma HM_trace_theorem:
  fixes p q
  shows "(traces p = traces q) = 
(\<forall>\<phi>. \<phi> \<in> HML_trace_formulas \<longrightarrow> (p \<Turnstile> \<phi> \<longleftrightarrow> q \<Turnstile> \<phi>))"
proof
  assume trace_eq: "traces p = traces q"
  show "\<forall>\<phi>. \<phi> \<in> HML_trace_formulas \<longrightarrow> (p \<Turnstile> \<phi>) = (q \<Turnstile> \<phi>)"
    using HM_trace_aux_theorem state_satisfies_trace trace_eq by blast
next
  assume assm: "(\<forall>\<phi>. \<phi> \<in> HML_trace_formulas \<longrightarrow> (p \<Turnstile> \<phi> \<longleftrightarrow> q \<Turnstile> \<phi>))"
  show "traces p = traces q"
    using state_satisfies_trace assm ttf ttf_in_HML_trace by blast
qed

section \<open>Hennessy–Milner Theorem of Modal Logic an Bisimilarity\<close>

lemma hml_bisim_invariant:
  assumes
    \<open>p \<simeq>B q\<close>
    \<open>p \<Turnstile> \<phi>\<close>
  shows
    \<open>q \<Turnstile> \<phi>\<close>
  using assms
proof (induct \<phi> arbitrary: p q)
  case (HML_conj x1 x2)
  then show ?case 
    using bisimilar_def sympD by fastforce
next
  case (HML_poss x1 \<phi>)
  then show ?case using simulation_def
    by (metis bisim_sim local.HML_sem_poss)
qed

lemma HML_equiv_sim:
  assumes "image_finite"
  shows \<open>simulation HML_equivalent\<close>
  unfolding simulation_def
proof (safe, rule ccontr)
  fix p q a p'
define \<phi>d_set where
  \<open>\<phi>d_set \<equiv> {SOME \<psi>. distinguishes \<psi> p' q' | q'. q' \<in> derivatives q a}\<close>
  from assms have "finite (derivatives q a)" unfolding image_finite_def
    by blast
  then have "finite \<phi>d_set" unfolding \<phi>d_set_def
    by simp
  define \<phi>d where
\<open>\<phi>d \<equiv> HML_poss a (HML_conj [] [])\<close>
    \<open>\<phi>d \<equiv> HML_conj (derivatives q a) (\<lambda>q'. SOME \<phi>. distinguishes \<phi> p' q')\<close>
  assume contra_assms:
    \<open>p \<mapsto> a p'\<close> \<open>HML_equivalent p q\<close> \<open>\<nexists>q'. q \<mapsto> a q' \<and>  HML_equivalent p' q'\<close>
  hence \<open>\<forall>q' \<in> derivatives q a. \<exists>\<phi>. distinguishes \<phi> p' q'\<close>
    using hml_distinctions by simp
  hence \<open>p' \<Turnstile> \<phi>d \<and> (\<forall>q' \<in> derivatives q a. \<not>q' \<Turnstile> \<phi>d)\<close>
    unfolding \<phi>d_def by auto (smt (verit, best) someI2_ex)+
  with contra_assms(1) have \<open>distinguishes (\<langle>a\<rangle>\<phi>d) p q\<close> by auto
  thus False using contra_assms unfolding HML_equivalent_def by blast
qed

theorem Hennessy_Milner_theorem:
  shows
    \<open>HML_equivalent p q = (p \<simeq>B q)\<close>
  using hml_bisim_invariant hml_equiv_sym HML_equiv_sim hml_distinctions
  unfolding bisimilar_def HML_equivalent_def by blast



end
end