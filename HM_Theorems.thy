theory HM_Theorems
imports Main HML_list HML_equivalences Relational_Equivalences
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
    then show ?case using trace_to_formula.simps Cons
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
  shows "(trace_to_formula t) \<in> HML_trace_formulas"
proof(induction t)
  case Nil
  then show ?case 
    using HML_trace.simps HML_trace_formulas_def trace_to_formula.simps(1) by blast
next
  case (Cons a t)
  then show ?case 
    using HML_trace_formulas_def trace_pos by fastforce
qed

lemma HM_trace_aux_theorem:
  fixes p \<phi>
  assumes "(\<phi> \<in> HML_trace_formulas \<and> (p \<Turnstile> \<phi>))"  
  shows "\<exists>t. t \<in> traces p \<and> (\<phi> \<Lleftarrow>\<Rrightarrow> (trace_to_formula t))"
  using assms
proof(induction \<phi> arbitrary: p)
  case TT
  then show ?case 
    using lts.step_sequence.intros(1) equivp_reflp hml_eq_equiv
    by fastforce
next
  case (hml_pos \<alpha> \<phi>)
  then have \<phi>_trace: "\<phi> \<in> HML_trace_formulas"
    using HML_trace.simps HML_trace_formulas_def 
    by (metis hml.distinct(1) hml.distinct(5) hml.inject(1) mem_Collect_eq)
  from hml_pos obtain q where "p \<mapsto>\<alpha> q \<and> q \<Turnstile> \<phi>"
    by auto
  with hml_pos \<phi>_trace have "\<exists>t. t \<in> traces q \<and> \<phi> \<Lleftarrow>\<Rrightarrow> trace_to_formula t" by blast
  then obtain \<psi> t where "t \<in> traces q" "\<phi> \<Lleftarrow>\<Rrightarrow> trace_to_formula t" "trace_to_formula t = (\<psi>::('a, 's)hml)"
    by blast
  define \<chi> where "\<chi> \<equiv> (hml_pos \<alpha> \<psi>)"
  have "(\<alpha>#t) \<in> traces p" 
    using \<open>p \<mapsto>\<alpha> q \<and> q \<Turnstile> \<phi>\<close> \<open>t \<in> traces q\<close> ttf by auto
  have "trace_to_formula (\<alpha>#t) = \<chi>"
    unfolding \<chi>_def
    by (simp add: \<open>trace_to_formula t = \<psi>\<close>)
  have "hml_pos \<alpha> \<phi> \<Lleftarrow>\<Rrightarrow> \<chi>"
    unfolding hml_formula_eq_def hml_impl_def \<chi>_def
    using \<open>\<phi> \<Lleftarrow>\<Rrightarrow> trace_to_formula t\<close> \<open>trace_to_formula t = \<psi>\<close> lts.hml_formula_eq_def lts.hml_impl_iffI by fastforce
  then show ?case 
    using \<open>\<alpha> # t \<in> traces p\<close> \<open>trace_to_formula (\<alpha> # t) = \<chi>\<close> by blast
next
  case (hml_conj I J \<Phi>)
  hence "I = {}" "J = {}"
    by (metis CollectD HML_trace.simps HML_trace_formulas_def hml.distinct(3) hml.distinct(5) hml.inject(2))+
  then show ?case
    using step_sequence.intros(1) hml_formula_eq_def hml_impl_iffI 
    by fastforce
qed

lemma state_satisfies_trace:
  assumes "t \<in> traces p"
  shows "p \<Turnstile> trace_to_formula t"
  using \<open>t \<in> traces p\<close>
  apply ((induction t arbitrary: p), simp)
  using ttf by blast

text \<open>HM Theorem for Traces\<close>

lemma HM_trace_theorem:
  fixes p q
  shows "(traces p = traces q) = 
HML_trace_equivalent p q"
proof
  assume trace_eq: "traces p = traces q"
  show "HML_trace_equivalent p q"
    unfolding HML_trace_equivalent_def using HM_trace_aux_theorem state_satisfies_trace trace_eq 
    using hml_formula_eq_def hml_impl_iffI by blast
next
  assume assm: "HML_trace_equivalent p q"
  then show "traces p = traces q"
    unfolding HML_trace_equivalent_def using state_satisfies_trace assm ttf ttf_in_HML_trace 
    by blast
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
  case TT
  then show ?case 
    using hml_sem_tt by blast
next
  case (hml_pos x1 \<phi>)
  then show ?case 
    using bisim_sim hml_sem_pos
    unfolding simulation_def 
    by meson
next
  case (hml_conj x1 x2 x3)
  then show ?case using bisimilar_def sympD by fastforce
qed

definition set_to_list :: "'s set \<Rightarrow> 's list"
where \<open>set_to_list s \<equiv> (SOME l. (set l) = s)\<close>

lemma set_to_list_eq:
  assumes \<open>finite s\<close>
  shows \<open>set (set_to_list s) = s\<close>
  unfolding set_to_list_def
  using someI_ex[OF finite_list[OF assms]] .

lemma map_SOME:
  assumes "\<forall>q' \<in> set der_list. \<exists>\<phi>. distinguishes \<phi> p' q'"
  shows "\<forall>\<psi> \<in> set (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list). p' \<Turnstile> \<psi>"
proof-
  define \<psi>_list where "\<psi>_list \<equiv> (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list)"
  then show "\<forall>\<psi> \<in> set \<psi>_list. p' \<Turnstile> \<psi>"
    using assms
  proof(induction \<psi>_list arbitrary: der_list)
    case Nil
    then show ?case
      by fastforce
  next
    case (Cons a \<psi>_tail) 
    have \<psi>_head: "\<exists>\<phi>. distinguishes \<phi> p' (hd der_list)"
      using local.Cons(2, 3) by force
    then have dist: "distinguishes (SOME \<phi>. distinguishes \<phi> p' (hd der_list)) p' (hd der_list)"
      using someI_ex
      by (metis (no_types, lifting))
    from Cons(3) have a_eq: "a = (SOME \<psi>. distinguishes \<psi> p' (hd der_list))"
      using Cons.hyps(2) by force
    with dist have a_dist: "distinguishes a p' (hd der_list)"
      by blast
    from Cons have "\<forall>\<psi>\<in>set \<psi>_tail. p' \<Turnstile> \<psi>"
      by auto
    with a_eq a_dist show ?case
      by simp
  qed
qed

lemma dist_junctor_implies_dist_conjunction:
  assumes "\<forall>q' \<in> set der_list. \<exists>\<phi>. distinguishes \<phi> p' q'"
  shows "(\<forall>q' \<in> set der_list. \<not>q' \<Turnstile> HML_conj (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list) [])"
proof
  fix q'
  assume q'_fix: "q' \<in> set der_list"
  define \<psi>d_list where \<open>\<psi>d_list \<equiv> (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list)\<close>
  then show "(\<not>q' \<Turnstile> HML_conj \<psi>d_list [])"
    using assms q'_fix
  proof(induction der_list arbitrary: \<psi>d_list)
    case Nil
    then show ?case
      by force
  next
    case (Cons a \<psi>d_list)
    from Cons(3) have "q' = a \<or> q' \<in> set \<psi>d_list"
      by auto
    then show ?case
    proof
      assume "q' = a"
      with Cons obtain \<phi> where "distinguishes \<phi> p' q'"
        by fastforce
      thus ?thesis using \<open>q' = a\<close> Cons(2) someI_ex HML_sem_conj
        by (metis (no_types, lifting) list.set_intros(1) list.simps(9))
    next
      assume "q' \<in> set \<psi>d_list"
      with Cons have "\<not> q' \<Turnstile> HML_conj (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') \<psi>d_list) []"
        by simp
      then show ?thesis
        by auto
    qed
  qed
qed

lemma HML_equiv_sim:
  assumes "image_finite"
  shows \<open>simulation HML_equivalent\<close>
  unfolding simulation_def
proof (safe, rule ccontr)
  fix p q a p'
  define der where \<open>der \<equiv> derivatives q a\<close>
  define der_list where \<open>der_list \<equiv> set_to_list der\<close>
  from assms have "finite der" unfolding image_finite_def der_def by simp
  with set_to_list_eq have "\<forall>q' \<in> set der_list. q' \<in> der" unfolding der_list_def der_def set_to_list_def
    by blast
  define \<phi>d_list where \<open>\<phi>d_list \<equiv> map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list\<close>
  define \<phi>d where \<open>\<phi>d \<equiv> HML_poss a (HML_conj \<phi>d_list [])\<close>
  assume contra_assms:
    \<open>p \<mapsto> a p'\<close> \<open>HML_equivalent p q\<close> \<open>\<nexists>q'. q \<mapsto> a q' \<and>  HML_equivalent p' q'\<close>
  hence dist_exists: \<open>\<forall>q' \<in> der. \<exists>\<phi>. distinguishes \<phi> p' q'\<close>
    unfolding der_def using hml_distinctions by simp
  hence dist: "\<forall>q' \<in> set (set_to_list der). \<exists>\<phi>. distinguishes \<phi> p' q'"
    using \<open>\<forall>q'\<in>set der_list. q' \<in> der\<close> der_list_def by blast
  hence "\<forall>\<psi> \<in> set \<phi>d_list. p' \<Turnstile> \<psi>"
    using map_SOME
    unfolding \<phi>d_list_def der_list_def
    by blast
  hence p'_sat: "p' \<Turnstile> (HML_conj \<phi>d_list [])"
    using HML_semantics.simps(1) by simp
  with contra_assms(1) have "p \<Turnstile> \<phi>d" unfolding \<phi>d_def
    using local.HML_sem_poss by blast
  have \<open>(\<forall>q' \<in> der. \<not>q' \<Turnstile> HML_conj \<phi>d_list [])\<close> 
    using dist_junctor_implies_dist_conjunction dist_exists
    unfolding \<phi>d_list_def der_def
    using \<open>finite der\<close> der_def der_list_def set_to_list_eq by blast
  with contra_assms(1) \<open>p' \<Turnstile> HML_conj \<phi>d_list []\<close> have \<open>distinguishes \<phi>d p q\<close>
    unfolding \<phi>d_def der_def by auto
  thus False using contra_assms unfolding HML_equivalent_def by blast
qed

theorem Hennessy_Milner_theorem:
  assumes "image_finite"
  shows
    \<open>HML_equivalent p q = (p \<simeq>B q)\<close>
  using hml_bisim_invariant hml_equiv_sym HML_equiv_sim hml_distinctions
  unfolding bisimilar_def HML_equivalent_def
  using assms by blast

theorem HM_simulation_theorem:
  assumes "image_finite"
  shows "HML_simulation_equivalent p q = (p \<simeq>F q)"
  oops

  section \<open>HM PF Theorem\<close>

lemma 
  assumes "\<phi> \<in> HML_possible_futures_formulas" "p \<simeq>PF q" "p \<Turnstile> \<phi>"
  shows "q \<Turnstile> \<phi>"
  using assms
proof(induction \<phi> arbitrary: p q)
  case (HML_conj x1 x2 p q)
  from this(3) have "\<forall>x1a \<in> set x1. HML_trace x1a"
    using HML_list.HML_possible_futures_formulas_def HML_possible_futures.simps
    by fastforce
  hence "\<forall>x1a \<in> set x1. HML_possible_futures x1a" 
    using HML_possible_futures.simps HML_trace.simps
  then show ?case sorry
next
  case (HML_poss \<alpha> \<psi>)
  then have "\<psi> \<in> HML_possible_futures_formulas"
    using HML_possible_futures_formulas_def HML_possible_futures.simps
    by (metis formula_list.distinct(1) formula_list.inject(2) mem_Collect_eq)
  from HML_poss obtain p' X where "p \<mapsto>\<alpha> p'" "p' \<Turnstile> \<psi>" "traces p' = X"
    using HML_semantics.simps(2)
    by blast
  hence "p \<mapsto>$ [\<alpha>] p'"
    using step_sequence.simps
    by metis 
  obtain q' where "p' \<simeq>PF q'"
    using possible_futures_equivalent_def 
    by blast

  have "q \<mapsto>$ [\<alpha>] q'" using \<open>p \<mapsto>$ [\<alpha>] p'\<close> \<open>p \<simeq>PF q\<close> possible_futures_equivalent_def
    sorry
  have "q \<mapsto>\<alpha> q'" using \<open>p  \<mapsto>\<alpha> p'\<close> \<open>p \<simeq>PF q\<close> possible_futures_equivalent_def sorry
  then obtain q' where "q \<mapsto>$[\<alpha>] q'" "traces q' = X"
    using \<open>p \<simeq>PF q\<close> possible_futures_equivalent_def sorry
    by auto+
  hence "q \<mapsto>\<alpha> q'"
    using step_sequence.simps
    by (metis list.distinct(1) list.sel(1) list.sel(3))
  hence "p' \<simeq>PF q'"
  hence "possible_future_pairs p' = possible_future_pairs q'"
    using \<open>p \<simeq>PF q\<close> \<open>traces p' = X\<close> \<open>traces q' = X\<close> \<open>p  \<mapsto>\<alpha> p'\<close> 
    unfolding possible_futures_equivalent_def 
  then have "p' \<simeq>PF q'" sorry
    using \<open>p \<simeq>PF q\<close> possible_futures_equivalent_def \<open>traces p' = X\<close> \<open>traces q' = X\<close> \<open>p  \<mapsto>\<alpha> p'\<close> 
      step_sequence.simps PF_trans
  from \<open>p  \<mapsto>\<alpha> p'\<close> HML_poss obtain q' where "p' \<simeq>PF q'" 
    using possible_futures_equivalent_def by blast
  with HML_poss \<open>p' \<Turnstile> \<psi>\<close> \<open>\<psi> \<in> HML_possible_futures_formulas\<close> have "q' \<Turnstile> \<psi>"
    by blast
  then show ?case 
    using possible_futures_equivalent_def sorry
qed
  oops

(*TODO*)
fun pf_pair_to_formula where
"pf_pair_to_formula ([], X) = HML_conj [] []" |
"pf_pair_to_formula ((a#tail), X) = HML_poss a (pf_pair_to_formula (tail, X))"

theorem pf_auxillary:
  assumes "image_finite" "\<phi> \<in> HML_possible_futures_formulas" "p \<Turnstile> \<phi>"
  shows "\<exists>t X. (t, X) \<in> possible_future_pairs p \<and> p \<Turnstile> pf_pair_to_formula (t, X)"
  oops

theorem HM_possible_futures_theorem:
  assumes "image_finite"
  shows "HML_possible_futures_equivalent p q = (p \<simeq>PF q)"
  oops

end
end