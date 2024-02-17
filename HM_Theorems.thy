theory HM_Theorems
imports Main HML_list HML_equivalences Relational_Equivalences HML_definitions
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
    by simp
next
  case (hml_pos \<alpha> \<phi>)
  then obtain p' q' where \<open>p \<mapsto> \<alpha> p'\<close> \<open>p' \<Turnstile> \<phi>\<close> \<open>q \<mapsto> \<alpha> q'\<close> \<open>p' \<simeq>B q'\<close>
    using bisim_sim unfolding simulation_def
    by (meson hml_sem_pos)
  with hml_pos show ?case 
    using hml_sem_pos by blast
next
  case (hml_conj x1 x2 x3) 
  then show ?case 
    using bisimilar_def sympD by fastforce
qed

lemma HML_equiv_sim:
  \<open>simulation HML_equivalent\<close>
  unfolding simulation_def
proof (safe, rule ccontr)
  fix p q a p'
  define der_q where "der_q \<equiv> (derivatives q a)"
  define \<phi>d where
    \<open>\<phi>d \<equiv> hml_conj der_q {} (\<lambda>q'. (if q' \<in> der_q then SOME \<phi>. distinguishes \<phi> p' q' else undefined))\<close>
  assume contra_assms:
    \<open>p \<mapsto> a p'\<close> \<open>HML_equivalent p q\<close> \<open>\<nexists>q'. q \<mapsto> a q' \<and>  HML_equivalent p' q'\<close>
  hence \<open>\<forall>q' \<in> derivatives q a. \<exists>\<phi>. distinguishes \<phi> p' q'\<close>
    using hml_distinctions by simp
  hence \<open>p' \<Turnstile> \<phi>d \<and> (\<forall>q' \<in> derivatives q a. \<not>q' \<Turnstile> \<phi>d)\<close>
    unfolding \<phi>d_def der_q_def by auto (smt (verit, best) someI2_ex)+
  with contra_assms(1) have \<open>distinguishes (hml_pos a \<phi>d) p q\<close> by auto
  thus False using contra_assms unfolding HML_equivalent_def by blast
qed

theorem Hennessy_Milner_theorem:
  shows
    \<open>HML_equivalent p q = (p \<simeq>B q)\<close>
  using hml_bisim_invariant hml_equiv_sym HML_equiv_sim hml_distinctions
  unfolding bisimilar_def HML_equivalent_def by blast

theorem HM_simulation_theorem:
  shows "HML_simulation_equivalent p q = (p \<simeq>F q)"
  using HML_equiv_sim
  unfolding HML_simulation_formulas_def HML_simulation_equivalent_def HML_equivalent_def failure_preordered_def
  oops

  section \<open>HM PF Theorem\<close>

lemma trace_formula_is_pf_formula:
  assumes "hml_trace \<phi>"
  shows "hml_possible_futures \<phi>"
  using assms hml_possible_futures.pf_tt hml_possible_futures.simps
by((induction \<phi> rule: hml_trace.induct), blast+)

lemma step_seq: "p \<mapsto>$ (a#xs) p' \<longleftrightarrow> (\<exists>p''. p \<mapsto> a p'' \<and> p'' \<mapsto>$ xs p')"
  using step_sequence.cases step_sequence.intros
  by fastforce

lemma replace_ex: 
  fixes p
  assumes "(\<exists>p. P p) \<longleftrightarrow> (\<exists>q. Q q)" "P p"
  shows "P p \<longleftrightarrow> (\<exists>q. Q q)" 
  using assms(1) assms(2) by blast

lemma pf_trace_shortening:
  fixes p' a tr
  assumes "p \<simeq>PF q" "p \<mapsto> a p'"
  shows "\<exists>q'. p' \<simeq>PF q' \<and> q \<mapsto> a q'"
proof-
  from assms(1) have subs: "{(xs, X)|xs X. \<exists>p'. p \<mapsto>$ xs p' \<and> traces p' = X} = {(xs, X)|xs X. \<exists>p'. q \<mapsto>$ xs p' \<and> traces p' = X}"
    unfolding possible_futures_preordered_def possible_futures_equivalent_def by blast
  hence "\<forall>xs X. (\<exists>p'. p \<mapsto>$ xs p' \<and> traces p' = X) \<longleftrightarrow> (\<exists>q'. q \<mapsto>$ xs q' \<and> traces q' = X)" 
    by (smt (verit, best) CollectD CollectI Pair_inject)
  hence "\<forall>xs X. (\<exists>p'. p \<mapsto>$ (a#xs) p' \<and> traces p' = X) \<longleftrightarrow> (\<exists>q'. q \<mapsto>$ (a#xs) q' \<and> traces q' = X)" by blast
  hence impl: "\<forall>xs X. (\<exists>p''. (\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ xs p'') \<and> traces p'' = X) \<longleftrightarrow> (\<exists>q''. (\<exists>q'. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'') \<and> traces q'' = X)"
    using step_seq by auto
  hence impl: "\<forall>xs X. (\<exists>p' p''. p \<mapsto> a p' \<and> p' \<mapsto>$ xs p'' \<and> traces p'' = X) \<longleftrightarrow> (\<exists>q' q''. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'' \<and> traces q'' = X)"
    by metis
  hence impl: "\<forall>xs X. (\<exists>p'. (\<exists>p''. p \<mapsto> a p' \<and> p' \<mapsto>$ xs p'' \<and> traces p'' = X)) \<longleftrightarrow> (\<exists>q'. (\<exists>q''. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'' \<and> traces q'' = X))"
    by fastforce
  hence impl: "\<forall>xs X. (\<exists>p''. p \<mapsto> a p' \<and> p' \<mapsto>$ xs p'' \<and> traces p'' = X) \<longleftrightarrow> (\<exists>q' q''. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'' \<and> traces q'' = X)"
    using assms(2) replace_ex
    sorry
  then obtain q' where "\<forall>xs X. (\<exists>p''. p \<mapsto> a p' \<and> p' \<mapsto>$ xs p'' \<and> traces p'' = X) \<longleftrightarrow> (\<exists>q''. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'' \<and> traces q'' = X)"
    sorry
  with assms have "\<forall>xs X. (\<exists>p''. p' \<mapsto>$ xs p'' \<and> traces p'' = X) \<longrightarrow> (\<exists>q' q''. q \<mapsto> a q' \<and> q' \<mapsto>$ xs q'' \<and> traces q'' = X)"
    sorry
  hence "\<exists>q'. {(xs, X)|xs X. \<exists>p''. p' \<mapsto>$ xs p'' \<and> traces p'' = X} \<subseteq> {(xs, X)|xs X. \<exists>p''. q' \<mapsto>$ xs p'' \<and> traces p'' = X} \<and> q \<mapsto> a q'"
    sorry
    by blast
  then show ?thesis
    using possible_futures_preordered_def by presburger
qed

lemma pf_aux:
  assumes "\<phi> \<in> hml_possible_futures_formulas" "p \<simeq>PF q" "p \<Turnstile> \<phi>"
  shows "q \<Turnstile> \<phi>"
  using assms
proof(induction \<phi> arbitrary: p q)
  case TT
  then show ?case
    using hml_sem_tt by blast
next
  case (hml_pos \<alpha> \<psi>)
  hence "\<psi> \<in> hml_possible_futures_formulas" 
    by (metis CollectD CollectI hml.distinct(1) hml.distinct(5) hml.inject(1) hml_possible_futures.simps hml_possible_futures_formulas_def)
  from hml_pos obtain p' X where "p \<mapsto>\<alpha> p'" "p' \<Turnstile> \<psi>" "traces p' = X"
    using hml_sem_pos by blast
  hence "p \<mapsto>$ [\<alpha>] p'"
    using step_sequence.simps
    by metis 
  then obtain q' where "p' \<simeq>PF q'" "q \<mapsto> \<alpha> q'"
    using possible_futures_equivalent_def pf_trace_shortening hml_pos(3) 
    by (meson \<open>p \<mapsto>\<alpha> p'\<close>)
  hence "q' \<Turnstile> \<psi>" using hml_pos 
    using \<open>\<psi> \<in> hml_possible_futures_formulas\<close> \<open>p' \<Turnstile> \<psi>\<close> by blast
  then show ?case using \<open>q \<mapsto> \<alpha> q'\<close> 
    using hml_sem_pos by blast
next
  case (hml_conj I J \<Phi> p q)
  from this(3) have "\<forall>x1a \<in> \<Phi> ` (I \<union> J). hml_trace x1a"
    using hml_possible_futures.simps hml.distinct(3) hml.distinct(5) hml.inject(2) hml_conj.prems(1)
    by (metis hml_possible_futures_formulas_def mem_Collect_eq)  
  hence "\<forall>x1a \<in> \<Phi> ` (I \<union> J).  hml_possible_futures x1a"
    using trace_formula_is_pf_formula by blast
  have "\<forall>x1a \<in> \<Phi> ` I. p \<Turnstile> x1a" using hml_conj 
    by simp
  hence "\<forall>x1a \<in> \<Phi> ` I. q \<Turnstile> x1a" using hml_conj \<open>\<forall>x1a \<in> \<Phi> ` (I \<union> J).  hml_possible_futures x1a\<close> 
    by (simp add: hml_possible_futures_formulas_def)
  from hml_conj(4) have "\<forall>x1a \<in> \<Phi> ` J. \<not>p \<Turnstile> x1a" by simp
  have "\<forall>x1a \<in> \<Phi> ` J. \<not>q \<Turnstile> x1a" proof((rule ccontr), simp)
    assume "\<exists>x1a\<in>J. q \<Turnstile> \<Phi> x1a"
    then obtain x1a where "x1a \<in> J" "q \<Turnstile> \<Phi> x1a" by blast
    have "hml_trace (\<Phi> x1a)" 
      using \<open>\<forall>x1a\<in>\<Phi> ` (I \<union> J). hml_trace x1a\<close> \<open>x1a \<in> J\<close> by auto
    then obtain tr q' where "q \<mapsto>$ tr q'" using \<open>\<forall>x1a \<in> \<Phi> ` (I \<union> J). hml_trace x1a\<close>
      using step_sequence.intros(1) by blast
    have "\<nexists>p'. p \<mapsto>$ tr p'" using \<open>\<forall>x1a \<in> \<Phi> ` J. \<not>p \<Turnstile> x1a\<close> 
      by (metis (no_types, lifting) CollectI \<open>hml_trace (\<Phi> x1a)\<close> \<open>q \<Turnstile> \<Phi> x1a\<close> \<open>x1a \<in> J\<close> hml_conj(1) hml_conj(3) hml_conj(4) hml_possible_futures_formulas_def hml_sem_conj lts.possible_futures_equivalent_def rangeI trace_formula_is_pf_formula)
    then show False 
      by (metis (no_types, lifting) CollectI \<open>hml_trace (\<Phi> x1a)\<close> \<open>q \<Turnstile> \<Phi> x1a\<close> \<open>x1a \<in> J\<close> hml_conj.IH hml_conj.prems(2) hml_conj.prems(3) hml_possible_futures_formulas_def hml_sem_conj possible_futures_equivalent_def rangeI trace_formula_is_pf_formula)
  qed
  then show ?case using \<open>\<forall>x1a \<in> \<Phi> ` I. q \<Turnstile> x1a\<close> by simp
qed

fun 

(*TODO*)
fun pf_pair_to_formula where
"pf_pair_to_formula ([], X) = HML_conj [] []" |
"pf_pair_to_formula ((a#tail), X) = hml_pos a (pf_pair_to_formula (tail, X))"

theorem pf_auxillary:
  assumes "\<phi> \<in> HML_possible_futures_formulas" "p \<Turnstile> \<phi>"
  shows "\<exists>t X. (t, X) \<in> possible_future_pairs p \<and> p \<Turnstile> pf_pair_to_formula (t, X)"
  oops

lemma
  fixes p q a b xs X p'
  assumes "hml_possible_futures_equivalent p q" "p \<mapsto>$ xs p'"
  shows "\<exists>xsa X. (xs, traces p') = (xsa, X) \<and> (\<exists>p'. q \<mapsto>$ xsa p' \<and> traces p' = X)"
proof(rule ccontr, simp)
  assume " \<forall>q'. q \<mapsto>$ xs q' \<longrightarrow> traces q' \<noteq> traces p'"
  obtain \<Phi> I where "\<Phi> ` (I::'s set) = traces p'" sorry

  obtain X where "X = traces p'" by blast
  oops

theorem HM_possible_futures_theorem:
  shows "hml_possible_futures_equivalent p q = (p \<simeq>PF q)"
  unfolding possible_futures_equivalent_def
proof(safe)
  show "possible_future_pairs p = possible_future_pairs q \<Longrightarrow> hml_possible_futures_equivalent p q"
    using pf_aux 
    unfolding possible_futures_equivalent_def hml_possible_futures_equivalent_def
    by (metis (no_types, lifting))
next
  fix a b xs X p'
  assume "hml_possible_futures_equivalent p q" "p \<mapsto>$ xs p'"

  oops

end
end