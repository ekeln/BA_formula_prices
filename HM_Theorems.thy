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

function set_to_list2 :: "'b set \<Rightarrow> 'b list" where
"set_to_list2 s = (if finite s then (if s = {} then [] else 
                   let x = SOME x. x \<in> s; 
                    s' = s - {x} in x # set_to_list2 s') else [])"
  by simp+

termination set_to_list2
proof
  show "wf (measure card)"
    by blast
  show "\<And>s x xa. finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> x = (SOME x. x \<in> s) \<Longrightarrow> xa = s - {x} \<Longrightarrow> (xa, s) \<in> measure card"
    by (metis card_Diff1_less_iff ex_in_conv in_measure tfl_some)
qed


lemma 
  assumes "finite s"
  defines "s_lst \<equiv> set_to_list2 s"
  shows "\<forall>x \<in> set s_lst. x \<in> s"
  using assms
proof(induction s_lst  arbitrary: s rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons a s_lst)
  then have 1: "\<forall>x\<in>set s_lst. x \<in> s" using set_to_list2.simps
    by (metis DiffE ex_in_conv list.distinct(1) list.inject list.set(1))
  from Cons(3) have "a = (SOME x. x \<in> s)" using set_to_list2.elims
    by (metis list.distinct(1) list.sel(1))
  then have "a \<in> s" 
    using Cons.hyps(3) some_in_eq by fastforce
  with 1 show ?case
    by simp
qed

function set_to_list :: "'s set \<Rightarrow> 's list" where
  "set_to_list s = (if finite s then (if s = {} then [] else 
                   let x = SOME x. x \<in> s; 
                    s' = s - {x} in x # set_to_list s') else [])"
  by simp+

termination set_to_list
proof
  show "wf (measure card)"
    by blast
  show "\<And>s x xa. finite s \<Longrightarrow> s \<noteq> {} \<Longrightarrow> x = (SOME x. x \<in> s) \<Longrightarrow> xa = s - {x} \<Longrightarrow> (xa, s) \<in> measure card"
    by (metis card_Diff1_less_iff ex_in_conv in_measure tfl_some)
qed

lemma test:
  fixes p a
  defines "der \<equiv> (derivatives p a)"
  assumes "finite (der)"
  shows "\<forall>p' \<in> set (set_to_list (der)). p' \<in> der"
proof-
  define der_lst where "der_lst \<equiv> set_to_list (der)"
  then show "\<forall>p'\<in>set (set_to_list der). p' \<in> der"
  using assms(2)
proof(induction der_lst arbitrary: der rule: list.induct)
  case Nil
  then show ?case by simp
next
  case (Cons hd rest)
  then have 1: "\<forall>x\<in>set rest. x \<in> der" unfolding der_lst_def der_def using set_to_list.simps
    by (metis finite_Diff insert_Diff insert_iff list.distinct(1) list.sel(3) some_in_eq)
  from Cons(3) have "hd \<in> der" using some_in_eq set_to_list.elims 
    by (metis Cons.hyps(2) list.distinct(1) list.sel(1))
  with 1 show ?case
    by (metis Cons.hyps(2) set_ConsD)
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
  with der_list_def have "\<forall>q' \<in> set der_list. q' \<in> der"
  proof(induction der_list arbitrary: der)
    case Nil
    then show ?case by simp
  next
    case (Cons hd rest)
    from Cons have "\<forall>q'\<in>set rest. q' \<in> der" unfolding der_list_def der_def using set_to_list.simps  
    by (metis finite_Diff insert_Diff insert_iff list.distinct(1) list.sel(3) some_in_eq)
    then show ?case using some_in_eq set_to_list.elims 
      by (metis Cons.hyps(2) list.distinct(1) list.inject set_ConsD)
  qed
  define \<phi>d_list where \<open>\<phi>d_list \<equiv> map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') der_list\<close>
  define \<phi>d where \<open>\<phi>d \<equiv> HML_poss a (HML_conj \<phi>d_list [])\<close>
  assume contra_assms:
    \<open>p \<mapsto> a p'\<close> \<open>HML_equivalent p q\<close> \<open>\<nexists>q'. q \<mapsto> a q' \<and>  HML_equivalent p' q'\<close>
  hence dist_exists: \<open>\<forall>q' \<in> der. \<exists>\<phi>. distinguishes \<phi> p' q'\<close>
    unfolding der_def using hml_distinctions by simp
  then have dist: "\<forall>q' \<in> set (set_to_list der). \<exists>\<phi>. distinguishes \<phi> p' q'"
    using \<open>\<forall>q'\<in>set der_list. q' \<in> der\<close> der_list_def by blast
  hence "\<forall>\<psi> \<in> set \<phi>d_list. p' \<Turnstile> \<psi>"
    unfolding \<phi>d_list_def  
    using der_list_def
  proof(induction der_list arbitrary: der rule: list.induct)
    case Nil
    then show ?case by simp 
  next
    case (Cons hd tail)
    then have A1: "tail = set_to_list (der - {hd})" using set_to_list.elims 
      by (metis (no_types, lifting) list.discI list.inject)
    with Cons have A2: " \<forall>q'\<in>set (set_to_list (der - {hd})). \<exists>\<phi>. distinguishes \<phi> p' q'" 
      using set_to_list.elims 
      by (metis list.set_intros(2))
    with A1 Cons have 1: "\<forall>a\<in>set (map (\<lambda>q'. SOME \<psi>. distinguishes \<psi> p' q') tail). p' \<Turnstile> a" 
      by blast
    from Cons have "\<exists>\<psi>. distinguishes \<psi> p' hd" using der_list_def set_to_list.simps
      by (metis list.set_intros(1))
    then have "p' \<Turnstile> (SOME \<psi>. distinguishes \<psi> p' hd)" 
      by (metis (mono_tags, lifting) someI2_ex)
    with 1 show ?case 
      by (metis (no_types, lifting) list.simps(9) set_ConsD) 
  qed
  hence p'_sat: "p' \<Turnstile> (HML_conj \<phi>d_list [])" 
    by force
  with contra_assms(1) have "p \<Turnstile> \<phi>d" unfolding \<phi>d_def
    using local.HML_sem_poss by blast
  have \<open>(\<forall>q'. q' \<in> der \<longrightarrow> \<not>q' \<Turnstile> HML_conj \<phi>d_list [])\<close>
  proof safe
    fix q'
    assume q'_in_der: "q' \<in> der" and q'_sat: "q' \<Turnstile> HML_conj \<phi>d_list []"
    from dist_exists have "\<exists>\<phi>. distinguishes \<phi> p' q'"
      using q'_in_der by blast
    from q'_in_der have "q \<mapsto>a q'" unfolding der_def
      by blast
    with contra_assms(3) have "\<not>(\<forall> \<phi>::('a) formula_list. (p' \<Turnstile> \<phi>) \<longrightarrow> (q' \<Turnstile> \<phi>))" 
      unfolding HML_equivalent_def
      using \<open>\<exists>\<phi>. distinguishes \<phi> p' q'\<close> by blast
    with contra_assms equiv_der show False
      using \<open>q \<mapsto>a q'\<close> by blast
  qed
  with contra_assms(1) \<open>p' \<Turnstile> HML_conj \<phi>d_list []\<close> have \<open>distinguishes \<phi>d p q\<close>
    using \<phi>d_def der_def by auto
  thus False using contra_assms unfolding HML_equivalent_def by blast
qed

theorem Hennessy_Milner_theorem:
  assumes "image_finite"
  shows
    \<open>HML_equivalent p q = (p \<simeq>B q)\<close>
  using hml_bisim_invariant hml_equiv_sym HML_equiv_sim hml_distinctions
  unfolding bisimilar_def HML_equivalent_def
  using assms by blast



end
end