theory HML_definitions
imports HML_list Traces Failures
begin











context lts begin 

lemma alt_trace_def_implies_trace_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_trace \<phi>"
  shows "\<exists>\<psi>. HML_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms  
proof(induction \<phi> rule: hml_trace.induct)
  case 1
  then show ?case using trace_tt by blast
next
  case (2 \<phi> \<alpha>)
  then obtain \<psi> where "HML_trace \<psi>" and IH: "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "HML_trace (hml_pos \<alpha> \<psi>)" 
    by (simp add: trace_pos)
  have "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" using IH 
    by simp
  then show ?case 
    using \<open>HML_trace (hml_pos \<alpha> \<psi>)\<close> by blast
qed

lemma trace_def_implies_alt_trace_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_trace \<phi>"
  shows "\<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case trace_tt
  then show ?case 
    using hml_trace.intros(1) by blast
next
  case (trace_conj \<psi>s)
  have "hml_trace TT" 
    using hml_trace.intros(1) by blast
  have "(\<forall>s. (s \<Turnstile> hml_conj {} {} \<psi>s) = (s \<Turnstile> TT))" 
    by simp
  then show ?case using \<open>hml_trace TT\<close> by blast
next
  case (trace_pos \<phi> \<alpha>)
  then obtain \<psi> where IH: "hml_trace \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" using hml_sem_pos by simp
  from IH have "hml_trace (hml_pos \<alpha> \<psi>)" 
    using hml_trace.simps by blast
  then show ?case using \<open>(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))\<close> 
    by blast
qed

lemma trace_definitions_equivalent: 
  "\<forall>\<phi>. (HML_trace \<phi> \<longrightarrow> (\<exists>\<psi>. hml_trace \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  "\<forall>\<phi>. (hml_trace \<phi> \<longrightarrow> (\<exists>\<psi>. HML_trace \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  using trace_def_implies_alt_trace_def alt_trace_def_implies_trace_def by blast+

lemma alt_failure_def_implies_failure_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_failure \<phi>"
  shows "\<exists>\<psi>. HML_failure \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case failure_tt
  then show ?case 
    using HML_failure.failure_tt by blast
next
  case (failure_pos \<phi> \<alpha>)
  then show ?case 
    using HML_failure.failure_pos by fastforce
next
  case (failure_conj I J \<psi>s)
  have "HML_failure (hml_conj I J \<psi>s)"
    by (metis HML_failure.failure_conj TT_like.intros(1) empty_iff failure_conj.hyps(1) failure_conj.hyps(2))
  then show ?case 
    by blast
qed

lemma failure_def_implies_alt_failure_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_failure \<phi>"
  shows "\<exists>\<psi>. hml_failure \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case failure_tt
  then show ?case 
    using hml_failure.failure_tt by blast
next
  case (failure_pos \<phi> \<alpha>)
  then obtain \<psi> where "hml_failure \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "hml_failure (hml_pos \<alpha> \<psi>) \<and> (\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" 
    by (simp add: hml_failure.failure_pos)
  then show ?case by blast
next
  case (failure_conj I \<psi>s J)
  then show ?case proof(cases "\<not>(\<exists>j \<in> J. TT_like (\<psi>s j)) \<and> \<psi>s ` I \<inter> \<psi>s ` J = {}")
    case True
    hence "\<forall>j \<in> J. (\<exists>\<alpha> \<chi>. \<psi>s j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)" 
      using local.failure_conj by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J
                          then (hml_pos (SOME \<alpha>. \<exists>\<chi>. \<psi>s i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) TT)::('a, 's)hml 
                          else undefined))"
    hence "\<forall>\<psi> \<in> \<Psi> ` J. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT" 
      by force
    hence "\<forall>j \<in> J. \<exists>\<alpha> \<chi>. \<psi>s j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi> \<and> \<Psi> j = hml_pos \<alpha> TT" 
      using \<Psi>_def \<open>\<forall>j\<in>J. \<exists>\<alpha> \<chi>. \<psi>s j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>\<close> by fastforce
    hence "(\<forall>s. \<forall>j \<in> J. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<psi>s j)))))" 
      using True HML_true_TT_like HML_true_def by auto
    have "\<forall>s. \<forall>i \<in> I. s \<Turnstile> \<psi>s i" 
      using HML_true_TT_like HML_true_def local.failure_conj by blast
    hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<psi>s) = (s \<Turnstile> (hml_conj {} J \<Psi>)))"
      using \<open>(\<forall>s. \<forall>j \<in> J. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<psi>s j)))))\<close>
      by simp
    have "hml_failure (hml_conj {} J \<Psi>)" 
      using \<Psi>_def hml_failure.failure_conj
      by (metis (no_types, lifting))
    then show ?thesis 
      using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<psi>s) = (s \<Turnstile> hml_conj {} J \<Psi>)\<close> by blast
  next
    case False
    hence "\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<psi>s)" 
      using HML_true_TT_like HML_true_def by fastforce
    from False obtain \<phi> i_\<phi> where "\<phi> \<in> \<psi>s ` I \<inter> \<psi>s ` J \<or> (\<phi> \<in> \<psi>s ` J \<and> TT_like \<phi>)" "\<psi>s i_\<phi> = \<phi>"
      by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
    hence "\<forall>s. \<not>(s \<Turnstile> (hml_conj {} {i_\<phi>} \<Psi>))" 
      by auto
    have "hml_failure (hml_conj {} {i_\<phi>} \<Psi>)" 
      by (simp add: \<Psi>_def hml_failure.failure_conj)
    then show ?thesis 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<psi>s\<close> \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} {i_\<phi>} \<Psi>\<close> by blast
  qed
qed

lemma failure_definitions_equivalent: 
  "\<forall>\<phi>. (HML_failure \<phi> \<longrightarrow> (\<exists>\<psi>. hml_failure \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  "\<forall>\<phi>. (hml_failure \<phi> \<longrightarrow> (\<exists>\<psi>. HML_failure \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  using failure_def_implies_alt_failure_def alt_failure_def_implies_failure_def by blast+

lemma alt_readiness_def_implies_readiness_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_readiness \<phi>"
  shows "\<exists>\<psi>. HML_readiness \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case read_tt
  then show ?case 
    using HML_readiness.read_tt by blast
next
  case (read_pos \<phi> \<alpha>)
  then show ?case 
    using HML_readiness.read_pos by fastforce
next
  case (read_conj \<Phi> I J)
  hence "HML_readiness (hml_conj I J \<Phi>)" 
    by (metis HML_readiness.read_conj TT_like.simps)
  then show ?case by blast
qed

lemma readiness_def_implies_alt_readiness_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_readiness \<phi>"
  shows "\<exists>\<psi>. hml_readiness \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case read_tt
  then show ?case 
    using hml_readiness.read_tt by blast
next
  case (read_pos \<phi> \<alpha>)
  then obtain \<psi> where "hml_readiness \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  hence "hml_readiness (hml_pos \<alpha> \<psi>) \<and> (\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))"
    by (simp add: hml_readiness.read_pos)
  then show ?case by blast
next
  case (read_conj \<Phi> I J)
  then consider "\<Phi> ` I \<inter> \<Phi> ` J = {} \<and> (\<forall>x \<in> (\<Phi> ` J). (\<exists>\<alpha> \<chi>. x = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))"
    | "\<Phi> ` I \<inter> \<Phi> ` J \<noteq> {} \<or> (\<exists>x \<in>\<Phi>` J. (TT_like x))" 
    by blast
  then show ?case proof(cases)
    case 1
    hence "\<forall>j \<in> J. (\<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)" 
      by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if (\<exists>\<alpha> \<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)
                          then (hml_pos (SOME \<alpha>. \<exists>\<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>) TT)::('a, 's)hml 
                          else undefined))"
    hence "\<forall>\<psi> \<in> \<Psi> ` J. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT"
      by (simp add: \<open>\<forall>j\<in>J. \<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>\<close>)
    define I' where "I' \<equiv> {i. i \<in> I \<and> ((\<exists>\<alpha> \<chi>. \<Phi> i = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>))}"
    have "\<forall>\<psi> \<in> \<Psi> ` I'. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT"
      unfolding I'_def \<Psi>_def
      by force
    hence "\<forall>j \<in> (J \<union> I'). \<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi> \<and> \<Psi> j = hml_pos \<alpha> TT" 
      using \<Psi>_def \<open>\<forall>j \<in> J. (\<exists>\<alpha> \<chi>. \<Phi> j = hml_pos \<alpha> \<chi> \<and> TT_like \<chi>)\<close> 
      unfolding \<Psi>_def I'_def
      by force
    hence "(\<forall>s. \<forall>j \<in> J \<union> I'. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))" 
      using HML_true_TT_like HML_true_def 
      by (metis hml_sem_pos hml_sem_tt)
    have "\<forall>x \<in> (I - I'). TT_like (\<Phi> x)"
      using read_conj 1
      unfolding I'_def
      by auto
    hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Phi>)))"
      using HML_true_TT_like read_conj 1
      unfolding I'_def HML_true_def 
      by (smt (verit, del_insts) Diff_iff hml_sem_conj mem_Collect_eq)
    hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Psi>)))"
      using \<open>(\<forall>s. \<forall>j \<in> J \<union> I'. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))\<close>
      by simp
    have "hml_readiness (hml_conj I' J \<Psi>)" 
      using \<Psi>_def I'_def
      using hml_readiness.simps 
      by (smt (verit, best) Un_iff \<open>\<forall>\<psi>\<in>\<Psi> ` I'. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT\<close> \<open>\<forall>\<psi>\<in>\<Psi> ` J. \<exists>\<alpha>. \<psi> = hml_pos \<alpha> TT\<close> image_Un)
    then show ?thesis 
      using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I' J \<Psi>))\<close> by blast
  next
    case 2
    hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
      using HML_true_TT_like HML_true_def by fastforce 
    obtain \<phi> i_\<phi> where "\<phi> \<in> \<Phi> ` I \<inter> \<Phi> ` J \<or> (\<phi> \<in> \<Phi> ` J \<and> TT_like \<phi>)" "\<Phi> i_\<phi> = \<phi>"
      using 2 by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
    have "hml_readiness (hml_conj {} {i_\<phi>} \<Psi>)" 
      by (simp add: \<Psi>_def hml_readiness.read_conj)
    have "\<forall>s. \<not>s \<Turnstile> (hml_conj {} {i_\<phi>} \<Psi>)" 
      by (simp add: \<Psi>_def)
    then show ?thesis 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> \<open>hml_readiness (hml_conj {} {i_\<phi>} \<Psi>)\<close> by blast
  qed
qed

lemma readiness_definitions_equivalent: 
  "\<forall>\<phi>. (HML_readiness \<phi> \<longrightarrow> (\<exists>\<psi>. hml_readiness \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  "\<forall>\<phi>. (hml_readiness \<phi> \<longrightarrow> (\<exists>\<psi>. HML_readiness \<psi> \<and> (s \<Turnstile> \<psi> \<longleftrightarrow> s \<Turnstile> \<phi>)))"
  using readiness_def_implies_alt_readiness_def alt_readiness_def_implies_readiness_def by blast+

lemma alt_impossible_futures_def_implies_impossible_futures_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_impossible_futures \<phi>"
  shows "\<exists>\<psi>. HML_impossible_futures \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case if_tt
  then show ?case 
    using HML_impossible_futures.if_tt by blast
next
  case (if_pos \<phi> \<alpha>)
  then show ?case 
    using HML_impossible_futures.if_pos by fastforce
next
  case (if_conj I \<Phi> J)
  then consider "\<Phi> ` I \<inter> \<Phi> ` J \<noteq> {} \<or> (\<exists>x\<in>\<Phi> ` J. x = TT)"
    | "\<Phi> ` I \<inter> \<Phi> ` J = {} \<and> (\<forall>x\<in>\<Phi>`J. x \<noteq> TT) \<and> (\<exists>x. x \<in> \<Phi>`J)"
    | "\<Phi> ` J = {}"
    by blast
  then show ?case proof(cases)
    case 1
    hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
      using HML_true_TT_like HML_true_def by fastforce
    obtain \<phi> i_\<phi> where "\<phi> \<in> \<Phi> ` I \<inter> \<Phi> ` J \<or> (\<phi> \<in> \<Phi> ` J \<and> \<phi> = TT)" "\<Phi> i_\<phi> = \<phi>"
      using 1 by blast
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
    have "HML_impossible_futures (hml_conj {} {i_\<phi>} \<Psi>)" 
      using \<Psi>_def HML_impossible_futures.simps trace_tt by fastforce
   have "\<forall>s. \<not>s \<Turnstile> (hml_conj {} {i_\<phi>} \<Psi>)"
      by (simp add: \<Psi>_def)
    then show ?thesis 
      using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> \<open>HML_impossible_futures (hml_conj {} {i_\<phi>} \<Psi>)\<close> by blast
  next
    case 2
    hence "\<forall>x \<in> \<Phi>`J. \<exists>\<alpha> \<phi>. x = (hml_pos \<alpha> \<phi>) \<and> hml_trace \<phi>"
      using if_conj 
      by (meson hml_trace.cases)
    hence "\<forall>x \<in> \<Phi>`J. \<exists>\<alpha> \<phi>. x = (hml_pos \<alpha> \<phi>) \<and> hml_trace \<phi> \<and> (\<exists>\<psi>. HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))"
      using alt_trace_def_implies_trace_def by meson
    hence SOME_ex: "\<forall>j \<in> J. \<exists>\<alpha>. (\<exists>\<phi>. \<Phi> j = hml_pos \<alpha> \<phi>) \<and> (\<exists>\<psi>. \<exists>\<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))"
      by (meson imageI)
    hence SOME_all: "\<forall>j \<in> J. \<forall>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<longrightarrow> (\<exists>\<psi>. HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))"
      by fastforce
    define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J
    then (hml_pos (SOME \<alpha>. \<exists>\<phi>. \<Phi> i = hml_pos \<alpha> \<phi>) 
      (SOME \<psi>. \<exists>\<alpha> \<phi>. \<Phi> i = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))) 
    else undefined))"
    hence "\<forall>j \<in> J. \<exists>\<alpha> \<psi>. \<Psi> j = hml_pos \<alpha> \<psi>"
      using SOME_ex 
      by simp
    have "\<forall>j \<in> J. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<exists>\<psi>. HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))"
      using SOME_ex by blast
    have "\<forall>j \<in> J. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<exists>\<psi>. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))"
      using SOME_ex by blast
    have "\<forall>j \<in> J. \<forall>\<alpha> \<phi> \<psi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> \<Phi> j = \<psi> \<longrightarrow> \<psi> = hml_pos \<alpha> \<phi>" 
      by blast
    from SOME_all have "\<forall>j \<in> J. \<exists>\<alpha> \<psi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi>"
      using SOME_all \<Psi>_def SOME_ex someI_ex 
      by (smt (verit, best)) 
    hence "\<forall>j \<in> J. \<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi>"
      using SOME_ex \<Psi>_def by fastforce 
    have "\<forall>j \<in> J. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<forall>\<psi>. \<psi> \<noteq> (hml_pos \<alpha> \<phi>) \<longrightarrow> \<Phi> j \<noteq> \<psi>)" 
      using SOME_ex by blast

    have "\<And>j. j \<in> J \<Longrightarrow> \<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>)"
    proof -
      {
        fix j assume j_in_J: "j \<in> J"
        then show "\<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))"
        proof-
        have "\<Psi> j = (if j \<in> J 
                    then (hml_pos (SOME \<alpha>. \<exists>\<phi>. \<Phi> j = hml_pos \<alpha> \<phi>) 
                              (SOME \<psi>. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))) 
                    else undefined)"
          by (simp add: \<Psi>_def j_in_J)
        also have "... = (hml_pos (SOME \<alpha>. \<exists>\<phi>. \<Phi> j = hml_pos \<alpha> \<phi>) 
                              (SOME \<psi>. \<exists>\<alpha> \<phi>. \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>)))"
          using j_in_J by simp
        finally obtain \<alpha> \<phi> \<psi> where 
          psi_def: "\<Psi> j = hml_pos \<alpha> \<psi>" and 
          trace_psi: "HML_trace \<psi>" and 
          phi_alpha_def: "\<Phi> j = hml_pos \<alpha> \<phi>" and
          phi_psi_equivalence: "\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>" 
          using SOME_all \<open>\<forall>j\<in>J. \<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi>\<close> hml.inject(1) j_in_J someI_ex
          by (smt (verit, ccfv_threshold))
        have "\<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>)"
          using phi_alpha_def phi_psi_equivalence psi_def trace_psi by blast
        then show "\<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> HML_trace \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))"
          by blast
      qed
    }
  qed
    hence "\<forall>j \<in> J. (\<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<phi> \<longleftrightarrow> s \<Turnstile> \<psi>))" 
      using SOME_all \<Psi>_def SOME_ex someI_ex 
      by auto
    hence "\<forall>j \<in> J. \<forall>s. s \<Turnstile> \<Psi> j \<longleftrightarrow> s \<Turnstile> \<Phi> j"
      using SOME_ex \<Psi>_def by fastforce
    hence "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {} J \<Psi>)"
      by (simp add: if_conj.hyps(1))
    have "\<forall>j \<in> J. HML_trace (\<Psi> j)" 
      using \<open>\<forall>j\<in>J. \<exists>\<alpha> \<psi> \<phi>. \<Psi> j = hml_pos \<alpha> \<psi> \<and> \<Phi> j = hml_pos \<alpha> \<phi> \<and> HML_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))\<close> trace_pos by fastforce
    hence "HML_impossible_futures (hml_conj {} J \<Psi>)"
      by (simp add: HML_impossible_futures.if_conj)
    then show ?thesis 
      using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj {} J \<Psi>)\<close> by blast
  next
    case 3
    hence "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>)" "HML_impossible_futures TT" "\<forall>s. s \<Turnstile> TT" 
      by (simp add: if_conj.hyps(1) HML_impossible_futures.if_tt)+
    then show ?thesis by blast
  qed 
qed

lemma impossible_futures_def_implies_alt_impossible_futures_def:
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_impossible_futures \<phi>"
  shows "\<exists>\<psi>. hml_impossible_futures \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case if_tt
  then show ?case 
    using hml_impossible_futures.if_tt by blast
next
  case (if_pos \<phi> \<alpha>)
  then show ?case 
    using hml_impossible_futures.if_pos by force
next
  case (if_conj \<Phi> I J)
  hence "\<forall>x \<in> \<Phi>`J. (\<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> x \<longleftrightarrow> s \<Turnstile> \<psi>))"
    using trace_def_implies_alt_trace_def by blast 
  hence "\<forall>j \<in> J. (\<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>))"
    by blast
  hence "\<And>j. j \<in> J \<Longrightarrow> \<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>)" by blast
  define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J then (SOME \<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> i \<longleftrightarrow> s \<Turnstile> \<psi>)) 
                              else undefined))"
  have "\<And>j. j \<in> J \<Longrightarrow> hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)"
    unfolding \<Psi>_def using \<open>\<And>j. j \<in> J \<Longrightarrow> \<exists>\<psi>. hml_trace \<psi> \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<psi>)\<close>
    by (smt (verit, ccfv_SIG) someI)
  hence "\<forall>j \<in> J. hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)" 
    by blast
  hence "hml_impossible_futures (hml_conj {} J \<Psi>)" 
    using hml_impossible_futures.simps by fastforce
  have "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {} J \<Psi>)" 
    using HML_true_TT_like HML_true_def \<open>\<forall>j \<in> J. hml_trace (\<Psi> j) \<and> (\<forall>s. s \<Turnstile> \<Phi> j \<longleftrightarrow> s \<Turnstile> \<Psi> j)\<close> if_conj.hyps(1) by auto
  then show ?case 
    using \<open>hml_impossible_futures (hml_conj {} J \<Psi>)\<close> by blast
qed



end
end