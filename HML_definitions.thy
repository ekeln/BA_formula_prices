theory HML_definitions
imports HML_list
begin

inductive hml_trace :: "('a, 's)hml \<Rightarrow> bool" where
"hml_trace TT" |
"hml_trace (hml_pos \<alpha> \<phi>)" if "hml_trace \<phi>"

inductive hml_failure_trace :: "('a, 's)hml \<Rightarrow> bool" where
"hml_failure_trace TT" |
"hml_failure_trace (hml_pos \<alpha> \<phi>)" if "hml_failure_trace \<phi>" |
"hml_failure_trace (hml_conj I J \<Phi>)" 
  if "(\<Phi> ` I) = {} \<or> (\<exists>i \<in> \<Phi> ` I. \<Phi> ` I = {i} \<and> hml_failure_trace i)"
     "\<forall>j \<in> \<Phi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT) \<or> j = TT" 


context lts begin 

lemma 
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

lemma 
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

lemma 
  fixes \<phi> :: "('a, 's) hml"
  assumes "hml_failure_trace \<phi>"
  shows "\<exists>\<psi>. HML_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof induct
  case 1
  then show ?case
    using f_trace_tt by blast
next
  case (2 \<phi> \<alpha>)
  then obtain \<psi> where "HML_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  have "HML_failure_trace (hml_pos \<alpha> \<psi>)" 
    by (simp add: \<open>HML_failure_trace \<psi>\<close> f_trace_pos)
  have "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" 
    by (simp add: \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
  then show ?case 
    using \<open>HML_failure_trace (hml_pos \<alpha> \<psi>)\<close> by blast
next
  case (3 \<Phi> I J)
  hence neg_case: "\<forall>j\<in>\<Phi> ` J. stacked_pos_conj_pos j" 
    using stacked_pos_conj_pos.simps nested_empty_pos_conj.intros(1) by auto
  from 3(1) show ?case proof(rule disjE)
    assume "\<Phi> ` I = {}"
    hence "HML_failure_trace (hml_conj I J \<Phi>) \<and> (\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Phi>)))"
      using neg_case 
      by (simp add: f_trace_conj)
    then show ?thesis by blast
  next
    assume "\<exists>i\<in>\<Phi> ` I.
       \<Phi> ` I = {i} \<and> hml_failure_trace i \<and> (\<exists>\<psi>. HML_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>)))"
    then obtain i \<psi> where IH: "i\<in>\<Phi> ` I" "\<Phi> ` I = {i}" "hml_failure_trace i" "HML_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> i) = (s \<Turnstile> \<psi>))"
      by blast
    then show ?case
    proof(cases "I \<inter> J = {}")
      case True
      define \<Psi> where  \<Psi>_def: "\<Psi> = (\<lambda>x. if x \<in> I then \<psi> else (if x \<in> J then \<Phi> x else undefined))"
      have "\<Psi> ` I = {\<psi>}" unfolding \<Psi>_def using \<open>\<Phi> ` I = {i}\<close> by auto
      hence pos: "(\<exists>\<psi> \<in> (\<Psi> ` I). (HML_failure_trace \<psi>) \<and> (\<forall>y \<in> (\<Psi> ` I). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y))"
        by (simp add: \<open>HML_failure_trace \<psi>\<close>)
      hence "\<forall>\<psi> \<in> \<Psi> ` J. stacked_pos_conj_pos \<psi>"
        unfolding \<Psi>_def
        using neg_case \<open>I \<inter> J = {}\<close> 
        by auto
      hence "HML_failure_trace (hml_conj I J \<Psi>)" using pos 
        by (simp add: f_trace_conj)
      from \<Psi>_def have "(\<forall>s. \<forall>j \<in> J. (\<not>(s \<Turnstile> (\<Psi> j)) = (\<not>(s \<Turnstile> (\<Phi> j)))))" using IH 
        using True by auto
      from \<Psi>_def have "(\<forall>s. \<forall>i \<in> I. (\<not>(s \<Turnstile> (\<Psi> i)) = (\<not>(s \<Turnstile> (\<Phi> i)))))" using IH 
        by (metis emptyE imageI insertE)
      have "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> (hml_conj I J \<Psi>)))" using IH hml_sem_conj \<Psi>_def 
        using \<open>\<forall>s. \<forall>i\<in>I. (s \<Turnstile> \<Psi> i) \<noteq> (\<not> s \<Turnstile> \<Phi> i)\<close> by auto
    then show ?thesis using \<open>HML_failure_trace (hml_conj I J \<Psi>)\<close> by blast
    next
      case False
      then obtain j where "j \<in> I \<inter> J" by blast
      from False have "(\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>))"
        using index_sets_conj_disjunct 
        by presburger
      define \<Psi> where "\<Psi> = (\<lambda>x. if x \<in> (I \<inter> J) then TT::('a, 's) hml else undefined)"
      with \<open>j \<in> I \<inter> J\<close> have "\<Psi> ` (I \<inter> J) = {TT}" 
        by auto
      have "stacked_pos_conj_pos TT" 
        using stacked_pos_conj_pos.intros(1) by blast
      hence "(\<forall>y \<in> (\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" using \<Psi>_def \<open>j \<in> I \<inter> J\<close> 
        using \<open>\<Psi> ` (I \<inter> J) = {TT}\<close> by fastforce
      have "(\<forall>y \<in> (\<Psi> ` {}). nested_empty_conj y) \<and> (\<forall>y \<in> (\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" 
        using neg_case 
        using \<open>\<forall>y\<in>\<Psi> ` (I \<inter> J). stacked_pos_conj_pos y\<close> by blast
      hence f_trace: "((\<exists>\<psi>\<in>(\<Psi> ` ({}::'s set)). HML_failure_trace \<psi> \<and> (\<forall>y\<in>(\<Psi> ` ({}::'s set)). \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or>
     (\<forall>y\<in>(\<Psi> ` ({}::'s set)). nested_empty_conj y)) \<and>
    (\<forall>y\<in>(\<Psi> ` (I \<inter> J)). stacked_pos_conj_pos y)" 
        by fastforce 
      define \<psi> where "\<psi> \<equiv> (hml_conj ({}::'s set) (I \<inter> J) \<Psi>)"
      have "HML_failure_trace \<psi>" unfolding \<psi>_def using f_trace_conj f_trace 
        by fastforce
      have "\<forall>s. \<not> s \<Turnstile> \<psi>" 
        using \<Psi>_def \<open>j \<in> I \<inter> J\<close> \<psi>_def by auto
      then show ?thesis using \<open>HML_failure_trace \<psi>\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj I J \<Phi>\<close> by blast
    qed
  qed
qed

lemma stacked_pos_rewriting:
  assumes "stacked_pos_conj_pos \<phi>" "\<not>HML_true \<phi>"
  shows "\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
  using assms proof(induction \<phi>)
  case 1
  then show ?case 
    unfolding HML_true_def
    using TT_like.intros(1) HML_true_TT_like by simp
next
  case (2 \<psi> uu)
  then show ?case 
    using HML_true_def HML_true_nested_empty_pos_conj by auto
next
  case (3 \<Phi> I J)
  have "(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>)" 
    using lts.HML_true_nested_empty_pos_conj by blast
  have "((\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi>) \<and> \<Phi> ` J = {}) \<longrightarrow> HML_true (hml_conj I J \<Phi>)"
    by (simp add: lts.HML_true_nested_empty_pos_conj nested_empty_pos_conj.intros(2))
  with 3 obtain \<phi> where "\<phi>\<in>\<Phi> ` I"
        "stacked_pos_conj_pos \<phi>" "(\<not> HML_true \<phi> \<longrightarrow> (\<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)))"
        "(\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>)"
    by meson
  then have "\<not> HML_true \<phi>" using 3(3) \<open>(\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>)\<close>
    by (smt (verit, ccfv_threshold) "3.hyps" HML_true_def ball_imageD empty_iff empty_is_image hml_sem_conj)
  then obtain \<alpha> where "\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)" 
    using \<open>\<not> HML_true \<phi> \<longrightarrow> (\<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT))\<close> by blast
  have "\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_pos \<alpha> TT)" 
    using "3.hyps" "3.prems" HML_true_def \<open>\<forall>\<psi>\<in>\<Phi> ` I. \<psi> \<noteq> \<phi> \<longrightarrow> nested_empty_pos_conj \<psi>\<close> \<open>\<forall>\<psi>\<in>\<Phi> ` I. nested_empty_pos_conj \<psi> \<longrightarrow> HML_true \<psi>\<close> \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> hml_pos \<alpha> TT)\<close> by fastforce
  then show ?case by blast
qed

lemma nested_empty_conj_TT_or_FF:
  assumes "nested_empty_conj \<phi>"
  shows "(\<forall>s. (s \<Turnstile> \<phi>)) \<or> (\<forall>s. \<not>(s \<Turnstile> \<phi>))"
  using assms HML_true_nested_empty_pos_conj
  unfolding HML_true_def
  by(induction, simp, fastforce)

lemma 
  fixes \<phi> :: "('a, 's) hml"
  assumes "HML_failure_trace \<phi>"
  shows "\<exists>\<psi>. hml_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> \<phi>) \<longleftrightarrow> (s \<Turnstile> \<psi>))"
  using assms proof(induct)
  case f_trace_tt
  then show ?case 
    using hml_failure_trace.intros(1) by blast
next
  case (f_trace_pos \<phi> \<alpha>)
  then obtain \<psi> where "hml_failure_trace \<psi>" "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" by blast
  have "hml_failure_trace (hml_pos \<alpha> \<psi>)" 
    using \<open>hml_failure_trace \<psi>\<close> hml_failure_trace.simps by blast
  have "(\<forall>s. (s \<Turnstile> hml_pos \<alpha> \<phi>) = (s \<Turnstile> (hml_pos \<alpha> \<psi>)))" 
    by (simp add: \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
  then show ?case 
    using \<open>hml_failure_trace (hml_pos \<alpha> \<psi>)\<close> by blast
next
  case (f_trace_conj \<Phi> I J)
  hence neg_case: "\<forall>j\<in>\<Phi> ` J. stacked_pos_conj_pos j" 
    using stacked_pos_conj_pos.simps nested_empty_pos_conj.intros(1) by auto
  from f_trace_conj have IH: "((\<exists>\<psi>\<in>\<Phi> ` I.
            (HML_failure_trace \<psi> \<and> (\<exists>\<psi>'. hml_failure_trace \<psi>' \<and> (\<forall>s. (s \<Turnstile> \<psi>) = (s \<Turnstile> \<psi>')))) \<and>
            (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)) \<or>
        (\<forall>y\<in>\<Phi> ` I. nested_empty_conj y))" 
    by blast
  from IH show ?case proof(rule disjE)
    assume "\<exists>\<psi>\<in>\<Phi> ` I.
       (HML_failure_trace \<psi> \<and> (\<exists>\<psi>'. hml_failure_trace \<psi>' \<and> (\<forall>s. (s \<Turnstile> \<psi>) = (s \<Turnstile> \<psi>')))) \<and>
       (\<forall>y\<in>\<Phi> ` I. \<psi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
    then obtain \<phi> \<psi> where "\<phi>\<in>\<Phi> ` I" "HML_failure_trace \<phi>" "hml_failure_trace \<psi>" 
                          "(\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>))" "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> nested_empty_conj y)"
      by meson
    then obtain i_\<phi> where "\<Phi> i_\<phi> = \<phi>" 
      by blast
    consider "\<exists>y \<in> \<Phi>`I. \<phi> \<noteq> y \<and> (\<forall>s. \<not>(s \<Turnstile> y))" | "(\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> HML_true y)"
      unfolding HML_true_def
      using nested_empty_conj_TT_or_FF
      using \<open>\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> nested_empty_conj y\<close> by blast
    then show "\<exists>\<psi>. hml_failure_trace \<psi> \<and> (\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> \<psi>))"
    proof(cases)
      case 1
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)"
        using hml_sem_conj by blast
      obtain y where "y \<in> \<Phi>`I" "\<phi> \<noteq> y \<and> (\<forall>s. \<not> s \<Turnstile> y)" 
        using "1" by blast
      define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> I then (TT::('a, 's)hml) else undefined))"
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} I \<Psi>)" 
        using \<open>y \<in> \<Phi> ` I\<close> by auto
      have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` I. j = TT" 
         apply blast
        unfolding \<Psi>_def 
        using \<open>y \<in> \<Phi>`I\<close> 
        by simp
      hence "hml_failure_trace (hml_conj {} I \<Psi>)" 
        by (meson hml_failure_trace.intros(3))
      then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} I \<Psi>\<close> by blast
    next
      case 2
      consider "\<forall>y \<in> \<Phi>`J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" | "(\<exists>y\<in>\<Phi> ` J. HML_true y)"
        unfolding HML_true_def
        using stacked_pos_rewriting neg_case
        using that(2) by blast
      then show ?thesis proof(cases)
        case 1
        show ?thesis proof(cases "\<Phi> ` I \<inter> \<Phi> ` J = {}")
          case True
          hence "I \<inter> J = {}"
            by blast
          from 2 have "\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> (\<forall>s. s \<Turnstile> y)"
            unfolding HML_true_def 
            by blast
          hence "\<forall>s. (\<forall>i \<in> I. s \<Turnstile> (\<Phi> i)) \<longleftrightarrow> s \<Turnstile> \<phi>"
            using \<open>\<phi> \<in> \<Phi> ` I\<close> by auto
          define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then \<psi> 
                                    else (if i \<in> J then (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)  
                                                else undefined)))"
          have "\<phi> \<notin> \<Phi> ` J"
            using True \<open>\<phi> \<in> \<Phi> ` I\<close> 
            by blast
          hence "\<forall>i \<in> J. \<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)"
            using True "1" \<Psi>_def  
            using \<open>\<Phi> i_\<phi> = \<phi>\<close> by auto
          have "\<forall>j \<in> J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
            using neg_case stacked_pos_rewriting "1" by blast
          hence "\<forall>j \<in> J. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> \<Psi> j))"
            using True \<open>\<forall>i \<in> J. \<Psi> i = (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> i) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT)\<close>
            by (smt (verit, ccfv_threshold) tfl_some)
          have "\<forall>i \<in> I. \<Phi> i \<noteq> \<phi> \<longrightarrow> (\<forall>s. s \<Turnstile> \<Phi> i)"
            by (simp add: \<open>\<forall>y\<in>\<Phi> ` I. \<phi> \<noteq> y \<longrightarrow> (\<forall>s. s \<Turnstile> y)\<close>) 
          have "\<Psi> ` {i_\<phi>} = {\<psi>}" 
            using \<Psi>_def \<open>\<phi>\<in>\<Phi> ` I\<close> \<open>\<phi> \<notin> \<Phi> ` J\<close> \<open>I \<inter> J = {}\<close>
            by simp
          hence "\<forall>s. (\<forall>i \<in> {i_\<phi>}. s \<Turnstile> (\<Psi> i)) \<longleftrightarrow> s \<Turnstile> \<psi>" 
            using \<open>\<phi> \<in> \<Phi> ` I\<close> \<Psi>_def \<open>\<Phi> i_\<phi> = \<phi>\<close> by auto
          hence "\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {i_\<phi>} J \<Psi>)"
            using \<open>\<forall>j \<in> J. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> \<Psi> j))\<close>
            by (simp add: \<open>\<forall>s. (\<forall>i\<in>I. s \<Turnstile> \<Phi> i) = (s \<Turnstile> \<phi>)\<close> \<open>\<forall>s. (s \<Turnstile> \<phi>) = (s \<Turnstile> \<psi>)\<close>)
          have "\<forall>j \<in> \<Psi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT)" 
            using \<open>\<forall>i\<in>J. \<Psi> i = hml_pos (SOME \<alpha>. \<forall>s. (s \<Turnstile> \<Phi> i) = (s \<Turnstile> hml_pos \<alpha> TT)) TT\<close> by blast
          have "(\<exists>i \<in> \<Psi> ` {i_\<phi>}. \<Psi> ` {i_\<phi>} = {i} \<and> hml_failure_trace i)"
            using \<Psi>_def
            using \<open>\<Psi> ` {i_\<phi>} = {\<psi>}\<close> \<open>hml_failure_trace \<psi>\<close> by auto
          have "hml_failure_trace (hml_conj {i_\<phi>} J \<Psi>)"
            by (meson \<open>\<exists>i\<in>\<Psi> ` {i_\<phi>}. \<Psi> ` {i_\<phi>} = {i} \<and> hml_failure_trace i\<close> \<open>\<forall>j\<in>\<Psi> ` J. \<exists>\<alpha>. j = hml_pos \<alpha> TT\<close> hml_failure_trace.intros(3))
          then show ?thesis using \<open>\<forall>s. s \<Turnstile> (hml_conj I J \<Phi>) \<longleftrightarrow> s \<Turnstile> (hml_conj {i_\<phi>} J \<Psi>)\<close>
            by blast
        next
          case False
          hence "\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>)" 
            by fastforce
          then obtain \<phi> i_\<phi> where "\<phi> \<in> \<Phi> ` I \<inter> \<Phi> ` J" "\<Phi> i_\<phi> = \<phi>" 
            using False by blast
          define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i = i_\<phi> then TT::('a, 's)hml else undefined))"
          hence "\<forall>s. \<not>(s \<Turnstile> hml_conj {} {i_\<phi>} \<Psi>)" 
            by simp
          have "hml_failure_trace (hml_conj {} {i_\<phi>} \<Psi>)" 
            by (simp add: \<Psi>_def hml_failure_trace.intros(3))
          then show ?thesis using \<open>\<forall>s. \<not>(s \<Turnstile> hml_conj {} {i_\<phi>} \<Psi>)\<close> \<open>\<forall>s. \<not>(s \<Turnstile> hml_conj I J \<Phi>)\<close> 
            by blast
        qed
      next
        case 2
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
          unfolding HML_true_def 
          by fastforce
        obtain y where "y \<in> \<Phi>`J" "(\<forall>s. s \<Turnstile> y)" 
          using "2"
          unfolding HML_true_def 
          by blast
      define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> J then (TT::('a, 's)hml) else undefined))"
      hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} J \<Psi>)" 
        using \<open>y \<in> \<Phi> ` J\<close> by auto
      have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` J. j = TT" 
         apply blast
        unfolding \<Psi>_def 
        using \<open>y \<in> \<Phi>`J\<close> 
        by simp
      hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
        by (meson hml_failure_trace.intros(3))
      then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
        using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} J \<Psi>\<close> by blast
    qed
  qed
next
    assume "\<forall>y\<in>\<Phi> ` I. nested_empty_conj y"
    then show ?thesis proof(cases "\<exists>i\<in>I. (\<forall>s. (\<not>(s \<Turnstile> (\<Phi> i))))")
      case True
      hence "\<forall>s. (\<not>(s \<Turnstile> hml_conj I J \<Phi>))" 
        using hml_sem_conj by blast
      define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> I then TT:: ('a, 's) hml else undefined))"
      have "\<forall>j \<in> \<Psi> ` I. j = TT" 
        using \<Psi>_def by force
      hence "hml_failure_trace (hml_conj {} I \<Psi>)" using hml_failure_trace.intros(3)
        by (metis image_empty)
      have "\<forall>s. (\<not>(s \<Turnstile> hml_conj {} I \<Psi>))" 
        using True \<Psi>_def by force
      then show ?thesis using \<open>hml_failure_trace (hml_conj {} I \<Psi>)\<close> \<open>\<forall>s. (\<not>(s \<Turnstile> hml_conj I J \<Phi>))\<close>
        by blast
    next
      case False
      consider "\<forall>y \<in> \<Phi>`J. \<exists>\<alpha>. (\<forall>s. (s \<Turnstile> y) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" | "(\<exists>y\<in>\<Phi> ` J. HML_true y)"
        using neg_case stacked_pos_rewriting by blast
      then show ?thesis proof(cases)
        case 1
        from False have "\<forall>i \<in> I. (\<forall>s. (s \<Turnstile> (\<Phi> i)))"
        using nested_empty_conj_TT_or_FF \<open>\<forall>y\<in>\<Phi> ` I. nested_empty_conj y\<close> by blast 
        have "\<forall>i \<in> {}. (\<forall>s. (s \<Turnstile> (\<Phi> i)))" by blast
        define \<Psi> where "\<Psi> \<equiv> (\<lambda>i. (if i \<in> J 
              then (hml_pos (SOME \<alpha>. (\<forall>s. (s \<Turnstile> (\<Phi> i)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))) TT:: ('a, 's) hml) 
              else undefined))"
      have "\<forall>j\<in>\<Phi> ` J. (\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT))))" 
        using stacked_pos_rewriting neg_case 1 by blast
      hence "\<forall>j \<in> J. (\<exists>\<alpha>. (\<forall>s. (s \<Turnstile> \<Phi> j) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT))))" 
        by blast
      hence "\<forall>j \<in> J. \<exists>\<alpha> .\<Psi> j = (hml_pos \<alpha> TT) \<and> (\<forall>s. (s \<Turnstile> (\<Phi> j)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))"
      proof(safe)
        fix j
        assume "\<forall>j\<in>J. \<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT)" "j \<in> J"
        then obtain \<alpha> where "\<Psi> j = hml_pos \<alpha> TT" 
          using \<Psi>_def by fastforce
        hence "(\<forall>s. (s \<Turnstile> (\<Phi> j)) \<longleftrightarrow> (s \<Turnstile> (hml_pos \<alpha> TT)))" unfolding \<Psi>_def using \<open>j \<in> J\<close> 
          by (smt (verit, best) \<open>\<forall>j\<in>J. \<exists>\<alpha>. \<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT)\<close> tfl_some)
        then show "\<exists>\<alpha>. \<Psi> j = hml_pos \<alpha> TT \<and> (\<forall>s. (s \<Turnstile> \<Phi> j) = (s \<Turnstile> hml_pos \<alpha> TT))"
          using \<open>\<Psi> j = hml_pos \<alpha> TT\<close> by blast
      qed
      hence "\<forall>j \<in> J. \<forall>s. s \<Turnstile> (\<Psi> j) \<longleftrightarrow> s \<Turnstile> (\<Phi> j)" using \<Psi>_def 
        by metis
      hence "\<forall>j \<in> J. \<forall>s. \<not>s \<Turnstile> (\<Psi> j) \<longleftrightarrow> \<not>s \<Turnstile> (\<Phi> j)" by blast
      hence "(\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj {} J \<Psi>))"
        using \<open>\<forall>i \<in> I. (\<forall>s. (s \<Turnstile> (\<Phi> i)))\<close> \<open>\<forall>i \<in> {}. (\<forall>s. (s \<Turnstile> (\<Phi> i)))\<close> 
        by simp
      have "\<forall>j \<in> \<Psi> ` J. \<exists>\<alpha>. j = (hml_pos \<alpha> TT)" 
        by (simp add: \<Psi>_def)
      hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
        by (simp add: hml_failure_trace.intros(3))
      then show ?thesis
        using \<open>\<forall>s. (s \<Turnstile> hml_conj I J \<Phi>) = (s \<Turnstile> hml_conj {} J \<Psi>)\<close> by blast
      next
        case 2
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)" 
          unfolding HML_true_def 
          by fastforce
        obtain y where "y \<in> \<Phi>`J" "(\<forall>s. s \<Turnstile> y)" 
          using "2"
          unfolding HML_true_def 
          by blast
        define \<Psi> where \<Psi>_def: "\<Psi> = (\<lambda>i. (if i \<in> J then (TT::('a, 's)hml) else undefined))"
        hence "\<forall>s. \<not>s \<Turnstile> (hml_conj {} J \<Psi>)" 
          using \<open>y \<in> \<Phi> ` J\<close> by auto
        have "\<Psi> ` {} = {}" "\<forall>j \<in> \<Psi> ` J. j = TT" 
           apply blast
          unfolding \<Psi>_def 
          using \<open>y \<in> \<Phi>`J\<close> 
          by simp
        hence "hml_failure_trace (hml_conj {} J \<Psi>)" 
          by (meson hml_failure_trace.intros(3))
        then show ?thesis using \<open>\<forall>s. \<not>s \<Turnstile> (hml_conj I J \<Phi>)\<close> 
          using \<open>\<forall>s. \<not> s \<Turnstile> hml_conj {} J \<Psi>\<close> by blast
      qed
    qed
  qed 
qed

end
end