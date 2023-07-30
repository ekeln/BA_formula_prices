theory HML_def
  imports 
    Transition_Systems
    "HOL-Library.Countable_Set_Type"
begin
notation cin (\<open>_ \<in>\<^sub>c _\<close> [100, 100] 100) 


(*Nur endliche Konjunktion, Negation nur "nach" Konjuntionen*)
datatype ('a)formula =
HML_conj \<open>('a)neg_formula cset\<close> 
| HML_poss \<open>'a\<close> \<open>('a)formula\<close>
and ('a)neg_formula =
HML_neg \<open>('a)formula\<close>
| HML_neg_conj \<open>('a)neg_formula cset\<close>
| HML_neg_poss \<open>'a\<close> \<open>('a)formula\<close>


(* abzählbar inf HML*)
datatype ('a, 'x)HML_formula =
HML_true
| HML_conj_2 \<open>'x set\<close> \<open>'x \<Rightarrow> ('a, 'x)HML_neg_formula\<close>(*negierte, nicht neg mengen teilen*)
| HML_poss_2 \<open>'a\<close> \<open>('a, 'x)HML_formula\<close>
and ('a, 'x)HML_neg_formula =
HML_neg_2 \<open>('a, 'x)HML_formula\<close>
| HML_no_neg \<open>('a, 'x)HML_formula\<close>


context lts begin

function HML_semantics :: \<open>'s \<Rightarrow> ('a)formula \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50) and
  HML_semantics_neg :: \<open>'s \<Rightarrow> ('a) neg_formula \<Rightarrow> bool\<close> 
  where
HML_sem_conj: \<open>(p \<Turnstile> HML_conj \<Phi>) = (\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> HML_semantics_neg p  \<phi>)\<close>
| HML_sem_poss: \<open>(HML_semantics p (HML_poss \<alpha> \<phi>)) = (\<exists> q. (p \<longmapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close>
| HML_sem_n: \<open>HML_semantics_neg p (HML_neg \<phi>) = (\<not> (p \<Turnstile> \<phi>))\<close>
| HML_sem_n_conj: \<open>HML_semantics_neg p (HML_neg_conj \<Phi>) = (\<forall>\<phi>. \<phi> \<in>\<^sub>c \<Phi> \<longrightarrow> HML_semantics_neg p \<phi>)\<close>
| HML_sem_n_poss: \<open>HML_semantics_neg p (HML_neg_poss \<alpha> \<phi>) = (\<exists> q. (p \<longmapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close> 
apply (metis formula.exhaust neg_formula.exhaust obj_sumE surj_pair)          
  apply simp+
  done

inductive_set HML_wf_rel :: \<open>('s \<times>('a) formula) rel\<close>
and HML_wf_rel_2 :: \<open>('s \<times> ('a) neg_formula) rel\<close>
  and HML_wf_rel_3 :: \<open>(('s \<times> ('a)neg_formula) \<times> ('s \<times> ('a)formula)) set\<close>
and HML_wf_rel_4 :: \<open>(('s \<times> ('a)formula) \<times> ('s \<times> ('a)neg_formula)) set\<close>
  where
\<open>((p, \<phi>), (p', HML_poss \<alpha> \<phi>)) \<in> HML_wf_rel\<close>
| \<open>\<phi> \<in>\<^sub>c \<Phi> \<Longrightarrow> ((p, \<phi>), (p, HML_conj \<Phi>)) \<in> HML_wf_rel_3\<close>
| \<open>((p, \<phi>), (p, HML_neg \<phi>)) \<in> HML_wf_rel_4\<close>
| \<open>((p, \<phi>), (p', HML_neg_poss \<alpha> \<phi>)) \<in> HML_wf_rel_4\<close>
| \<open>\<phi> \<in>\<^sub>c \<Phi> \<Longrightarrow> ((p, \<phi>), (p, HML_neg_conj \<Phi>)) \<in> HML_wf_rel_2 \<close>

thm wf
termination sorry

thm obj_sumE
thm surj_pair

thm HML_semantics_neg.cases
thm HML_semantics.pelims

function HML_inf_semantics :: \<open>'s \<Rightarrow> ('a, 'x)HML_formula \<Rightarrow> bool\<close> and
HML_inf_semantics_neg :: \<open>'s \<Rightarrow> ('a, 'x)HML_neg_formula \<Rightarrow> bool\<close> where
sem_inf_true: \<open>HML_inf_semantics p HML_true = True\<close>
| sem_inf_conj: \<open>HML_inf_semantics p (HML_conj_2 I F) = (\<forall> i \<in> I. HML_inf_semantics_neg p (F i))\<close>
| sem_inf_poss: \<open>HML_inf_semantics p (HML_poss_2 \<alpha> \<phi>) = (\<exists> p'. p \<longmapsto>\<alpha> p' \<and> HML_inf_semantics p' \<phi>)\<close>
| sem_inf_neg: \<open>HML_inf_semantics_neg p (HML_neg_2 \<phi>) = (\<not> HML_inf_semantics p \<phi>)\<close>
| sem_inf_no_neg: \<open>HML_inf_semantics_neg p (HML_no_neg \<phi>) = HML_inf_semantics p \<phi>\<close>
apply (metis HML_formula.exhaust HML_neg_formula.exhaust obj_sumE surj_pair)
  apply simp+
  done

termination sorry

  end
end