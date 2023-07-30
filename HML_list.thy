theory HML_list
  imports
 Main
 Transition_Systems

begin
(*TODO: prüfen, True drin durch leeren listen?*)
datatype ('a)formula_list =
HML_conj \<open>('a)formula_list list\<close>  \<open>('a)formula_list list\<close>
| HML_poss \<open>'a\<close> \<open>('a)formula_list\<close>

context lts begin

fun HML_semantics :: \<open>'s \<Rightarrow> ('a)formula_list \<Rightarrow> bool\<close>
(\<open>_ \<Turnstile> _\<close> [50, 50] 50)
  where
HML_sem_conj: \<open>(p \<Turnstile> HML_conj \<Phi> \<Psi>) = 
(\<forall>\<phi>. (\<phi> \<in> set \<Phi> \<longrightarrow> HML_semantics p  \<phi>) \<and> (\<phi> \<in> set \<Psi> \<longrightarrow> \<not>(HML_semantics p \<phi>)))\<close>
| HML_sem_poss: \<open>(HML_semantics p (HML_poss \<alpha> \<phi>)) = (\<exists> q. (p \<longmapsto>\<alpha> q) \<and> q \<Turnstile> \<phi>)\<close>
end

(*TODO*)
(*Trace equiv: T \<in> trace, wenn \<phi> dann auch <a>\<phi>.*)
(*(\<infinity>, 1, 0, 0, 0, 0)*)
inductive HML_trace :: "('a)formula_list \<Rightarrow> bool"
  where
"HML_trace (HML_conj [] [])"|
"HML_trace (HML_poss \<alpha> \<phi>)" if "HML_trace \<phi>"

end