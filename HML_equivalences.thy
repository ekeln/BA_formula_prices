theory HML_equivalences
imports Main
HML_list
begin

context lts begin

definition HML_trace_equivalent where
"HML_trace_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> HML_trace_formulas \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

definition HML_simulation_equivalent :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  "HML_simulation_equivalent p q \<equiv> 
(\<forall>\<phi>. \<phi> \<in> HML_simulation_formulas \<longrightarrow> (p \<Turnstile> \<phi> \<longleftrightarrow> q \<Turnstile> \<phi>))"

definition HML_possible_futures_equivalent where
"HML_possible_futures_equivalent p q \<equiv> (\<forall> \<phi>. \<phi> \<in> HML_possible_futures_formulas \<longrightarrow> (p \<Turnstile> \<phi>) \<longleftrightarrow> (q \<Turnstile> \<phi>))"

end
end