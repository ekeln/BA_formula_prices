theory Transition_Systems
imports Main
begin


(* Zustände: \<open>'s\<close> und Aktionen \<open>'a\<close>, Transitionsrelation ist locale trans. Ein LTS wird dann durch
seine Transitionsrelation definiert.*)
locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close>
    ("_ \<longmapsto>_ _" [70, 70, 70] 80)
(*    and S :: \<open>'s set\<close>
    and A :: \<open>'a set\<close> *)
end