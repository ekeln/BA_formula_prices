theory Bisimulation
imports
Simulation
begin

context lts begin
text \<open>Two states are bisimilar if they can be related by a symmetric simulation.\<close>
definition bisimilar (infix \<open>\<simeq>B\<close> 80) where
  \<open>p \<simeq>B q \<equiv> \<exists>R. simulation R \<and> symp R \<and> R p q\<close>

text \<open>Bisimilarity is a simulation.\<close>
lemma bisim_sim:
  shows \<open>simulation (\<simeq>B)\<close>
  unfolding bisimilar_def simulation_def by blast

end

end