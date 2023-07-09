theory TS_inst
  imports Main
begin

type_synonym state = "string"
type_synonym action = "string"

definition states :: "state set" where
  "states = {''p'', ''q''}"

definition actions :: "action set" where
  "actions = {''a'', ''b''}"

definition transition :: "(state \<times> action \<times> state) set" where
  "transition = {(''p'', ''a'', ''q''), (''p'', ''b'', ''p'')}"

definition instance_1 :: "(state set) \<times> (action set) \<times> (state \<times> action \<times> state) set" where
  "instance_1 = (states, actions, transition)"

lemma action_a_in_p_poss: (*p \<Turnstile> <a>T *)
  assumes "''p'' \<in> states"
  shows "\<exists>s'. (''p'', ''a'', s') \<in> transition"
proof -
  have "(''p'', ''a'', ''q'') \<in> transition"
    using assms transition_def by auto
  thus ?thesis by blast
qed

end
