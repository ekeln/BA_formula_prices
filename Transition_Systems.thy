(*<*)
theory Transition_Systems
  imports Main
"HOL-Library.Countable_Set"
begin
(*>*)

section \<open>Labeled Transition Systems\<close>
text \<open>\label{sec:LTS}\<close>

text \<open>- modelling (reactive) systems\\
- model for parallel computation (Kel)\\
- formalization of deadlock (Kel)\\
- models "parallelism" - for q there may be many states q' such that q -> q' -> model non determinism\\\<close>

text \<open>Harel:\\
- reactive systems: continuously respond to external inputs\\
- doens't perform function but maintains relationship with its environment\<close>

text \<open>Labeled Transition Systems (LTS) serve as models for representing the behavior of systems (Kel76). 
An LTS consists of three components: processes, actions, and transitions. Processes represent momentary states or configurations of a system. Actions denote the events or operations that can occur within the system.
The outgoing transitions of each process correspond to the actions the system can perform in that state, yielding a subsequent state.
\<close>

subsubsection \<open>Definition 1 (Labeled transition Systems)\<close>

text \<open>A Labelled Transition System (LTS) is a tuple $\mathcal{S} = (\Proc, \Act, \rightarrow)$ where $\Proc$ is the set of processes, 
$\Act$ is the set of actions and $\rightarrow$ $\subseteq \Proc \times \Act \times \Proc$ is a transition relation.\\

In concurrency theory, it is customary that the semantics of Reactive Systems are given in terms of labelled transition systems.
The processes represent the states a reactive system can be in. A transition of one state into another, 
caused by performing an action, can be understood as moving along the corresponding edge in the transition relation. \\

- Example?\\

- examples (to reuse later?)???
\<close>

subsubsection \<open>Some more Definitions\<close>

text \<open>The $\alpha$-derivatives of a process are the processes that can be reached with one $\alpha$-transition:\<close>


text \<open>
- image finite? nötig?\\
- image countable?
- initial actions
- deadlock
- relevant actions?
- step sequence!
- \<close>

subsection \<open>Isabelle\<close>

text \<open>Zustände: \<open>'s\<close> und Aktionen \<open>'a\<close>, Transitionsrelation ist locale trans. Ein LTS wird dann durch
seine Transitionsrelation definiert.\<close>
locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> 
    ("_ \<mapsto>_ _" [70, 70, 70] 80)
begin

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close>
  where
\<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto>\<alpha> p'}\<close>

text \<open>Transition System is image-finite\<close>

definition image_finite where
\<open>image_finite \<equiv> (\<forall>p \<alpha>. finite (derivatives p \<alpha>))\<close>

definition image_countable :: \<open>bool\<close>
  where \<open>image_countable \<equiv> (\<forall> p \<alpha>. countable (derivatives p \<alpha>))\<close>

text \<open>stimmt definition? definition benötigt nach umstieg auf sets?\<close>
definition lts_finite where
\<open>lts_finite \<equiv> (finite (UNIV :: 's set))\<close>

abbreviation initial_actions:: \<open>'s \<Rightarrow> 'a set\<close>
  where
\<open>initial_actions p \<equiv> {\<alpha>|\<alpha>. (\<exists>p'. p \<mapsto>\<alpha> p')}\<close>

abbreviation deadlock :: \<open>'s \<Rightarrow> bool\<close> where
\<open>deadlock p \<equiv> (\<forall>a. derivatives p a = {})\<close>

text \<open>nötig?\<close>
abbreviation relevant_actions :: \<open>'a set\<close>
  where
\<open>relevant_actions \<equiv> {a. \<exists>p p'. p \<mapsto>a p'}\<close>

inductive step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$ _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$ [] p\<close> |
\<open>p \<mapsto>$ (a#rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close>

end

(*<*)
end
(*>*)