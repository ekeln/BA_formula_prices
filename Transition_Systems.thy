(*<*)
theory Transition_Systems
  imports Main
"HOL-Library.Countable_Set"
begin
(*>*)

section \<open>Labeled Transition Systems\<close>
text \<open>\label{sec:LTS}\<close>

text \<open>As mentioned in (Introduction), labeled transition systems are formal models used to describe the behavior of reactive systems.
A LTS consists of three components: processes, actions, and transitions. Processes represent momentary states or configurations of a system. Actions denote the events or operations that can occur within the system.
The outgoing transitions of each process correspond to the actions the system can perform in that state, yielding a subsequent state.
A process may have multiple outgoing transitions labeled with the same or different actions. This signifies that the system can choose any of these transitions nondeterministically
\footnote{Note that "nondeterministic" has been used  differently in some of the literature (citation needed). In the context of reactive systems, 
all transitions are directly triggered by external actions or events and represent synchronization with the environment.
The next state of the system is then uniquely determined by its current state and the external action. In that sense the behavior of the system is deterministic.}.
The semantic equivalences treated in (Glabbeeck) are defined entirely in terms of action relations.
We treat processes as being \textit{sequential}, meaning it can perform at most one action at a time, and instantanious.
Note that many modeling methods of systems use a special $\tau$-action to represent internal behavior. However, in our definition of LTS, 
internal behavior is not considered.\<close>

subsubsection \<open>Definition 1.1 (Labeled transition Systems)\<close>

text \<open>A \textit{Labeled Transition System} (LTS) is a tuple $\mathcal{S} = (\Proc, \Act, \rightarrow)$ where $\Proc$ is the set of processes, 
$\Act$ is the set of actions and $\rightarrow$ $\subseteq \Proc \times \Act \times \Proc$ is a transition relation.
We write $p \rightarrow{\alpha} p'$ for $(p, \alpha, p')\in \rightarrow$.\<close>

text \<open>Actions and processes are formalized using type variable \<open>'a\<close> and \<open>'s\<close>, respectively. As only actions and states involved in the transition relation are relevant, 
the set of transitions uniquely defines a specific LTS. We express this relationship using the predicate \<open>tran\<close>. We associate it with a more readable notation (\<open>p \<mapsto>\<alpha> p'\<close> for $p \xrightarrow{\alpha} p'$).\<close>

locale lts = 
  fixes tran :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> 
    ("_ \<mapsto>_ _" [70, 70, 70] 80)
begin

text \<open>Example... (to reuse later?)\<close>

text \<open>We introduce some concepts to better talk about LTS. Note that these Isabelle definitions are only defined in the \<open>context\<close> of LTS.\<close>

subsubsection \<open>Definition 1.2\<close>

text \<open>The \textit{$\alpha$-derivatives} of a state refer to the set of states that can be reached with an $\alpha$-transition:
$$mathit{Der} (p, \alpha) = \{ p' \mid p \xrightarrow{\alpha} p' \}.$$\<close>

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close>
  where
\<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto>\<alpha> p'}\<close>

text \<open>The set of \textit{initial actions} of a process $p$ is defined by: 
$$I(p)={\alpha \in Act \mid \exists p'. p \xrightarrow{\alpha} p'}$$\<close>

abbreviation initial_actions:: \<open>'s \<Rightarrow> 'a set\<close>
  where
\<open>initial_actions p \<equiv> {\<alpha>|\<alpha>. (\<exists>p'. p \<mapsto>\<alpha> p')}\<close>

text \<open>The step sequence relation $\xrightarrow{\sigma}*$ for $\sigma \in \Act$ is the reflexive transitive closure of $p \xrightarrow{\alpha} p'$.
It is defined recursively by:
\begin{align*}
  p &\xrightarrow{\varepsilon}^* p \\
  p &\xrightarrow{\alpha} p' \text{ with } \alpha \in \text{Act} \text{ and } p' \xrightarrow{\sigma}^* p'' \text{ implies } p' \xrightarrow{\sigma}^* p''
\end{align*}
\<close>

inductive step_sequence :: \<open>'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$ _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$ [] p\<close> |
\<open>p \<mapsto>$ (a#rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close>

text \<open>$p$ is image-finite if for each $\alpha \in \Act$ the set $mathit{Der} (p, \alpha)$ is finite.
An LTS is image-finite if each $p \in \Proc$ is image-finite:
"$$\forall p \in\Proc, \alpha \in \Act. mathit{Der} (p, \alpha)$$ is finite.\<close>

definition image_finite where
\<open>image_finite \<equiv> (\<forall>p \<alpha>. finite (derivatives p \<alpha>))\<close>

text \<open>We say that a process is in a \textit{deadlock} if no observation is possible. That is:
$$\mathit{deadlock} p = (\forall\alpha .\mathit{deadlock} p \alpha = \varnothing)$$\<close>

abbreviation deadlock :: \<open>'s \<Rightarrow> bool\<close> where
\<open>deadlock p \<equiv> (\<forall>\<alpha>. derivatives p \<alpha> = {})\<close>

text \<open>nötig?\<close>

definition image_countable :: \<open>bool\<close>
  where \<open>image_countable \<equiv> (\<forall> p \<alpha>. countable (derivatives p \<alpha>))\<close>

text \<open>stimmt definition? definition benötigt nach umstieg auf sets?\<close>
definition lts_finite where
\<open>lts_finite \<equiv> (finite (UNIV :: 's set))\<close>

abbreviation relevant_actions :: \<open>'a set\<close>
  where
\<open>relevant_actions \<equiv> {a. \<exists>p p'. p \<mapsto>a p'}\<close>


end

(*<*)
end
(*>*)