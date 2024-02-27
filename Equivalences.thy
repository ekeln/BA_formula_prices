(*<*)
theory Equivalences
imports Transition_Systems
begin
(*>*)

(*<*)
(*Zu viel dopplng mit introduction Evtl irgwo bisimilarity und HM-Theorem einbauen, sonst weglassen.*)
section \<open>Behavioral Equivalence of Processes\<close>

text \<open>One important equivalence relation is trace equivalence. 
Trace equivalence considers two states of an LTS equivalent if they produce the same 
sequence of observable actions, or "traces," when starting from those states. 
In other words, two states are trace equivalent if they lead to indistinguishable observable behaviors.

Trace equivalence is motivated by the desire to abstract away internal details of a system and 
focus solely on its externally observable behavior. In many practical scenarios, 
such as distributed systems or communication protocols, what matters most is the sequence of 
interactions with the environment rather than the intricate internal workings of the system. 
By considering processes with the same traces as equivalent, we can simplify the analysis and 
verification of systems while still capturing their essential observable behavior. 
This abstraction allows us to reason about complex systems more effectively and 
make predictions about their behavior in real-world scenarios.
\<close>

(*Für section bisimilarity*)
subsubsection \<open>Bisimilarity\<close>
text \<open>The notion of strong bisimilarity can be formalised through \emph{strong bisimulation} (SB) relations, introduced originally in (citation Park). 
A binary relation $\mathcal{R}$ over the set of processes $\Proc$ is an SB iff for all $(p,q) \in \mathcal{R}$:
\begin{align*}
&\forall p' \in \Proc,\; \alpha \in \Act .\; p \xrightarrow{\alpha} p' \longrightarrow
\exists q' \in \Proc .\; q \xrightarrow{\alpha} q' \wedge (p',q') \in \mathcal{R}, \text{ and}\\
&\forall q' \in \Proc,\; \alpha \in \Act .\; q \xrightarrow{\alpha} q' \longrightarrow
\exists p' \in \Proc .\; p \xrightarrow{\alpha} p' \wedge (p',q') \in \mathcal{R}.
\end{align*}\<close>
end
(*>*)