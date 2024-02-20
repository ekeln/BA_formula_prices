(*<*)
theory Equivalences
imports Transition_Systems
begin
(*>*)

section \<open>Behavioral Equivalence of Processes\<close>

text \<open>As discussed in the previous sections, LTSs model the behaviour of reactive systems. That behaviour
is observable by the environment in terms of transitions performed by the system. Depending on different criteria
on what constitutes equal behavior has led to a large number of equivalences for concurrent processes. Those equivalences are often
defined in term of relations on LTSs or sets of executions. The finest commonly used \textit{extensional behavioral equivalence}
is \textit{Bisimilarity}. In extensional equivalences, only observable behavior is taken into account, without considering the
identity of the processes. This sets bisimilarity apart from stronger graph equivalences like \textit{graph isomorphism}, 
here the (intensional) identity of processes is relevant. The coarsest commonly used equivalence is \textit{trace equivalence}.

- LT-BT spectrum (between them there is a lattice of equivalences ...)
- Wir behandeln bisimilarität hier gesondert wegen dessen bezihung zu HML (HM-Theorem) (s.h. Introduction, doppelung vermeiden).
- example bisimilarity

Informally, we call two processes bisimilar if...\<close>


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