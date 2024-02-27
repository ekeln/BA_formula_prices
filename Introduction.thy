(*<*)
theory Introduction
  imports 
    Pure
begin
(*>*)

chapter \<open>Introduction\<close>
text \<open>In this thesis, I show the correspondence between various equivalences popular in the reactive
systems community and coordinates of a formula price function, as introduced by Bisping in \cite{bisping2023process}. I formalized the concepts and proofs discussed in this thesis in the interactive proof assistant Isabelle.

\textit{Reactive systems} are computing systems that continuously interact with their environment, reacting to external stimuli and producing outputs accordingly \cite{harel85}.
At a high level of abstraction, these systems can be seen as collections of interacting processes, where each process represents a state or configuration of the system. 
Labeled Transition Systems (LTS) \cite{keller76} provide a formal framework for modeling and analyzing the behavior of reactive systems. Roughly, an LTS is a labeled directed graph, whose nodes denote the processes
and whose edges correspond to transitions between those processes (or states).

Verification of these systems involves proving statements regarding the behavior of such a system model. Often, verification tasks aim to show that a system's observed behavior aligns with its intended behavior.
That requires a criterion of what constitutes similar behavior on LTS, commonly referred to as the \textit{semantics of equality} of processes. Depending on the requirements of a particular user, many different such criterions have been defined.
For a subset of processes, namely the class of concrete sequential processes, \cite{GLABBEEK20013} classified many such semantics. 
\textit{Sequential} means that the processes can only perform one action at a time. \textit{Concrete} processes are processes in which no internal actions occur, meaning that it exclusively captures the system's interactions with its environment.
In such LTS, every transition represents an observable event or action between the system and its environment.
The classification in \cite{GLABBEEK20013} involved partially ordering many of these semantics by the relation 'makes strictly more identifications on processes than'. The resulting lattice is
known as the (infinitary) linear-time--branching-time spectrum \footnote{On Infinity?} 
\footnote{Linear time describes identification via the order of events, while branching time captures the branching possibilities in system executions.}.
One way to characterize the behavior of LTS is through the use of modal logics. Formulas of a logic can be seen as describing certain properties of states within an LTS. A commonly used modal logic is Hennessy-Milner logic (HML) \cite{hm85}. 
Equivalence in terms of HML is determined by whether processes satisfy the same set of formulas. The linear-time--branching-time spectrum can be recharted in terms of the subset relation between these modal-logical characterizations. 
 \<close>
(*<*)
text \<open>
Systems with this kind of processes can be modeled using labeled transition systems (Kel). An LTS is a triple of a set of processes, or states of the system,
a set of possible actions and a transition relation between a process, an action and another process. The outgoing transitions of each process correspond to the actions the system can perform in that state, 
yielding a subsequent state. In accordance with our restriction to concrete processes, we do not distinguish between different kinds of actions. 
\footnote{A popular notion of identification is internal behavior, LTS capable of modeling internal behavior use a fixed action to express internal behavior. This extension allows for additional semantics that have been investigated, for instance, in (Glabeeck).}

In LTS verwenden? überflüssig?\<close>
(*>*)
text \<open>
In the context of this spectrum, demonstrating that a system model's observed behavior aligns with the behavior of a model of the specification can be done by 
finding the finest notions of behavioral equivalence that equate them. Special bisimulation games and algorithms capable of answering equivalence questions 
by performing a 'spectroscopy' of the differences between two processes have been developed \cite{bisping2022deciding}\cite{bisping2023process}.
These approaches rechart the linear-time--branching-time spectrum using an expressiveness function that assigns a \textit{formula price} to every formula. 
This price is supposed to capture the expressive capabilities of this particular formula. However, to be sure that these characterizations really capture the desired equivalences one has to perform the proofs. 
\<close>

text \<open>
\begin{figure}[htbp]
    \centering
\begin{tikzpicture}[auto,node distance=3.2cm] % Adjusted node distance
  \node[align=center] (B) {Bisimulation B\\$(\infty, \infty, \infty, \infty, \infty, \infty)$};
  \node[align=center, below of=B] (2S) {2-nested-simulation 2S};
  \node[align=center, below left of=2S] (RS) {ready simulation RS};
  \node[align=center, below right of=RS] (RT) {readiness traces RT};
  \node[align=center] (PF) at (6,-8) {possible futures PF};
  \node[align=center, below left of=RT] (FT) {failure traces FT};
  \node[align=center, left of=FT] (S) {simulation S};
  \node[align=center, below right of=RT] (R) {readiness R};
  \node[align=center, below left of=R] (RV) {revivals RV};
  \node[align=center] (IF) at (5,-12) {impossible futures IF};
  \node[align=center, below right of=RV] (F) {failures F};
  \node[align=center, below left of=F] (T) {traces T};

  
  \draw[-] (B) -- node[above] {} (2S);
  \draw[-] (2S) -- node[left] {} (RS);
  \draw[-] (2S) -- node[right] {} (PF);
  \draw[-] (RS) -- node[left] {} (S);
  \draw[-] (RS) -- node[left] {} (RT);
  \draw[-] (PF) -- node[left] {} (IF);
  \draw[-] (RT) -- node[left] {} (FT);
  \draw[-] (RT) -- node[left] {} (R);
  \draw[-] (FT) -- node[left] {} (RV);
  \draw[-] (R) -- node[left] {} (RV);
  \draw[-] (RV) -- node[left] {} (F);
  \draw[-] (IF) -- node[left] {} (F);
  \draw[-] (F) -- node[left] {} (T);
  \draw[-] (S) -- node[left] {} (T);
\end{tikzpicture}
\caption{TEEEEEEEEEEEEEEEEEEST}
    \label{fig:your_label}
\end{figure}\<close>

subsubsection \<open>Contributions\<close>
text \<open>
This thesis provides a machine-checkable proof that the price bounds of the expressiveness function $\textsf{expr}$ of \cite{bisping2023process} correspond to the modal-logical characterizations of named equivalences. 
More precisely, we consider a formula $\varphi$ to be in an observation language $\mathcal{O}_X$ iff its price is within the given price bound.
For every expressiveness price bound $e_X$, we derive the sublanguage of Hennessy--Miler logic $\mathcal{O}_X$ and show that a formula $\varphi$ is in $\mathcal{O}_X$ precisely if its price \<open>expr(\<phi>)\<close> is less than or equal to $e_X$.
Then we show that $\mathcal{O}_X$ has exactly the same distinguishing power as the modal-logical characterization of that equivalence.
In (ref Foundations (chapter 2)) we discuss and introduce formal definitions of LTSs, Hennessy-Milner logic and the expressiveness function $\textsf{expr}$, in (ref The Correspondances?! name!) we perform
the proofs for the standard notions of equivalence, i.e. the equivalences of (ref Figure 1). Namely for trace-, failures-, failure-trace-, readiness-, ready-trace-, revivals-, possible-futures-, impossible-futures-, simulation-, ready-simulation-, 2-nested-simulation- and bisimulation semantics.
All the main concepts and proofs have been formalized and conducted using the interactive proof assistant Isabelle. More information on Isabelle can be found in (appendix?).
We tried to present Isabelle implementations directly after their corresponding mathematical definitions.
The mathematical definitions are marked as 'definitions' and presented in standard text format. Their corresponding Isabelle implementations
are presented right after, distinguished by their \<open>monospaced font\<close> and \textcolor{RoyalBlue}{colored} \textcolor{ForestGreen}{syntax} \textcolor{Cerulean}{highlighting}.
However, for readability purposes, a majority of the Isabelle proofs are hidden and replaced by \<open>\<proof>\<close> and some lemmas excluded. The whole Isabelle code and a web version of this thesis can be found on Github\footnote{\textcolor{red}{Link!!!}}.
\<close>
(*Strucutre of Thesis:\\
Foundations: LTS, Bismilarity (weil besonders dadurch das es feinste äquivalenz ist,verbindung zu HML(HM Theorem), HML, Price spectra \\
Formula Pricing - capturing expressiveness using formula prices \\
Korrespondenz zwischen koordinaten und äquivalenzen beweise\\
diskussion?\\
appendix?\\

and its coordinates captures the linear time branching time spectrum.. \\
- Isabelle:\\
  - formalization of concepts, proofs \\
  - what is isabelle \\
  - difference between mathematical concepts and their implementation? \\*)



(*<*)
end
(*>*)
