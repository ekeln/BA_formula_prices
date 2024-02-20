(*<*)
theory Introduction
  imports 
    Pure
begin
(*>*)

chapter \<open>Introduction\<close>
text \<open>In this thesis, I show the correspondence between various equivalences popular in the reactive
systems community and coordinates of a formula price function, as introduced by Benjamin Bisping (citation).
I formalised the concepts and proofs discussed in this thesis in the interactive proof assistant Isabelle (citation).
\\\\
\textit{Reactive systems} are computing systems that continuously interact with their environment, reacting to external stimuli and producing outputs accordingly(Harel).
At a high level of abstraction, they can be seen as a collection of interacting processes. Modeling and verifying these processes is often referred to as \textit{Process Theory}. \\\\

Verification of these systems involves proving statements regarding the behavior of a system model. Often, verification tasks aim to show that a system's observed behavior aligns with its intended behavior.
That requires a criterion of similar behavior, or \textit{semantics of equality}. Depending on the requirements of a particular user, many different such criterions have been defined.
For a subset of processes, namely the class of sequential processes lacking internal behavior, (Glaabbeck) classified many such semantics. 
The processes in this subset can only perform one action at a time. Furthermore, this class is restricted to \textit{concrete} processes; processes in which no internal actions occur.
This classification involved partially ordering them by the relation 'makes strictly more identifications on processes than' (Glabbeeck). The resulting complete lattice is
referred to as the (infinitary) linear-time--branching-time spectrum. \footnote{On Infinity?} 
\footnote{linear time describes identification via the order of events, while branching time captures the branching possibilities in system executions.}
\\\\
more on LT BT spectrum?
\\\\
Systems with this kind of processes can be modeled using labeled transition systems (Kel). An LTS is a triple of a set of processes, or states of the system,
a set of possible actions and a transition relation between a process, an action and another process. The outgoing transitions of each process correspond to the actions the system can perform in that state, 
yielding a subsequent state. In accordance with our restriction to concrete processes, we do not distinguish between different kinds of actions. 
\footnote{A popular notion of identification is internal behavior, LTS capable of modeling internal behavior use a fixed action to express internal behavior. This extension allows for additional semantics that have been investigated, for instance, in (Glabeeck).}
\\\\
In the context of this spectrum, demonstrating that a system model's observed behavior aligns with the behavior of a model of the specification involves 
finding the finest notions of behavioral equivalence that equate them. Special bisimulation games and algorithms capable of answering equivalence questions 
by performing a 'spectroscopy' of the differences between two processes have been developed (Deciding all at once)((accounting for silent steps), evtl hier weglassen oder mention: anderes spektrum)(process equiv as energy games)(A game for lt bt spectr).
These approaches rechart the linear-time--branching-time spectrum using \textit{formula prices} that capture the expressive capabilities of Hennessy-Milner Logic (HML).

This thesis provides a machine-checkable proof that certain price bounds correspond to the modal-logical characterizations of named equivalences. 
More precisely, a formula \<open>\<phi>\<close> is in an observation language $\mathcal{O_X}$ iff its price is within the given price bound.
Concretely, for every expressiveness price bound $e_X$, i derive the sublanguage of Hennessy--Miler logic $\mathcal{O_X}$ and show that a formula \<open>\<phi>\<close> is in $\mathcal{O_X}$ precisely if its price \<open>expr(\<phi>)\<close> is less than or equal to $e_X$.
Then i show that $\mathcal{O_X}$ has exactly the same distinguishing power as the modal-logical characterization of that equivalence.

For the class of sequential processes, that can at most perform one action at a time, and that do not posses internal behavior.
(cite glabbeeck) classified many such semantics by partially ordering them by the relation 'makes strictly more identifications on processes than'. However,
The term \emph{reactive system} (citation) describes computing systems that continuously interact with their environment. Unlike sequential systems, 
the behavior or reactive systems is inherently event-driven and concurrent. They can be modeled by labeled directed graphs called \emph{labeled transition systems} (LTSs) (citation),
where the nodes of an LTS describe the states of a reactive system and the edges describe transitions between those states.


Strucutre:\\
Foundations: LTS, Bismilarity (weil besonders dadurch das es feinste äquivalenz ist,verbindung zu HML(HM Theorem), HML \\
Formula Pricing - capturing expressiveness using formula prices \\
Korrespondenz zwischen koordinaten und äquivalenzen beweise\\
diskussion?\\
appendix?\\

The semantics of reactive systems can be modeled as equivalences, that determine whether or not two systems behave similarly.
In the literature on concurrent systems many different notion of equivalence can be found, the maybe best known being \emph{(strong) bisimilarity}.
Rab van Glabbeek`s \emph{linear-time--branching-spectrum}(citation) ordered some of the most popular in a hierachy of equivalences.
-> New Paper characterizes them different... (HML beschreibung als erstes?!!)


- Reactive Systmes \\
  - modelling (via lts etc) \\
  - Semantics of resysts \\
    - Verification \\
    - different notions of equivalence (because of nondeteminism?) -> van glabbeek \\
    - Different definitions of semantics -> HML/relational/... \\
 --> linear-time--branching-time spectrum understood through properties of HML \\
  --> capture expressiveness capabilities of HML formulas via a function \\
--> Contribution o Paper: The in (citation) introduced expressiveness function 
and its coordinates captures the linear time branching time spectrum.. \\
- Isabelle:\\
  - formalization of concepts, proofs \\
  - what is isabelle \\
  - difference between mathematical concepts and their implementation? \\
\<close>


(*<*)
end
(*>*)
