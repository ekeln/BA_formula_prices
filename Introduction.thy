(*<*)
theory Introduction
  imports 
    Pure
begin
(*>*)

chapter \<open>Introduction\<close>
text \<open>In this thesis, I show the corrspondence between various equivalences popular in the reactive
systems community and coordinates of a price function, as introduced by Benjamin Bisping (citation).
I formalised the concepts and proofs discussed in this thesis in the interactive proof assistant Isabelle (citation).

The term \emph{reactive system} (citation) describes computing systems that continously interact with their environment. Unlike sequential systems, 
the behavior or reactive systems is inherently event-driven and concurrent. They can be modeled by labeled directed graphs called \emph{labeled transition systems} (LTSs) (citation),
where the nodes of an LTS describe the states of a reactive system and the edges describe transitions between those states.

The semantics of reactive systems can be modeled as equivalences, that determine wether or not two systems behave similarly.
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
