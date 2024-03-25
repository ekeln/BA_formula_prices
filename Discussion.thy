(*<*)
theory Discussion
imports Main
begin
(*>*)
section \<open>Discussion\<close>
subsubsection \<open>Proof Optimizations\<close>
text \<open>The intricacies of \textsf{expr} leads to modal characterizations of the price bounds that contain syntactic features that do not add any expressiveness.
One can assume that formulas are flattened in the sense that conjunctions do not contain other conjunctions as immediate subformulas without loosing any expressiveness.
This would make the modal characterizations of the price bounds much closer to $\mathcal{O}_X$. 
- reuse lemmas?
\<close>
subsubsection \<open>The prices do not distinguish between:\<close>
text \<open>
- finitely branching
- infinitely deep formulas
- other equivalences:
  - completed traces?
  - singleton failures:
    - another dimension to distinguish negative branches of conjunction, similar to expr3, expr4
  - transition system with silent steps:
    2 more dimesions, see (cite) for stab resp branching spectrum\<close>

subsubsection \<open>Is formalization of LTS actually correct (can \<open>'s\<close> index set capture expressiveness?)\<close>

subsubsection \<open>HM-theoreme:\<close>
text \<open>Add machine checkable proofs that modal characterizations correspond to colloquial definitions (relational, refusal sets, ...)\<close>

subsubsection \<open>Spectroscopy Game\<close>
text \<open>(Als anwendung von spektrum)\<close>
end