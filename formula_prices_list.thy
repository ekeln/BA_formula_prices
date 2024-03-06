(*<*)
theory formula_prices_list
  imports 
    HML
    "HOL-Library.Extended_Nat"
begin
(*>*)

section \<open>Price Spectra of Behavioral Equivalences\<close>

text \<open>The linear-time--branching-time spectrum can be represented in terms of HML-expressiveness (s.h. section HML).
(Deciding all at once)(energy games) show how one can think of the amount of HML-expressiveness used by a formula by its \textit{price}.
The equivalences of the spectrum (or their modal-logical characterizations) can then be defined in terms of \textit{price coordinates}, that is
equivalence $X$ is characterized by the HML formulas with prices less then or equal to a \textit{X-price bound} $e_X$.
We use the six dimensions from (energy games) to characterize the notions of equivalence we are interested in (In figure xx oder so umschreiben).
Intuitively, the dimensions can be described as follows:\\
1. Formula modal depth of observations: How many modal operations $\langle \alpha \rangle$ may one pass when descending the syntax tree. (Algebraic laws for nondeterminism and concurrency)(Operational and algebraic semantics of concurrent processes)\\
2. Formula nesting depth of conjunctions: How often may one pass a conjunction?\\
3. Maximal modal depth of deepest positive clauses in conjunctions\\
4. Maximal modal depth of other positive clauses in conjunctions\\
5. Maximal modal depth of negative clauses in conjunctions\\
6. Formula nesting depth of negations\\\<close>

subsubsection \<open>Definition 2.3.1 (Formula Prices)\<close>
text \<open>
The expressiveness price $\textsf{expr} : \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \infty})^6$ of a formula interpreted as $6 \times 1$-dimensional vectors is defined recursively by:

\[
\text{expr}(\langle a \rangle \varphi) :=
\begin{pmatrix}
1 + \text{expr}_1(\varphi) \\
\text{expr}_2(\varphi) \\
\text{expr}_3(\varphi) \\
\text{expr}_4(\varphi) \\
\text{expr}_5(\varphi) \\
\text{expr}_6(\varphi) \\
\end{pmatrix}
\]

\[
\text{expr}(\neg \varphi) := 
\begin{pmatrix}
\text{expr}_1(\varphi) \\
\text{expr}_2(\varphi) \\
\text{expr}_3(\varphi) \\
\text{expr}_4(\varphi) \\
\text{expr}_5(\varphi) \\
1 + \text{expr}_6(\varphi) \\
\end{pmatrix}
\]

\[
\text{expr}\left( \bigwedge_{i \in I} \psi_i \right) := \sup(\{
\begin{pmatrix}
0 \\
1 + \sup_{i \in I} \text{expr}_2(\psi_i) \\
\sup_{i \in \text{Pos}} \text{expr}_1(\psi_i) \\
\sup_{i \in \text{Pos} \backslash \mathcal{R}} \text{expr}_1(\psi_i) \\
\sup_{i \in \text{Neg}} \text{expr}_1(\psi_i) \\
0 \\
\end{pmatrix} \} \cup \{\textsf{expr}(\psi_i) | i \in I\} 
\]

where:

$\textit{Neg} := \{i \in I \, | \, \exists \varphi'_i. \psi_i = \neg \varphi'_i\}$

$\textit{Pos} := I \setminus \text{Neg}$

$\mathcal{R} := \left\{
\begin{aligned}
&\varnothing \text{ if } \textit{Pos} = \varnothing, \\
&\{ r \} \text{ for some } r \in \textit{Pos} \text{ where } \text{expr}_1(\psi_r) \text{ maximal for \textit{Pos}}
\end{aligned}
\right.$

Our Isabelle definition of HML makes it very easy to derive the sets Pos and Neg, by \<open>\<Phi> ` I\<close> and \<open>\<Phi> ` J\<close> respectively.

Remark: We deviate from the definition in (cite Bisp) by including infinity in the domain of the function due to infinite branching conjunctions. Supremum over infinite set wird zu unendlich.\<close>

text \<open>To better argue about the function we define each dimension as a seperate function.\<close>

text \<open>Vlt als erstes: modaltiefe als beispiel für observation expressiveness von formel, mit isabelle definition,
dann pos\_r definition,
direct\_expr definition,
einzelne dimensionen,
lemma direct\_expr = expr...\<close>

text \<open>Formally, the \textit{modal depth} $\textsf{expr}_1$ of a formula $\varphi$ is defined recursively by:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    &\text{then } \textsf{expr}_1(\varphi) = 1 + \textsf{expr}_1(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_1, \psi_2, \ldots \} \\
    &\text{then } \textsf{expr}_1(\varphi) = \sup(\textsf{expr}_1(\psi_i)) \\
    \text{if } \psi &= \neg \varphi \\
    &\text{then } \textsf{expr}_1(\psi) = \textsf{expr}_1(\varphi)
\end{align*}
\<close>

primrec expr_1 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_1_tt: \<open>expr_1 TT = 0\<close> |
expr_1_conj: \<open>expr_1 (hml_conj I J \<Phi>) = Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J)\<close> |
expr_1_pos: \<open>expr_1 (hml_pos \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

text \<open>With the help of the modal depth we can derive Pos$\backslash$R in Isabelle:\<close>

fun pos_r :: "('a, 's)hml set \<Rightarrow> ('a, 's)hml set"
  where
"pos_r xs = (
let max_val = (Sup (expr_1 ` xs)); 
  max_elem = (SOME \<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val);
  xs_new = xs - {max_elem}
in xs_new)"

text \<open>Now we can directly define the expressiveness function as \<open>direct_expr\<close>.\<close>

function direct_expr :: "('a, 's)hml \<Rightarrow> enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat" where
  "direct_expr TT = (0, 1, 0, 0, 0, 0)" |
  "direct_expr (hml_pos \<alpha> \<phi>) = (1 + fst (direct_expr \<phi>), 
                                fst (snd (direct_expr \<phi>)), 
                                fst (snd (snd (direct_expr \<phi>))), 
                                fst (snd (snd (snd (direct_expr \<phi>)))), 
                                fst (snd (snd (snd (snd (direct_expr \<phi>))))), 
                                snd (snd (snd (snd (snd (direct_expr \<phi>))))))" |
  "direct_expr (hml_conj I J \<Phi>) = (Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> direct_expr \<circ> \<Phi>) ` J), 
                                    1 + Sup ((fst \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J), 
(Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)),
(Sup (((fst \<circ> direct_expr) ` (pos_r (\<Phi> ` I)))  \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)),  
(Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J \<union> (fst \<circ> direct_expr \<circ> \<Phi>) ` J)), 
(Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J))))"
  by ((meson hml.exhaust), simp+)

text \<open>In order to demonstrate termination of the function, it is necessary to establish that each sequence of recursive function calls reaches a base case. 
This is accomplished by proving that the relation between process-formula pairs, as defined recursively by the function, is contained within a well-founded relation. 
A relation \( R \subset X \times X \) is considered well-founded if every non-empty subset \( X' \subset X \) contains a minimal element \( m \) such that \( (x, m) \notin R \) for all \( x \in X' \). 
A key property of well-founded relations is that all descending chains \( (x_0, x_1, x_2, \ldots) \) (where \( (x_i, x_{i+1}) \in R \)) originating from any element \( x_0 \in X \) are finite. 
Consequently, this ensures that each sequence of recursive invocations terminates after a finite number of steps. 

These proofs were inspired by the Isabelle formalizations presented in [WEP+16].
\<close>

inductive_set HML_wf_rel :: "(('a, 's)hml) rel" where
"\<phi> = \<Phi> i \<and> i \<in> (I \<union> J) \<Longrightarrow> (\<phi>, (hml_conj I J \<Phi>)) \<in> HML_wf_rel" |
"(\<phi>, (hml_pos \<alpha> \<phi>)) \<in> HML_wf_rel"

lemma HML_wf_rel_is_wf: \<open>wf HML_wf_rel\<close>
  unfolding wf_def
proof safe
  fix P
  assume assm: "\<forall>x. (\<forall>y. (y, x) \<in> HML_wf_rel \<longrightarrow> P y) \<longrightarrow> P x"
  show "\<And>\<phi>. P \<phi>" proof-
    fix \<phi>
    show "P \<phi>" proof(induction \<phi>)
    case TT
    then show ?case 
      using HML_wf_rel.cases assm by blast
  next
    case (hml_pos x1 \<phi>)
    then show ?case 
      using HML_wf_rel.cases hml.inject hml.simps assm 
      by (smt (verit, best))
  next
    case (hml_conj x1 x2 x3)
    then show ?case 
      using assm
      by (metis HML_wf_rel.cases hml.inject(2) hml.simps(8) rangeI)
    qed
  qed
qed

lemma pos_r_subs: "pos_r (\<Phi> ` I) \<subseteq> (\<Phi> ` I)"
  by auto

termination
  apply rule
  using HML_wf_rel_is_wf HML_wf_rel.simps Un_iff pos_r_subs by fastforce+

text \<open>The other functions are also defined recursively:

Formula nesting depth of conjunctions $\textsf{expr}_2$:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_2(\varphi) = \textsf{expr}_2(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{\psi_i \} \\
    & \text{then } \textsf{expr}_2(\varphi) = 1 + \sup(\textsf{expr}_2(\psi_i)) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_2(\psi) = \textsf{expr}_2(\varphi)
\end{align*}
\<close>

primrec expr_2 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_2_tt: \<open>expr_2 TT = 1\<close> |
expr_2_conj: \<open>expr_2 (hml_conj I J \<Phi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)\<close> |
expr_2_pos: \<open>expr_2 (hml_pos \<alpha> \<phi>) = expr_2 \<phi>\<close>

text \<open>Maximal modal depth of the deepest positive branch $\textsf{expr}_3$:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{md}(\varphi) = \textsf{md}(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{md}(\varphi) = \sup(\{\textsf{expr}_1(\psi_i) | i \in \text{Pos}\} \cup \{\textsf{expr}_3(\psi_i) | i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_3(\psi) = \textsf{expr}_3(\varphi)
\end{align*}
\<close>

primrec expr_3 :: "('a, 's) hml \<Rightarrow> enat"
  where
expr_3_tt: \<open>expr_3 TT = 0\<close> |
 expr_3_pos: \<open>expr_3 (hml_pos \<alpha> \<phi>) = expr_3 \<phi>\<close> | 
expr_3_conj: \<open>expr_3 (hml_conj I J \<Phi>) = (Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J))\<close>

text \<open>Maximal modal depth of other positive clauses in conjunctions $\textsf{expr}_4$:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_4(\varphi) = \textsf{expr}_4(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{\ \psi_i \} \\
    & \text{then } \text{md}(\varphi) = \sup(\{\textsf{expr}_1(\psi_i)|i\in\text{Pos}\backslash \mathcal{R}\}\cup\{\textsf{expr}_4(\psi_i) | i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_4(\psi) = \textsf{expr}_4(\varphi)
\end{align*}
\<close>

primrec expr_4 :: "('a, 's)hml \<Rightarrow> enat" 
  where
expr_4_tt: "expr_4 TT = 0" |
expr_4_pos: "expr_4 (hml_pos a \<phi>) = expr_4 \<phi>" |
expr_4_conj: "expr_4 (hml_conj I J \<Phi>) = Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J)"

text \<open>Maximal modal depth of negative clauses in conjunctions $\textsf{expr}_5$:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_5(\varphi) = \textsf{expr}_5(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{expr}_5(\varphi) = \sup(\{\textsf{expr}_1(\psi_i)| i \in \text{Neg}\}\cup \{\textsf{expr}_5(\psi_i)|i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_5(\psi) = \textsf{expr}_5(\varphi)
\end{align*}
\<close>

primrec expr_5 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_5_tt: \<open>expr_5 TT = 0\<close> |
expr_5_pos:\<open>expr_5 (hml_pos \<alpha> \<phi>) = expr_5 \<phi>\<close>|
expr_5_conj: \<open>expr_5 (hml_conj I J \<Phi>) = 
(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J))\<close>

text \<open>Formula nesting depth of negations $\textsf{expr}_6$:

\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_6(\varphi) = \textsf{expr}_6(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{expr}_6(\varphi) = \sup(\{\textsf{expr}_6(\psi_i)| i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_6(\psi) = 1 + \textsf{expr}_6(\varphi)
\end{align*}
\<close>

primrec expr_6 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_6_tt: \<open>expr_6 TT = 0\<close> |
expr_6_pos: \<open>expr_6 (hml_pos \<alpha> \<phi>) = expr_6 \<phi>\<close>|
expr_6_conj: \<open>expr_6 (hml_conj I J \<Phi>) = 
(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J)))\<close>

text \<open>That leaves us with a definition \textsf{expr} of the expressiveness function that is easier to use.\<close>

fun expr :: "('a, 's)hml \<Rightarrow> enat \<times> enat \<times> enat \<times>  enat \<times> enat \<times> enat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>

text \<open>We show that \<open>direct_expr\<close> and \<open>expr\<close> are the same:\<close>


(*<*)
lemma expr_6_direct_expr_eq:
  assumes "\<And>x. x \<in> \<Phi> ` I \<Longrightarrow> expr_6 x = snd (snd (snd (snd (snd (direct_expr x)))))"
  shows "(expr_6 \<circ> \<Phi>) ` I = (snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I"
proof -
  have "(expr_6 \<circ> \<Phi>) ` I = (\<lambda>x. snd (snd (snd (snd (snd (direct_expr (\<Phi> x))))))) ` I"
    by (simp add: assms)
  also have "... = (snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I"
    by auto
  finally show ?thesis .
qed

lemma expr_6_eSuc_eq:
  assumes "\<And>x. x \<in> \<Phi> ` J \<Longrightarrow> eSuc (expr_6 x) = eSuc (snd (snd (snd (snd (snd (direct_expr x))))))"
  shows "((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) = ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
proof-
  have "((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) = (\<lambda>x. eSuc (snd (snd (snd (snd (snd (direct_expr (\<Phi> x)))))))) ` J"
    using assms by force
  also have "... = ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
    by auto
  finally show ?thesis.
qed

lemma expr_5_dir_eq:
  assumes "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_5 x = fst (snd (snd (snd (snd (direct_expr x)))))"
  shows "((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J) = 
          ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
proof-
  have "((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J) = (\<lambda>x. fst (snd (snd (snd (snd (direct_expr (\<Phi> x))))))) ` (I \<union> J)"
    using assms 
    by auto
  also have "... = (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` (I \<union> J)"
    by auto 
  also have "... =  ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
    by blast
  finally show ?thesis.
qed
(*>*)

lemma 
  shows "expr \<phi> = direct_expr \<phi>"
proof(induction \<phi>)
  case TT
  have "expr TT = (0, 1, 0, 0, 0, 0)" using expr.simps expr_1.simps(1) expr_2.simps(1) expr_3.simps(1) expr_4.simps(1) expr_5.simps(1) expr_6.simps(1)
    by force
  then show ?case using direct_expr.simps(1) 
    by force
next
  case (hml_pos \<alpha> \<phi>)
  hence IH: "(expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>) =
                                (fst (direct_expr \<phi>), 
                                fst (snd (direct_expr \<phi>)), 
                                fst (snd (snd (direct_expr \<phi>))), 
                                fst (snd (snd (snd (direct_expr \<phi>)))), 
                                fst (snd (snd (snd (snd (direct_expr \<phi>))))), 
                                snd (snd (snd (snd (snd (direct_expr \<phi>))))))"
    by auto
  have expr: "expr (hml_pos \<alpha> \<phi>) = (1 + (expr_1 \<phi>), expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)"
    using expr.simps expr_1.simps expr_2.simps expr_3.simps expr_4.simps expr_5.simps expr_6.simps
    by simp
  have "direct_expr (hml_pos \<alpha> \<phi>) = 
                                (1 + fst (direct_expr \<phi>), 
                                fst (snd (direct_expr \<phi>)), 
                                fst (snd (snd (direct_expr \<phi>))), 
                                fst (snd (snd (snd (direct_expr \<phi>)))), 
                                fst (snd (snd (snd (snd (direct_expr \<phi>))))), 
                                snd (snd (snd (snd (snd (direct_expr \<phi>))))))"
    using direct_expr.simps(2) by auto
  then show ?case using expr IH by force
next
  case (hml_conj I J \<Phi>)
  hence IH: "\<forall>\<phi> \<in> \<Phi> ` I. (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>) =
                                (fst (direct_expr \<phi>), 
                                fst (snd (direct_expr \<phi>)), 
                                fst (snd (snd (direct_expr \<phi>))), 
                                fst (snd (snd (snd (direct_expr \<phi>)))), 
                                fst (snd (snd (snd (snd (direct_expr \<phi>))))), 
                                snd (snd (snd (snd (snd (direct_expr \<phi>))))))"
        "\<forall>\<phi> \<in> \<Phi> ` J. (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>) =
                                (fst (direct_expr \<phi>), 
                                fst (snd (direct_expr \<phi>)), 
                                fst (snd (snd (direct_expr \<phi>))), 
                                fst (snd (snd (snd (direct_expr \<phi>)))), 
                                fst (snd (snd (snd (snd (direct_expr \<phi>))))), 
                                snd (snd (snd (snd (snd (direct_expr \<phi>))))))"
    by simp+
  hence e1: "Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J) = Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> direct_expr \<circ> \<Phi>) ` J)"
    by (smt (verit, best) Pair_inject comp_apply image_cong image_eqI)
  have e2: "1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J) = 1 + Sup ((fst \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
    using IH Sup_le_iff 
    by (smt (verit) Pair_inject comp_apply image_cong image_eqI)
  have e3: "(Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J)) =
        (Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J))"
    using IH Sup_le_iff 
    by (smt (verit, ccfv_SIG) Pair_inject comp_apply image_comp image_cong)
  have e4: "Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) =
        (Sup (((fst \<circ> direct_expr) ` (pos_r (\<Phi> ` I)))  \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J))"
  proof-
    have sup_pos_r: "\<forall>x \<in> pos_r (\<Phi> ` I). expr_1 x = (fst \<circ> direct_expr) x"
      using IH 
      by (metis (no_types, lifting) Diff_iff Pair_inject comp_apply pos_r.simps)
    hence "Sup (expr_1 ` pos_r (\<Phi> ` I)) = Sup ((fst \<circ> direct_expr) ` pos_r (\<Phi> ` I))"
      by (meson SUP_cong)
    have "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_4 x = fst (snd (snd (snd (direct_expr x))))"
      using IH
      by blast+
    hence "Sup ((expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J) = 
          Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union>
          (fst \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
      using SUP_cong by auto
    then show ?thesis using sup_pos_r 
      by (metis (no_types, lifting) Sup_union_distrib image_cong inf_sup_aci(6))
  qed
  have e5: "(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J)) =
  (Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J \<union> (fst \<circ> direct_expr \<circ> \<Phi>) ` J))"
    using IH
  proof-
    have fa_e5: "\<forall>x \<in> \<Phi> ` (I \<union> J). expr_5 x = fst (snd (snd (snd (snd (direct_expr x)))))"
          "\<forall>x \<in> \<Phi> ` J. expr_1 x = fst (direct_expr x)"
      using IH 
      by blast+
    hence "Sup ((expr_1 \<circ> \<Phi>) ` J )= Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` J)" 
      by fastforce
    have "Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J) = 
          Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> (fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
      using expr_5_dir_eq fa_e5 by force
    then show ?thesis 
      using \<open>Sup ((expr_1 \<circ> \<Phi>) ` J )= Sup ((fst \<circ> direct_expr \<circ> \<Phi>) ` J)\<close> 
      by (simp add: Sup_union_distrib)
  qed

  have e6: "(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J))) =
        (Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)))"
  proof-
    have "\<forall>x \<in> \<Phi> ` I. expr_6 x = snd (snd (snd (snd (snd (direct_expr x)))))"
          "\<forall>x \<in> \<Phi> ` J. expr_6 x = snd (snd (snd (snd (snd (direct_expr x)))))"
      using IH by blast+
    from this(1) have "((expr_6 \<circ> \<Phi>) ` I) = ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I)"
      using expr_6_direct_expr_eq by force
    hence "Sup ((expr_6 \<circ> \<Phi>) ` I) = Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I)"
      by presburger 
    have "\<forall>x \<in> \<Phi> ` J. eSuc (expr_6 x) = eSuc (snd (snd (snd (snd (snd (direct_expr x))))))"
      using \<open>\<forall>x \<in> \<Phi> ` J. expr_6 x = snd (snd (snd (snd (snd (direct_expr x)))))\<close> by simp
    hence "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) = Sup ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
      using expr_6_eSuc_eq by auto
    then show ?thesis using \<open>Sup ((expr_6 \<circ> \<Phi>) ` I) = Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I)\<close>
      by (simp add: Sup_union_distrib)
  qed

  then show ?case using e1 e2 e3 e4 e5 e6 by simp
qed

text \<open>Prices are compared component wise, i.e., $(e_1, \ldots e_6) \leq (f_1 \ldots f_6)$ iff $e_i \leq f_i$ for each $i$.\<close>

fun less_eq_t :: "(enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) \<Rightarrow> bool"
  where
"less_eq_t (n1, n2, n3, n4, n5, n6) (i1, i2, i3, i4, i5, i6) =
    (n1 \<le> i1 \<and> n2 \<le> i2 \<and> n3 \<le> i3 \<and> n4 \<le> i4 \<and> n5 \<le> i5 \<and> n6 \<le> i6)"

definition less where
"less x y \<equiv> less_eq_t x y \<and> \<not> (less_eq_t y x)"

(*<*)
definition e_sup :: "(enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat) set \<Rightarrow> (enat \<times> enat \<times> enat \<times> enat \<times> enat \<times> enat)"
  where
"e_sup S \<equiv> ((Sup (fst ` S)), (Sup ((fst \<circ> snd) ` S)), (Sup ((fst \<circ> snd \<circ> snd) ` S)), 
(Sup ((fst \<circ> snd \<circ> snd \<circ> snd) ` S)), (Sup ((fst \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` S)), 
(Sup ((snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd) ` S)))"
(*>*)

text \<open>\textbf{Proposition} The expressiveness function is monotonic.\<close>

lemma mon_pos:
  fixes n1 and n2 and n3 and n4::enat and n5 and n6 and \<alpha>
  assumes A1: "less_eq_t (expr (hml_pos \<alpha> \<phi>)) (n1, n2, n3, n4, n5, n6)"
  shows "less_eq_t (expr \<phi>) (n1, n2, n3, n4, n5, n6)" 
proof-
  from A1 have E_rest: 
"expr_2 \<phi> \<le> n2 \<and> expr_3 \<phi> \<le> n3 \<and> expr_4 \<phi> \<le> n4 \<and> expr_5 \<phi> \<le> n5 \<and>expr_6 \<phi> \<le> n6" 
    using expr.simps 
    by simp
  from A1 have "1 + expr_1 \<phi> \<le> n1"
    using expr_1.simps(1) by simp
  hence "expr_1 \<phi> \<le> n1" 
    using ile_eSuc plus_1_eSuc(1) dual_order.trans by fastforce
  with E_rest show ?thesis by simp
qed

lemma mon_conj:
  fixes n1 and n2 and n3 and n4 and n5 and n6 and xs and ys
  assumes "less_eq_t (expr (hml_conj I J \<Phi>)) (n1, n2, n3, n4, n5, n6)"
  shows "(\<forall>x \<in> (\<Phi> ` I). less_eq_t (expr x) (n1, n2, n3, n4, n5, n6))" 
"(\<forall>y \<in> (\<Phi> ` J). less_eq_t (expr y) (n1, n2, n3, n4, n5, n6))"
proof-
  have e1_eq: "expr_1 (hml_conj I J \<Phi>) = Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J)"
    using expr_1_conj by blast
  have e2_eq: "expr_2 (hml_conj I J \<Phi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)"
    using expr_2_conj by blast
  have e3_eq: "expr_3 (hml_conj I J \<Phi>) = (Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J))"
    using expr_3_conj by blast
  have e4_eq: "expr_4 (hml_conj I J \<Phi>) = Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J)"
    using expr_4_conj by blast
  have e5_eq: "expr_5 (hml_conj I J \<Phi>) = (Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J))"
    using expr_5_conj by blast
  have e6_eq: "expr_6 (hml_conj I J \<Phi>) = (Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J)))"
    using expr_6_conj by blast

  have e1_le: "expr_1 (hml_conj I J \<Phi>) \<le> n1" and
e2_le: "expr_2 (hml_conj I J \<Phi>) \<le> n2" and
e3_le: "expr_3 (hml_conj I J \<Phi>) \<le> n3" and
e4_le: "expr_4 (hml_conj I J \<Phi>) \<le> n4" and
e5_le: "expr_5 (hml_conj I J \<Phi>) \<le> n5" and
e6_le: "expr_6 (hml_conj I J \<Phi>) \<le> n6"
    using less_eq_t.simps expr.simps assms
    by metis+

  from e1_eq e1_le have e1_pos: "Sup ((expr_1 \<circ> \<Phi>) ` I) \<le> n1"
and e1_neg: "Sup ((expr_1 \<circ> \<Phi>) ` J) \<le> n1"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by metis+
  hence e1_le_pos: "\<forall>x\<in>\<Phi> ` I. expr_1 x \<le> n1"
and e1_le_neg: "\<forall>y\<in>\<Phi> ` J. expr_1 y \<le> n1"
    by (simp add: Sup_le_iff)+

  from e2_eq e2_le have e2_pos: "Sup ((expr_2 \<circ> \<Phi>) ` I) <= n2"
and e2_neg: "Sup ((expr_2 \<circ> \<Phi>) ` J) \<le> n2"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (metis (no_types, lifting) dual_order.trans ile_eSuc plus_1_eSuc(1))+

  from e3_eq e3_le have e3_pos: "Sup ((expr_3 \<circ> \<Phi>) ` I) <= n3"
and e3_neg: "Sup ((expr_3 \<circ> \<Phi>) ` J) <= n3"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e4_eq e4_le have e4_pos: "Sup ((expr_4 \<circ> \<Phi>) ` I) \<le> n4"
and e4_neg: "Sup ((expr_4 \<circ> \<Phi>) ` J) \<le> n4"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e5_eq e5_le have e5_pos: "Sup ((expr_5 \<circ> \<Phi>) ` I) <= n5"
and e5_neg: "Sup ((expr_5 \<circ> \<Phi>) ` J) <= n5"
    using Sup_union_distrib le_sup_iff sup_enat_def
    by (simp add: Sup_le_iff)+

  from e6_eq e6_le have e6_pos: "Sup ((expr_6 \<circ> \<Phi>) ` I) \<le> n6"
and e6_neg: "Sup ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) \<le> n6"
    using Sup_union_distrib le_sup_iff sup_enat_def
     apply (simp add: Sup_le_iff)
    using Sup_union_distrib le_sup_iff sup_enat_def e6_eq e6_le
    by metis

  from e6_neg have e6_neg: "Sup ((expr_6 \<circ> \<Phi>) ` J) \<le> n6"
    using Sup_enat_def eSuc_def
    by (metis dual_order.trans eSuc_Sup i0_lb ile_eSuc image_comp)


  show "\<forall>x\<in>\<Phi> ` I. less_eq_t (expr x) (n1, n2, n3, n4, n5, n6)"
    using e1_pos e2_pos e3_pos e4_pos e5_pos e6_pos
expr.simps less_eq_t.simps
    by (simp add: Sup_le_iff)

  show "\<forall>y\<in>\<Phi> ` J. less_eq_t (expr y) (n1, n2, n3, n4, n5, n6)"
    using e1_neg e2_neg e3_neg e4_neg e5_neg e6_neg
expr.simps less_eq_t.simps
    by (simp add: Sup_le_iff)
qed

(*<*)
end
(*>*)