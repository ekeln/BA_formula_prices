(*<*)
theory formula_prices_list
  imports 
    HML
    "HOL-Library.Extended_Nat"
begin
(*>*)

section \<open>Price Spectra of Behavioral Equivalences\<close>

text \<open>\cite{bisping2023process, bisping2022deciding} use a pricing system to measure the amount of HML-expressiveness used by a formula. By assigning an expressiveness price to each formula, the authors create a price lattice that allows for comparing distinguishing power of different formulas, where lower prices indicate less distinguishing power. This allows for a new way of defining HML-subsets. Instead of bounding the subsets by the structure of the included formulas, they are defined as sets of formulas whose prices are less than or equal to a given expressiveness price bound, or \textit{price coordinates}.
The value of each dimension of these price coordinates constrains different syntactic features of the formulas. The authors derive the linear-time--branching-time spectrum by assigning a price coordinate to every equivalence in the spectrum, see \cref{fig:1_1}. In this section, we introduce the definition of the expressiveness price function of (\cite{bisping2023process}, definition 5) and how that function is used to chart the spectrum.\<close>

text \<open>Unlike \cite{bisping2023process}, we define the price for every dimension $i$ as a seperate function, $\textsf{expr}_i : \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \{\infty\}})$ and combine them to the expressiveness function, $\textsf{expr} : \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \{\infty\}})^6$. Each function inductively traverses the syntax tree of a formula and increases its value when encountering the respective syntax feature.\<close>

subsubsection \<open>Definition 2.3.1 (Formula Prices)\<close>
text \<open>\textit{
(\textcolor{red}{1}) The \textnormal{modal depth} $\textsf{expr}_1$ measures the nesting depth of observations within a formula: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:}
\textit{
\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    &\text{then } \textsf{expr}_1(\varphi) = 1 + \textsf{expr}_1(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_1, \psi_2, \ldots \} \\
    &\text{then } \textsf{expr}_1(\varphi) = \sup(\textsf{expr}_1(\psi_i)) \\
    \text{if } \psi &= \neg \varphi \\
    &\text{then } \textsf{expr}_1(\psi) = \textsf{expr}_1(\varphi)
\end{align*}
}


\textit{(\textcolor{orange}{2}) The \textnormal{nesting depth of conjunctions} $\textsf{expr}_2$ measures the maximal number of conjunctions that are nested inside one another in a formula: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:}
\textit{
\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_2(\varphi) = \textsf{expr}_2(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{\psi_i \} \\
    & \text{then } \textsf{expr}_2(\varphi) = 1 + \sup(\textsf{expr}_2(\psi_i)) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_2(\psi) = \textsf{expr}_2(\varphi)
\end{align*}
}

\textit{(\textcolor{myyellow}{3}) The \textnormal{maximal modal depth of deepest positive clauses in conjunctions} $\textsf{expr}_3$ measures the deepest modal depth of the positive conjuncts of all conjunctions of a formula: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:}

\textit{\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{md}(\varphi) = \textsf{md}(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{md}(\varphi) = \sup(\{\textsf{expr}_1(\psi_i) | i \in \text{Pos}\} \cup \{\textsf{expr}_3(\psi_i) | i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_3(\psi) = \textsf{expr}_3(\varphi)
\end{align*}
}

\textit{(\textcolor{green}{4}) The \textnormal{maximal modal depth of other positive clauses in conjunctions} $\textsf{expr}_4$ measures the deepest positive modal depth aside from the deepest positive clause: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:}
\textit{
\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_4(\varphi) = \textsf{expr}_4(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{\ \psi_i \} \\
    & \text{then } \text{md}(\varphi) = \sup(\{\textsf{expr}_1(\psi_i)|i\in\text{Pos}\backslash \mathcal{R}\}\cup\{\textsf{expr}_4(\psi_i) | i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_4(\psi) = \textsf{expr}_4(\varphi)
\end{align*}
}

\textit{
(\textcolor{cyan}{5}) The \textnormal{maximal modal depth of negative clauses in conjunctions} $\textsf{expr}_5$ measures the deepest modal depth of the negative conjuncts of all conjunctions of a formula: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:
}
\textit{
\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_5(\varphi) = \textsf{expr}_5(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{expr}_5(\varphi) = \sup(\{\textsf{expr}_1(\psi_i)| i \in \text{Neg}\}\cup \{\textsf{expr}_5(\psi_i)|i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_5(\psi) = \textsf{expr}_5(\varphi)
\end{align*}
}
\textit{(\textcolor{violet}{6}) The \textnormal{nesting depth of negations} $\textsf{expr}_{6}$ measures the maximal number of negations when traversing the syntax tree of a formula: $\text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})$ of a formula $\varphi$ is defined recursively by:}
\textit{
\begin{align*}
    \text{if } \varphi &= \langle a \rangle \psi \quad \text{ with } a \in \Sigma \\
    & \text{then } \textsf{expr}_6(\varphi) = \textsf{expr}_6(\psi) \\
    \text{if } \varphi &= \bigwedge_{i \in I} \{ \psi_i \} \\
    & \text{then } \textsf{expr}_6(\varphi) = \sup(\{\textsf{expr}_6(\psi_i)| i \in I\}) \\
    \text{if } \psi &= \neg \varphi \\
    & \text{then } \textsf{expr}_6(\psi) = 1 + \textsf{expr}_6(\varphi)
\end{align*}
}
\textit{where:}

$\textit{Neg} := \{i \in I \, | \, \exists \varphi'_i. \psi_i = \neg \varphi'_i\}$

$\textit{Pos} := I \setminus \text{Neg}$

$\mathcal{R} := \left\{
\begin{aligned}
&\varnothing \textit{ if } \textit{Pos} = \varnothing, \\
&\{ r \} \textit{ for some } r \in \textit{Pos} \text{ where } \textit{expr}_1(\psi_r) \textit{ maximal for \textit{Pos}}
\end{aligned}
\right\}.$

\textit{We combine this to the expressiveness price $\textsf{expr}: \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \infty})^6$ of a formula $\varphi$:
\[
\text{expr}(\varphi) :=
\begin{pmatrix}
\text{expr}_1(\varphi) \\
\text{expr}_2(\varphi) \\
\text{expr}_3(\varphi) \\
\text{expr}_4(\varphi) \\
\text{expr}_5(\varphi) \\
\text{expr}_6(\varphi) \\
\end{pmatrix}
\]
}

We show that $\textsf{expr}$ defines the same function as (\cite{bisping2023process}, definition 5) in (appendix).
\<close>

text \<open>The formalization closely follows the structure outlined in the definition. Neg and Pos can easily be derived using our formalization of Conjunctions. \\
The function \<open>pos_r\<close> formalizes the set $Pos - \mathcal{R}$. It invokes the axiom of choice by selecting and removing a formula with maximal modal depth from Pos using the Hilbert choice operator \<open>SOME\<close>.\<close>

primrec expr_1 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_1_tt: \<open>expr_1 TT = 0\<close> |
expr_1_conj: \<open>expr_1 (hml_conj I J \<Phi>) = Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J)\<close> |
expr_1_pos: \<open>expr_1 (hml_pos \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

primrec expr_2 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_2_tt: \<open>expr_2 TT = 1\<close> |
expr_2_conj: \<open>expr_2 (hml_conj I J \<Phi>) = 1 + Sup ((expr_2 \<circ> \<Phi>) ` I \<union> (expr_2 \<circ> \<Phi>) ` J)\<close> |
expr_2_pos: \<open>expr_2 (hml_pos \<alpha> \<phi>) = expr_2 \<phi>\<close>

primrec expr_3 :: "('a, 's) hml \<Rightarrow> enat"
  where
expr_3_tt: \<open>expr_3 TT = 0\<close> |
expr_3_pos: \<open>expr_3 (hml_pos \<alpha> \<phi>) = expr_3 \<phi>\<close> | 
expr_3_conj: \<open>expr_3 (hml_conj I J \<Phi>) = (Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` I \<union> (expr_3 \<circ> \<Phi>) ` J))\<close>

fun pos_r :: "('a, 's)hml set \<Rightarrow> ('a, 's)hml set"
  where
"pos_r xs = (
let max_val = (Sup (expr_1 ` xs)); 
  max_elem = (SOME \<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val);
  xs_new = xs - {max_elem}
in xs_new)"

primrec expr_4 :: "('a, 's)hml \<Rightarrow> enat" 
  where
expr_4_tt: "expr_4 TT = 0" |
expr_4_pos: "expr_4 (hml_pos a \<phi>) = expr_4 \<phi>" |
expr_4_conj: "expr_4 (hml_conj I J \<Phi>) = Sup ((expr_1 ` (pos_r (\<Phi> ` I)))  \<union> (expr_4 \<circ> \<Phi>) ` I \<union> (expr_4 \<circ> \<Phi>) ` J)"

primrec expr_5 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_5_tt: \<open>expr_5 TT = 0\<close> |
expr_5_pos:\<open>expr_5 (hml_pos \<alpha> \<phi>) = expr_5 \<phi>\<close>|
expr_5_conj: \<open>expr_5 (hml_conj I J \<Phi>) = 
(Sup ((expr_5 \<circ> \<Phi>) ` I \<union> (expr_5 \<circ> \<Phi>) ` J \<union> (expr_1 \<circ> \<Phi>) ` J))\<close>

primrec expr_6 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_6_tt: \<open>expr_6 TT = 0\<close> |
expr_6_pos: \<open>expr_6 (hml_pos \<alpha> \<phi>) = expr_6 \<phi>\<close>|
expr_6_conj: \<open>expr_6 (hml_conj I J \<Phi>) = 
(Sup ((expr_6 \<circ> \<Phi>) ` I \<union> ((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J)))\<close>

fun expr :: "('a, 's)hml \<Rightarrow> enat \<times> enat \<times> enat \<times>  enat \<times> enat \<times> enat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>

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

text \<open>\begin{figure}[t]
    \centering
\begin{multicols}{2}

\columnbreak
\begin{tikzpicture}[-, >=stealth, node distance=1.2cm, every node/.style={minimum size=0.3cm}]
    \node (p1) {$\langle a \rangle$};
    \node (p2) [below of=p1] {$\bigwedge$};
    \node (p3) [below left=of p2] {$\langle b \rangle$};
    \node (p4) [below right=of p2] {$\langle a \rangle$};
    \node (p5) [below of=p3] {$\bigwedge$};
    \node (p6) [below of=p4] {$\bigwedge$};
    \node (p7) [below left of=p6] {$\lnot$};
    \node (p8) [below right of=p6] {$\lnot$};
    \node (p9) [below of=p7] {$\langle a \rangle$};
    \node (p10) [below of=p9] {$\langle c \rangle$};
    \node (p11) [below of=p10] {$\bigwedge$};
    \node (p12) [below of=p8] {$\langle b \rangle$};
    \node (p13) [below of=p12] {$\bigwedge$};

    \path[-] (p1) edge (p2);
    \path[-] (p2) edge (p3);
    \path[-] (p2) edge (p4);
    \path[-] (p3) edge (p5);
    \path[-] (p4) edge (p6);
    \path[-] (p6) edge (p7);
    \path[-] (p6) edge (p8);
    \path[-] (p7) edge (p9);
    \path[-] (p9) edge (p10);
    \path[-] (p10) edge (p11);
    \path[-] (p8) edge (p12);
    \path[-] (p12) edge (p13);

  \node[circle, draw=red, fill=red, inner sep=0.3pt, minimum size=3pt] (v11) at (4,0) {};
  \node[circle, draw=red, fill=red, inner sep=0.3pt, minimum size=3pt] (v12) at (4,-2.67) {};
  \node[circle, draw=red, fill=red, inner sep=0.3pt, minimum size=3pt] (v12) at (4,-6) {};
  \node[circle, draw=red, fill=red, inner sep=0.3pt, minimum size=3pt] (v13) at (4,-7.2) {};
  \node (v14) at (4,-8.7) {};
  \node (v21) at (5,0.2) {};
  \node[circle, draw=orange, fill=orange, inner sep=0.3pt, minimum size=3pt] (v22) at (5,-1.2) {};
  \node[circle, draw=orange, fill=orange, inner sep=0.3pt, minimum size=3pt] (v23) at (5,-3.8) {};
  \node[circle, draw=orange, fill=orange, inner sep=0.3pt, minimum size=3pt] (v24) at (5,-7.2) {};
  \node (v25) at (5,-8.7) {};
  \node (v31) at (6,0.2) {};
  \node[circle, draw=myyellow, fill=myyellow, inner sep=0.3pt, minimum size=3pt] (v32) at (6,-2.67) {};
  \node[circle, draw=myyellow, fill=myyellow, inner sep=0.3pt, minimum size=3pt] (v32) at (6,-6) {};
  \node[circle, draw=myyellow, fill=myyellow, inner sep=0.3pt, minimum size=3pt] (v33) at (6,-7.2) {};
  \node (v34) at (6,-8.7) {};
  \node (v41) at (7,0.2) {};
  \node[circle, draw=green, fill=green, inner sep=0.3pt, minimum size=3pt] (v42) at (7,-2.67) {};
  \node (v43) at (7,-8.7) {};
  \node (v51) at (8,0.2) {};
  \node[circle, draw=cyan, fill=cyan, inner sep=0.3pt, minimum size=3pt] (v52) at (8,-6) {};
  \node[circle, draw=cyan, fill=cyan, inner sep=0.3pt, minimum size=3pt] (v53) at (8,-7.2) {};
  \node (v54) at (8,-8.7) {};
  \node (v61) at (9,0.2) {};
  \node[circle, draw=violet, fill=violet, inner sep=0.3pt, minimum size=3pt] (v62) at (9,-5.2) {};
  \node (v63) at (9,-8.7) {};

  \path[-, red] (v11) edge (v14);
  \path[-, orange] (v21) edge (v25);
  \path[-, myyellow] (v31) edge (v34);
  \path[-, green] (v41) edge (v43);
  \path[-, cyan] (v51) edge (v54);
  \path[-, violet] (v61) edge (v63);


\end{tikzpicture}
\end{multicols}
\caption{Pricing of formula $\langle a \rangle \bigwedge \{\langle b \rangle, \langle a \rangle \bigwedge \{\lnot \langle a \rangle \langle c \rangle, \lnot \langle b \rangle\}\}$}
    \label{fig:2_3}
\end{figure}\<close>

lemma example_2_3:
  fixes s and t and a and b and c
  assumes "s \<noteq> t"
  defines \<phi>: "(\<phi>::('a, 's)hml) \<equiv> 
  (hml_pos a 
    (hml_conj {s, t} {}
      (\<lambda>i. (if i = s 
            then (hml_pos b TT) 
            else 
              (if i = t  
               then (hml_pos a 
                      (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))))
               else undefined)))))"

shows 
  "expr_1 \<phi> = 4"
  "expr_2 \<phi> = 3"
  "expr_3 \<phi> = 3"
  "expr_4 \<phi> = 1"
  "expr_5 \<phi> = 2"
  "expr_6 \<phi> = 1"
  proof- 
    have "expr_1 (hml_pos a (hml_pos c TT)) = 2" "expr_1 (hml_pos b TT) = 1"
      by simp+
    hence "Sup ((expr_1 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 2"
      by (smt (verit, best) SUP_insert Sup_empty assms(1) ile_eSuc image_is_empty o_apply one_add_one plus_1_eSuc(1) sup.orderE sup_bot.right_neutral)
    hence "expr_1 (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) = 2"
      using expr_1_conj 
      by auto
    hence 1: "expr_1 (hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))) = 3"
      and 2: "expr_1 ( hml_pos b TT) = 1"
      by force+
    hence "Sup ((expr_1 \<circ> (\<lambda>i. if i = s then hml_pos b TT
                 else if i = t
                      then hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))
                      else undefined)) ` {s, t}) = 3"
      using "1" SUP_insert Sup_empty assms(1) image_is_empty o_apply one_le_numeral sup.orderE sup_bot.right_neutral sup_commute
      by (smt (verit, del_insts) ile_eSuc numeral_Bit1 numeral_One one_add_one one_plus_numeral_commute plus_1_eSuc(1))
    
    hence "expr_1 (hml_conj {s, t} {}
           (\<lambda>i. if i = s then hml_pos b TT
                 else if i = t
                      then hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))
                      else undefined)) = 3" 
      by simp
    thus e1: "expr_1 \<phi> = 4"  
      unfolding \<phi> 
      by fastforce

    show e2: "expr_2 \<phi> = 3" 
      unfolding \<phi>  
      by (smt (z3) "1" "2" SUP_empty SUP_insert Un_insert_right \<open>Sup ((expr_1 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 2\<close> \<open>expr_1 (hml_conj {} {s, t} (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) = 2\<close> assms(1) comp_def expr_1_pos expr_2_conj expr_2_pos expr_2_tt image_Un insert_is_Un numeral_One one_le_numeral sup.order_iff sup_bot_right)

    show e3: "expr_3 \<phi> = 3"
    proof-
      have e3_1: "expr_3 (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))) = 0"
        by simp
      hence e1_1: "(Sup ((expr_1 \<circ> (\<lambda>i. (if i = s 
            then (hml_pos b TT) 
            else 
              (if i = t  
               then (hml_pos a 
                      (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))))
               else undefined)))) ` {s, t})) = 3"
        using \<open>Sup ((expr_1 \<circ> (\<lambda>i. if i = s then hml_pos b TT else if i = t then hml_pos a (hml_conj {} {s, t} (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) else undefined)) ` {s, t}) = 3\<close> by blast
      have "(Sup ((expr_3 \<circ> (\<lambda>i. (if i = s 
            then (hml_pos b TT) 
            else 
              (if i = t  
               then (hml_pos a 
                      (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))))
               else undefined)))) ` {s, t})) = 0"
        
        by simp
      hence "expr_3  
    (hml_conj {s, t} {}
      (\<lambda>i. (if i = s 
            then (hml_pos b TT) 
            else 
              (if i = t  
               then (hml_pos a 
                      (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))))
               else undefined)))) = 3"
        using e1_1
        by (smt (verit, best) Sup_union_distrib bot_enat_def expr_3_conj image_empty sup_bot.right_neutral)
      thus ?thesis
        unfolding \<phi> 
        by fastforce
    qed

    show e5: "expr_5 \<phi> = 2"
    proof-
      have "expr_5 (hml_pos b TT) = 0"
        by fastforce
      have "expr_5 (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))) = 2"
        using \<open>Sup ((expr_1 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 2\<close> bot_enat_def by auto

      hence "expr_5 (hml_conj {s, t} {}
      (\<lambda>i. (if i = s 
            then (hml_pos b TT) 
            else 
              (if i = t  
               then (hml_pos a 
                      (hml_conj {} {s, t} 
                        (\<lambda>j. (if j = s 
                              then (hml_pos a 
                                     (hml_pos c TT)) 
                              else 
                                (if j = t 
                                 then (hml_pos b TT) 
                                 else undefined)))))
               else undefined)))) = 2"
        using \<open>expr_5 (hml_pos b TT) = 0\<close> image_insert SUP_insert Sup_union_distrib Un_insert_left Un_insert_right \<open>Sup ((expr_1 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 2\<close> assms(1) comp_apply expr_5_conj expr_5_pos image_Un image_empty insert_absorb insert_iff insert_is_Un
        
      proof -
        assume "Sup ((expr_1 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 2"
        have f1: "(expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {} \<union> (expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {s, t} \<union> (expr_1 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {s, t} = (expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {} \<union> (expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {t, s} \<union> insert ((expr_1 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) t) ((expr_1 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {s})"
          by (simp add: insert_commute)
        have f2: "expr_5 (TT::('a, 's) hml) = expr_5 (if t = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if t = t then hml_pos b TT else undefined)"
          by auto
        have f3: "insert (expr_5 (if t = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if t = t then hml_pos b TT else undefined)) (insert ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) s) ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {})) = (expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {} \<union> (expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {t, s}"
          by auto
        have "expr_5 (hml_conj {s, t} {} (\<lambda>sa. if sa = s then hml_pos b TT else if sa = t then hml_pos a (hml_conj {} {s, t} (\<lambda>sa. if sa = s then hml_pos a (hml_pos c TT) else if sa = t then hml_pos b TT else undefined)) else undefined)) = Sup (insert ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) s) ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {}) \<union> insert ((expr_1 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) t) ((expr_1 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {s}) \<union> insert ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) s) ((expr_5 \<circ> (\<lambda>sa. if sa = s then hml_pos a (hml_pos c (TT::('a, 's) hml)) else if sa = t then hml_pos b TT else undefined)) ` {}))"
          using f1 \<open>s \<noteq> t\<close> by auto
        then show ?thesis
          using f3 f2 by (smt (z3) \<open>\<And>a A. insert a A = {a} \<union> A\<close> \<open>\<And>a C B. insert a B \<union> C = insert a (B \<union> C)\<close> \<open>\<And>f B A. f ` (A \<union> B) = f ` A \<union> f ` B\<close> \<open>\<And>f a B. f ` insert a B = insert (f a) (f ` B)\<close> \<open>\<And>x g f. (f \<circ> g) x = f (g x)\<close> \<open>expr_5 (hml_conj {} {s, t} (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) = 2\<close> empty_is_image expr_5_conj expr_5_pos insert_commute)
      qed
      thus ?thesis
        unfolding \<phi>
        by force
    qed

    show e6: "expr_6 \<phi> = 1"
    proof-
      have e6_1: "Sup ((expr_6 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                  else if j = t then hml_pos b TT else undefined)) ` {}) = 0"
        using bot_enat_def by force 
      have "Sup (((expr_6 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                  else if j = t then hml_pos b TT else undefined)) ` {s, t})) = 0"
        by simp
      hence e6_2: "Sup (((eSuc \<circ> expr_6 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                  else if j = t then hml_pos b TT else undefined)) ` {s, t})) = 1"
        using eSuc_def 
        by (simp add: one_eSuc)
      thus "expr_6 \<phi> = 1"
        unfolding \<phi>
        using e6_1 
        by (smt (z3) SUP_insert assms(1) ccSUP_empty comp_def empty_is_image expr_6.simps(1) expr_6.simps(2) expr_6_conj sup_bot.left_neutral sup_bot_right)
    qed

      have "(expr_1 ` (pos_r ((\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined) ` {}))) = {}"
  "((expr_4 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {}) = {}"
      by auto
    hence "Sup (expr_1 ` (pos_r ((\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined) ` {}))) = 0"
          "Sup((expr_4 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {}) = 0"
          "Sup((expr_4 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 0"
      using bot_enat_def by fastforce+
    hence "Sup ((expr_1 ` (pos_r ((\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined) ` {})))  \<union> (expr_4 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {} \<union> (expr_4 \<circ> (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)) ` {s, t}) = 0" by simp
    hence "expr_4 (hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))) = 0"
      by simp
    have "(pos_r ((\<lambda>i. if i = s then hml_pos b TT
                 else if i = t
                      then hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))
                      else undefined) ` {s, t})) = 
                          {hml_pos b TT}"
    proof-
      define xs where "xs \<equiv> ((\<lambda>i. if i = s then hml_pos b TT
                 else if i = t
                      then hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))
                      else undefined) ` {s, t})"
      have "(Sup (expr_1 ` xs)) = 3" 
        unfolding xs_def
        by (metis Sup.SUP_image \<open>Sup ((expr_1 \<circ> (\<lambda>i. if i = s then hml_pos b TT else if i = t then hml_pos a (hml_conj {} {s, t} (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined)) else undefined)) ` {s, t}) = 3\<close>)
      hence "{\<psi> | \<psi>. \<psi> \<in> xs \<and> (expr_1 \<psi> = (Sup (expr_1 ` xs)))} =
              {(hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)))}"
        using 1 2 assms(1) xs_def by force
      hence "(SOME \<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = (Sup (expr_1 ` xs))) =
              (hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined)))"
        unfolding xs_def
        using pos_r.simps 2 1 assms(1)
        by (smt (verit, ccfv_threshold) mem_Collect_eq singleton_iff someI_ex)
      then show ?thesis 
        unfolding xs_def
        using pos_r.simps assms(1) by auto
    qed
    hence "Sup ((expr_1 ` (pos_r ((\<lambda>i. if i = s then hml_pos b TT
                 else if i = t
                      then hml_pos a
                            (hml_conj {} {s, t}
                              (\<lambda>j. if j = s then hml_pos a (hml_pos c TT)
                                    else if j = t then hml_pos b TT else undefined))
                      else undefined) ` {s, t})))) = 1" 
      using "1" by auto
    then show "expr_4 \<phi> = 1" 
      unfolding \<phi>
      by (smt (verit, del_insts) SUP_insert Sup_union_distrib \<open>expr_4 (hml_pos a (hml_conj {} {s, t} (\<lambda>j. if j = s then hml_pos a (hml_pos c TT) else if j = t then hml_pos b TT else undefined))) = 0\<close> bot_enat_def ccSUP_empty comp_apply expr_4_conj expr_4_pos expr_4_tt sup_bot.right_neutral)
  qed

  text \<open>\textit{Example 2}: This example illustrates how the prices of a formula are calculated. In Figure \ref{fig:2_3}, you can see the pricing process for the formula $\langle a \rangle \bigwedge \{\langle b \rangle, \langle a \rangle \bigwedge \{\lnot \langle a \rangle \langle c \rangle, \lnot \langle b \rangle\}\}$. Each line to the right of the syntax tree represents the price of a specific dimension. The circles of each line represent an increase in the price of that dimension. The colors of these lines correspond to those defined in (ref definition 2.3.1) and indicate the dimension they represent. Note the finishing empty conjunction, which increases the conjunction depth by one.
We can use the function to calculate the prices of the formulas in Example 1. The price of $\varphi_1 :=\langle a \rangle\bigwedge\{\lnot\langle c \rangle\}$ is $expr(\varphi_1) = (2, 2, 0, 0, 1, 1)$. For $\varphi_2 := \bigwedge\{\lnot\langle a \rangle\bigwedge\{\lnot\langle c \rangle\}\}$, $expr(\varphi_2) = (2, 3, 0, 0, 2, 2)$.
\<close>
text \<open>\textbf{Proposition} The expressiveness function is monotonic. Specifically, for any formula $\langle\alpha\rangle\varphi$, is the expressiveness of the subformula $\varphi$ less than or equal to the expressiveness of $\langle\alpha\rangle\varphi$.
Similarly, for any conjunctive formula $\bigwedge_{i\in I}\psi_i$, the expressiveness of every conjunct $\psi_i$ is less than or equal to the expressiveness of $\bigwedge_{i\in I}\psi_i$.\<close>

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