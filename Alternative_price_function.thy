(*<*)
theory Alternative_price_function
imports
  formula_prices_list
begin
(*>*)
chapter \<open>Alternative price function\<close>
text \<open>\label{chap:alternative_price_function}\<close>

text \<open>Den Rest in den Appendix:\<close>

text \<open>\textit{
The expressiveness price $\textsf{expr} : \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \infty})^6$ of a formula interpreted as $6 \times 1$-dimensional vectors is defined recursively by:}

\begin{minipage}{0.45\textwidth}
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
\end{minipage}
\hfill
\begin{minipage}{0.45\textwidth}
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
\end{minipage}

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

Remark: The only deviation from \cite{bisping2023process} (Definition 5) is, that we include infinity in the range of the function since we allow for infinite branching conjunctions.

It turned out that it was easier to also define the price for every dimension i as a seperate function $\textsf{expr} : \text{HML}[\Sigma] \rightarrow (\mathbb{N \cup \infty})$.\<close>

text \<open>Our Isabelle definition of HML makes it very easy to derive the sets Pos and Neg, by \<open>\<Phi> ` I\<close> and \<open>\<Phi> ` J\<close> respectively.\<close>
text \<open>Vlt als erstes: modaltiefe als beispiel für observation expressiveness von formel, mit isabelle definition,
dann pos\_r definition,
direct\_expr definition,
einzelne dimensionen,
lemma direct\_expr = expr...\<close>

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



text \<open>We show that \<open>direct_expr\<close> and \<open>expr\<close> are the same:\<close>


(*<*)
lemma \<^marker>\<open>tag (proof) visible\<close> expr_6_direct_expr_eq:
  assumes "\<And>x. x \<in> \<Phi> ` I \<Longrightarrow> expr_6 x = snd (snd (snd (snd (snd (direct_expr x)))))"
  shows "(expr_6 \<circ> \<Phi>) ` I = (snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I"
proof -
  have "(expr_6 \<circ> \<Phi>) ` I = (\<lambda>x. snd (snd (snd (snd (snd (direct_expr (\<Phi> x))))))) ` I"
    by (simp add: assms)
  also have "... = (snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` I"
    by auto
  finally show ?thesis .
qed

lemma \<^marker>\<open>tag (proof) visible\<close> expr_6_eSuc_eq:
  assumes "\<And>x. x \<in> \<Phi> ` J \<Longrightarrow> eSuc (expr_6 x) = eSuc (snd (snd (snd (snd (snd (direct_expr x))))))"
  shows "((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) = ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
proof-
  have "((eSuc \<circ> expr_6 \<circ> \<Phi>) ` J) = (\<lambda>x. eSuc (snd (snd (snd (snd (snd (direct_expr (\<Phi> x)))))))) ` J"
    using assms by force
  also have "... = ((eSuc \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> snd \<circ> direct_expr \<circ> \<Phi>) ` J)"
    by auto
  finally show ?thesis.
qed

lemma \<^marker>\<open>tag (proof) visible\<close> expr_5_dir_eq:
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

(*<*)
end
(*>*)