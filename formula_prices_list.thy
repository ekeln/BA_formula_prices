(*<*)
theory formula_prices_list
  imports 
    Main
    HML_list
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
1. Observations\\
...
...\\ \<close>

subsubsection \<open>Formula Prices\<close>
text \<open>The \textit{expressiveness price} $\text{expr}: \text{HML}[\Sigma] \rightarrow (\mathbb{N} \cup \{\infty\})^6$ of a formula is defined recursively, similar to energy games:
TODO: $\text{expr}$ function \\\\

Remark: Infinity is included in our definition, due to infinite branching conjunctions. Supremum over infinite set wird zu unendlich.\<close>

text \<open>To better argue about the function we define each dimension as a seperate function.\<close>

text \<open>Vlt als erstes: modaltiefe als beispiel für observation expressiveness von formel, mit isabelle definition,
dann pos\_r definition,
direct\_expr definition,
einzelne dimensionen,
lemma direct\_expr = expr...\<close>

primrec expr_1 :: "('a, 's)hml \<Rightarrow> enat"
  where
expr_1_tt: \<open>expr_1 TT = 0\<close> |
expr_1_conj: \<open>expr_1 (hml_conj I J \<Phi>) = Sup ((expr_1 \<circ> \<Phi>) ` I \<union> (expr_1 \<circ> \<Phi>) ` J)\<close> |
expr_1_pos: \<open>expr_1 (hml_pos \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

fun pos_r :: "('a, 's)hml set \<Rightarrow> ('a, 's)hml set"
  where
"pos_r xs = (
let max_val = (Sup (expr_1 ` xs)); 
  max_elem = (SOME \<psi>. \<psi> \<in> xs \<and> expr_1 \<psi> = max_val);
  xs_new = xs - {max_elem}
in xs_new)"

lemma pos_r_subs: "pos_r (\<Phi> ` I) \<subseteq> (\<Phi> ` I)"
  by auto

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

termination
  apply rule
  using HML_wf_rel_is_wf HML_wf_rel.simps Un_iff pos_r_subs by fastforce+

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

lemma apply_comp:
  assumes "\<forall>x \<in> \<Phi> ` I. F x = G1 (G2 (G3 (G4 (G5 ((H x))))))"
  shows "Sup ((F \<circ> \<Phi>) ` I) = Sup((G1 \<circ> G2 \<circ> G3 \<circ> G4 \<circ> G5 \<circ> H \<circ> \<Phi>) ` I)"
  using assms by auto

lemma fa_set_eq: 
  assumes "\<forall>x \<in> \<Phi> ` I. F x = G (H x)"
  shows "((F \<circ> \<Phi>) ` I) = (G \<circ> H \<circ> \<Phi>) ` I" 
  using assms by force

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

thm comp_apply

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