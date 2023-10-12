theory formula_prices_list
  imports 
    Main
    HML_list
begin

fun modal_depth :: "('a)formula_list \<Rightarrow> nat" where
"modal_depth (HML_conj [] []) = 0" |
"modal_depth (HML_conj (x#xs) ys) = Max ({0} \<union> {modal_depth x} \<union> {modal_depth (HML_conj xs ys)})"
| "modal_depth (HML_conj [] (y#ys)) = Max ({0} \<union> {modal_depth y} \<union> {modal_depth (HML_conj ys [])})"
| "modal_depth (HML_poss _ \<phi>) = 1 + modal_depth \<phi>"

value "modal_depth (HML_conj ([]::('a)formula_list list) ([]::('a)formula_list list))"

inductive_set subformula_rel :: "('a)formula_list rel" where
"(\<phi>, \<phi>) \<in> subformula_rel" |
"\<phi> \<in> set \<Phi> \<Longrightarrow> (\<phi> ,(HML_conj \<Phi> \<Psi>)) \<in> subformula_rel" |
"\<phi> \<in> set \<Psi> \<Longrightarrow> (\<phi> ,(HML_conj \<Phi> \<Psi>)) \<in> subformula_rel" |
"(\<phi>, \<psi>) \<in> subformula_rel \<Longrightarrow> \<psi> \<in> set \<Phi> \<Longrightarrow> (\<phi>, (HML_conj \<Phi> \<Psi>)) \<in> subformula_rel" |
"(\<phi>, \<psi>) \<in> subformula_rel \<Longrightarrow> \<psi> \<in> set \<Psi> \<Longrightarrow> (\<phi>, (HML_conj \<Phi> \<Psi>)) \<in> subformula_rel" |
"(\<phi>, \<psi>) \<in> subformula_rel \<Longrightarrow> (\<phi> ,(HML_poss \<alpha> \<psi>)) \<in> subformula_rel"

lemma wf_subformula_rel: "wf {(\<phi>, \<psi>). (\<phi>, \<psi>) \<in> subformula_rel \<and> modal_depth \<phi> < modal_depth \<psi>}"
  by (metis (mono_tags, lifting) case_prod_conv in_measure mem_Collect_eq wfUNIVI wf_induct_rule wf_measure)

lemma subformula_basis: "\<forall>f. ((HML_conj [] []), f) \<in> subformula_rel"
proof(rule allI)
  fix g::"'a formula_list"
  show "(HML_conj [] [], g) \<in> subformula_rel"
  proof(induction g)
    case (HML_conj x1 x2)
    then show ?case
      by (metis list.set_intros(1) neq_Nil_conv subformula_rel.intros(1) subformula_rel.intros(4) subformula_rel.intros(5))
  next
    case (HML_poss x1 g)
    then show ?case 
      by (rule formula_prices_list.subformula_rel.intros(6))
        qed
      qed

thm wf_measure
thm HML_list.formula_list.exhaust

fun expr_1 :: "('a)formula_list \<Rightarrow>  nat"
  where
expr_1_conj_empty:\<open>expr_1 (HML_conj [] []) = 0\<close> |
expr_1_conj: \<open>expr_1 (HML_conj (x#xs) \<Psi>) = (Max ({0} \<union> {expr_1 x} \<union> {expr_1 (HML_conj xs \<Psi>)}))\<close> |
expr_1_conj_right:\<open>expr_1 (HML_conj [] (y#ys)) = (Max ({0} \<union> {expr_1 y} \<union> {expr_1 (HML_conj [] ys)}))\<close> |
expr_1_pos: \<open>expr_1 (HML_poss \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

(*Done*)
lemma expr_1_set_form: "expr_1 (HML_conj \<Phi> \<Psi>) =
Max({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
proof(induction \<Phi>)
  case Nil
  then show ?case
  proof(induction \<Psi>)
    case Nil
    then show ?case by simp
  next
    case (Cons a \<Psi>)
    then show ?case 
    proof-
      have A1: "{expr_1 y |y. y \<in> set (a#\<Psi>)} = {expr_1 a} \<union> {expr_1 y|y. y \<in> set \<Psi>}"
        by auto
      have "expr_1 (HML_conj [] (a#\<Psi>)) = (Max ({0} \<union> {expr_1 a} \<union> {expr_1 (HML_conj [] \<Psi>)}))"
        by simp
      also have "... = 
(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})}))"
        using local.Cons by fastforce
      finally have expr_1_IS: "expr_1 (HML_conj [] (a#\<Psi>)) = 
(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})}))"
        by this
      have fin: "finite ({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})"
        by simp
      have ne: "({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>}) \<noteq> {}"
        by simp
      have "\<forall>x \<in> {0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>}. x \<le>
Max({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})"
        by simp
      thm Max_in
      from fin ne have "Max({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>}) \<in> 
{0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>}"
        by (smt (verit, best) Max_in emptyE empty_Collect_eq empty_set)
      then have "(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})})) = 
(Max ({0} \<union> {expr_1 a} \<union> {0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>}))" 
        by simp
      also from A1 have "(Max ({0} \<union> {expr_1 a} \<union> {0} \<union> {expr_1 x |x. x \<in> set []} \<union> {expr_1 y |y. y \<in> set \<Psi>})) = 
Max ({0} \<union> {expr_1 y |y. y \<in> set (a # \<Psi>)} \<union> {0} \<union> {expr_1 x |x. x \<in> set []})"
        by simp
      from this expr_1_IS show ?thesis by simp
    qed
  qed
next
  case (Cons a \<Phi>)
  then show ?case 
  proof(induction \<Psi>)
    case Nil
    then show ?case
    proof-
      have "expr_1 (HML_conj (a # \<Phi>) []) = (Max ({0} \<union> {expr_1 a} \<union> {expr_1 (HML_conj \<Phi> [])}))"
        by simp
      also have "... = 
(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})}))"
        using local.Nil by force
      finally have expr_1_eq: "expr_1 (HML_conj (a#\<Phi>) []) = 
(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})}))"
        by this
      have ne: "{0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []} \<noteq> {}"
        by simp
      have fin: "finite ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})"
        by simp
      have fa: "\<forall>x \<in> {0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []}. x \<le>
Max({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})"
        by simp
      from fin ne have "Max({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []}) \<in>
{0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []}" 
        by (smt (verit, best) Max_in emptyE empty_Collect_eq empty_set)
      from this fa have "(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})})) = 
(Max ({0} \<union> {expr_1 a} \<union> {0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []}))" 
        by simp
      also have eq2: "(Max ({0} \<union> {expr_1 a} \<union> {0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})) = 
(Max ({0} \<union> {expr_1 a}  \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []}))"
        by simp
      have "{expr_1 a}  \<union> {expr_1 x |x. x \<in> set \<Phi>} = {expr_1 x |x. x \<in> set (a#\<Phi>)}"
        by auto
      then have "(Max ({0} \<union> {expr_1 a}  \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set []})) = 
(Max ({0}  \<union> {expr_1 x |x. x \<in> set (a#\<Phi>)} \<union> {expr_1 y |y. y \<in> set []}))"
        by (metis (mono_tags, lifting) eq2 sup_assoc)
      from this expr_1_eq show "expr_1 (HML_conj (a#\<Phi>) []) = 
(Max ({0} \<union> {expr_1 x |x. x \<in> set (a # \<Phi>)} \<union> {expr_1 y |y. y \<in> set []}))" 
        by simp
    qed
  next
    case (Cons b \<Psi>)
    then show ?case 
    proof-
      have A1: "{expr_1 a} \<union> {expr_1 x |x. x \<in> set \<Phi>} = {expr_1 x |x. x \<in> set (a # \<Phi>)}" 
        by auto
      have ne: "{0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)} \<noteq> {}"
        by simp
      have fin: "finite ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})"
        by simp
      have fa: "\<forall>x \<in> ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)}). x \<le>
Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})" 
        by simp
      from fin ne have elem: "Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)}) \<in>
({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})"
        by (smt (verit, best) Max_in emptyE empty_Collect_eq empty_set)
      have "expr_1 (HML_conj (a # \<Phi>) (b # \<Psi>)) = 
(Max ({0} \<union> {expr_1 a} \<union> {expr_1 (HML_conj \<Phi> (b#\<Psi>))}))"
        by simp
      also have "... = 
(Max ({0} \<union> {expr_1 a} \<union> {Max ({0} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})}))"
        using Cons.prems by presburger
      also from fa elem have "... = 
(Max ({0} \<union> {expr_1 a} \<union> {expr_1 x |x. x \<in> set \<Phi>} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)}))" 
        by simp
      also from A1 have "... = Max ({0} \<union> {expr_1 x |x. x \<in> set (a # \<Phi>)} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})"
        by (metis (no_types, lifting) sup_assoc)
      finally show "expr_1 (HML_conj (a # \<Phi>) (b # \<Psi>)) = 
Max ({0} \<union> {expr_1 x |x. x \<in> set (a # \<Phi>)} \<union> {expr_1 y |y. y \<in> set (b # \<Psi>)})"
        by this
    qed
  qed
qed


value "expr_1 (HML_conj ([]::nat formula_list list) ([]::nat formula_list list))"
value"set ([HML_conj [] []]::nat formula_list list)"

value "expr_1 (HML_conj [] [a])" (* 0 *)

fun expr_2 :: "('a)formula_list \<Rightarrow>  nat"
  where
expr_2_conj_empty:\<open>expr_2 (HML_conj [] []) = 1\<close> |
expr_2_conj: \<open>expr_2 (HML_conj (x#xs) \<Psi>) = (Max ({1 + expr_2 x} \<union> {expr_2 (HML_conj xs \<Psi>)}))\<close> |
expr_2_conj_right:\<open>expr_2 (HML_conj [] (y#ys)) = (Max ({1 + expr_2 y} \<union> {expr_2 (HML_conj [] ys)}))\<close> |
expr_2_pos: \<open>expr_2 (HML_poss \<alpha> \<phi>) = expr_2 \<phi>\<close>

(*TODO*)
lemma expr_2_set: "expr_2 (HML_conj \<Phi> \<Psi>) =
Max({1} \<union> {1 + expr_2 x | x. x \<in> set \<Phi>} \<union> {1 + expr_2 y | y. y \<in> set \<Psi>})"
  sorry

fun pos_r :: "('a)formula_list list \<Rightarrow> ('a)formula_list list"
  where
"pos_r [] = []"|
"pos_r xs = (
let max_val = Max (set (map(\<lambda>x. expr_1 x) xs)); 
max_elem = hd(filter (\<lambda>y. expr_1 y = max_val) xs);
xs_new = filter(\<lambda>y. y \<noteq> max_elem) xs
in xs_new)"
(*xs_new = filter (\<lambda>y. expr_1 y < max_val) xs*)


fun r :: "('a)formula_list list \<Rightarrow> nat"
  where
\<open>r xs = Max (set (map(\<lambda>x. expr_1 x) xs))\<close>


fun expr_3 :: "('a) formula_list \<Rightarrow> nat"
where
 expr_3_pos: \<open>expr_3 (HML_poss \<alpha> \<phi>) = expr_3 \<phi>\<close>
| expr_3_conj_emtpy: \<open>expr_3 (HML_conj [] []) = 0\<close>
| expr_3_conj_right: \<open>expr_3 (HML_conj [] (y#ys)) = Max ({0} \<union> {expr_3 y} \<union> {expr_3 (HML_conj [] ys)})\<close>
| expr_3_conj: \<open>expr_3 (HML_conj (x#xs) \<Psi>) = 
Max ({0} \<union> {expr_1 x} \<union> {expr_3 (HML_conj xs \<Psi>)} \<union> {expr_3 x})\<close>

(*TODO*)
lemma expr_3_set: "expr_3 (HML_conj \<Phi> \<Psi>) =
Max({0} \<union> {expr_3 x | x. x \<in> set \<Phi>} \<union> {expr_3 y | y. y \<in> set \<Psi>} \<union> {expr_1 x | x. x \<in> set \<Phi>})"
  sorry

(* Neg := {i \<in> I| \<exists>\<phi>\<^sub>i. \<psi>\<^sub>i = \<not>\<phi>\<^sub>i}*)

fun 
  expr_4 :: "('a)formula_list \<Rightarrow> nat" and
expr_4_2 :: "('a)formula_list \<Rightarrow> ('a)formula_list list \<Rightarrow> nat"
where
"expr_4 (HML_poss a \<phi>) = expr_4 \<phi>" |
"expr_4 (HML_conj \<Phi> \<Psi>) = expr_4_2 (HML_conj \<Phi> \<Psi>) \<Phi>" |
"expr_4_2 (HML_poss a \<phi>) \<Phi> = expr_4 \<phi>" |
"expr_4_2 (HML_conj [] []) y1 = Max {expr_1 (HML_conj (pos_r y1) [])}" |
"expr_4_2 (HML_conj (a#\<Phi>) \<Psi>) y1 = Max({expr_4 a} \<union> {expr_4_2(HML_conj \<Phi> \<Psi>) y1})" |
"expr_4_2 (HML_conj [] (a#\<Psi>)) y1 = Max({expr_4 a} \<union> {expr_4_2(HML_conj [] \<Psi>) y1})"

lemma expr_4_eq_expr_4_2: "expr_4_2(HML_conj [] \<Psi>) y1 = 
Max({expr_4 x|x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
proof(induction \<Psi>)
  case Nil
  then show ?case by simp

next
  case (Cons a \<Psi>)
  have "expr_4_2 (HML_conj [] (a # \<Psi>)) y1 = 
Max({expr_4 a} \<union> {expr_4_2(HML_conj [] \<Psi>) y1})"
    by simp
  also have "... = 
Max({expr_4 a} \<union> {Max ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
    using local.Cons by presburger
  finally have expr_4_2_form: "expr_4_2 (HML_conj [] (a # \<Psi>)) y1 =
Max({expr_4 a} \<union> {Max ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
    by this
  have ne: "({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])}) \<noteq> {}"
    by simp
  have fin: "finite ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})" 
    by simp
  from fin ne have elem: "Max ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])}) \<in> 
({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})" 
    by (rule Max_in)
  from fin ne have "\<forall>x \<in> ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])}). 
x \<le> Max({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
    by simp
  from this elem fin ne have "Max({expr_4 a} \<union> {Max ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})}) =
Max({expr_4 a} \<union> ({expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])}))"
    by (metis (no_types, lifting) Max.union Max_singleton empty_not_insert finite.emptyI finite.insertI)
  also have eq: "... = Max({expr_4 a} \<union> {expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
    by simp
  have "{expr_4 a} \<union> {expr_4 x |x. x \<in> set \<Psi>} = {expr_4 x |x. x \<in> set (a # \<Psi>)}"
    by auto
  then have "Max({expr_4 a} \<union> {expr_4 x |x. x \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1)[])}) =
 Max ({expr_4 x |x. x \<in> set (a # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
    by simp
  then show ?case
    using calculation eq expr_4_2_form by presburger
qed

(*Done*)
lemma expr_4_2_eq: "expr_4_2(HML_conj \<Phi> \<Psi>) y1 =
Max({expr_4 x|x. x\<in> set \<Phi>} \<union> {expr_4 y|y. y \<in> set \<Psi>} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
proof(induction \<Phi>)
  case Nil
  then show ?case
    by (simp add: expr_4_eq_expr_4_2)
next
  case (Cons a \<Phi>)
  then show ?case 
  proof(induction \<Psi>)
    case Nil
    have ne: "({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})
\<noteq> {}"
      by simp
    have fin: "finite ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    from fin ne Max_in have elem: "Max({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])}) \<in>
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by (smt (verit, ccfv_threshold) emptyE empty_Collect_eq empty_set)
    from fin ne have "\<forall>x \<in> ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])}).
x \<le> Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    from this elem fin ne have max_decompos: "Max ({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})}) =
Max({expr_4 a} \<union> 
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])}))"
      by (smt (verit, best) Max_eqI Max_singleton Sup_fin.union Sup_fin_Max empty_not_insert finite.emptyI finite.insertI)
    have "expr_4_2 (HML_conj (a # \<Phi>) []) y1 =
Max ({expr_4 a} \<union> {expr_4_2(HML_conj \<Phi> []) y1})"
      by simp
    also have eq_1: "... = 
Max ({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
      using local.Nil by fastforce
    finally have "expr_4_2 (HML_conj (a # \<Phi>) []) y1 =
Max ({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
      by this
    from max_decompos eq_1 have "expr_4_2 (HML_conj (a # \<Phi>) []) y1 = 
Max({expr_4 a} \<union> 
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])}))"
      by simp
    then have eq: "expr_4_2 (HML_conj (a # \<Phi>) []) y1
 = Max({expr_4 a} \<union> 
{expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set []} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    have "{expr_4 a} \<union> {expr_4 x |x. x \<in> set \<Phi>} = {expr_4 x |x. x \<in> set (a#\<Phi>)}"
      by auto
    from this eq show ?case by simp
  next
    case (Cons b \<Psi>)
    have "expr_4_2 (HML_conj (a # \<Phi>) (b # \<Psi>)) y1 = 
Max({expr_4 a} \<union> {expr_4_2(HML_conj \<Phi> (b#\<Psi>)) y1})"
      by simp
    also have "... = Max({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
      using Cons.prems by presburger
    finally have expr_4_2_form: "expr_4_2 (HML_conj (a # \<Phi>) (b # \<Psi>)) y1 = 
Max({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})})"
      by this
    have ne:
"({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])}) \<noteq> 
{}" 
      by simp
    have fin: 
"finite(
{expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    from fin ne have elem: "Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])}) \<in>
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by (rule Max_in)
    have "\<forall>x \<in> ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])}). x \<le>
Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    from elem this have "Max({expr_4 a} \<union> 
{Max ({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})}) =
Max({expr_4 a} \<union> 
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])}))"
      by (metis (no_types, lifting) Max_singleton Sup_fin.union Sup_fin_Max empty_not_insert fin finite.emptyI finite.insertI ne)
    from this expr_4_2_form have "expr_4_2 (HML_conj (a # \<Phi>) (b # \<Psi>)) y1 = 
Max({expr_4 a} \<union> 
({expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])}))"
      by simp
    also have "... = 
Max({expr_4 a} \<union> 
{expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by simp
    finally have eq: "expr_4_2 (HML_conj (a # \<Phi>) (b # \<Psi>)) y1 =
Max({expr_4 a} \<union> 
{expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set (b # \<Psi>)} \<union> {expr_1 (HML_conj (pos_r y1) [])})"
      by this
    have "{expr_4 a} \<union> {expr_4 x |x. x \<in> set \<Phi>} =  
{expr_4 x |x. x \<in> set (a#\<Phi>)}"
      by auto
    from this eq show ?case by simp
  qed
qed

(*Done*)
lemma expr_4_set: "expr_4 (HML_conj \<Phi> \<Psi>) =
Max ({expr_1 (HML_conj (pos_r \<Phi>)[])} \<union> {expr_4 x|x. x \<in> set \<Phi>} \<union> {expr_4 y|y. y \<in> set \<Psi>})"
proof-
  have "expr_4 (HML_conj \<Phi> \<Psi>) = expr_4_2 (HML_conj \<Phi> \<Psi>) \<Phi>"
    by simp
  also from expr_4_2_eq have "... = 
Max ({expr_1 (HML_conj (pos_r \<Phi>)[])} \<union> {expr_4 x |x. x \<in> set \<Phi>} \<union> {expr_4 y |y. y \<in> set \<Psi>})"
    by auto
  finally show ?thesis
    by this
qed

fun expr_5 :: "('a)formula_list \<Rightarrow> nat"
where
expr_5_pos:\<open>expr_5 (HML_poss \<alpha> \<phi>) = expr_5 \<phi>\<close>|
expr_5_conj_empty: \<open>expr_5 (HML_conj [] []) = 0\<close> |
expr_5_conj: \<open>expr_5 (HML_conj (x#xs) \<Psi>) = Max ({0} \<union> {expr_5 x} \<union> {expr_5 (HML_conj xs \<Psi>)})\<close> |
expr_5_conj_2: 
\<open>expr_5 (HML_conj [] (y#ys)) = Max ({0} \<union> {expr_5 y} \<union> {expr_5 (HML_conj [] ys)} \<union> {expr_1 y})\<close>

lemma expr_5_set: "expr_5 (HML_conj \<Phi> \<Psi>) = 
Max({0} \<union> {expr_5 x | x. x \<in> set \<Phi>} \<union> {expr_5 y | y. y \<in> set \<Psi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
  sorry

fun expr_6 :: "('a)formula_list \<Rightarrow> nat"
where
expr_6_pos: \<open>expr_6 (HML_poss \<alpha> \<phi>) = expr_6 \<phi>\<close>|
expr_6_conj_empty: \<open>expr_6 (HML_conj [] []) = 0\<close>|
expr_6_conj: \<open>expr_6 (HML_conj (x#xs) \<Psi>) = Max({0} \<union> {expr_6 x} \<union> {expr_6 (HML_conj xs \<Psi>)})\<close> |
expr_6_conj_2: \<open>expr_6 (HML_conj [] (y#ys)) = Max({0}  \<union> {1 + expr_6 y} \<union> {expr_6 (HML_conj [] ys)})\<close>

(*TODO*)
lemma expr_6_set: "expr_6 (HML_conj \<Phi> \<Psi>) = 
Max({0} \<union> {expr_6 x | x. x \<in> set \<Phi>} \<union> {1 + expr_6 y | y. y \<in> set \<Psi>})"
  sorry

fun expr :: "('a)formula_list \<Rightarrow> nat \<times> nat \<times> nat \<times>  nat \<times> nat \<times> nat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>


thm Sup
thm Max_def
end