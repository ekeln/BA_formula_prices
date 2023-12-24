theory formula_prices_list
  imports 
    Main
    HML_list
    "HOL-Library.Extended_Nat"
begin

fun expr_1 :: "('a)formula_list \<Rightarrow> enat"
  where
expr_1_conj: \<open>expr_1 (HML_conj \<Phi> \<Psi>) = (Sup ((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>))))\<close> |
expr_1_pos: \<open>expr_1 (HML_poss \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

(*Done*)
lemma expr_1_set_form: "expr_1 (HML_conj \<Phi> \<Psi>) =
Max({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
  apply((cases \<Phi>), (cases \<Psi>))
proof-
  assume assms: "\<Phi> = []" "\<Psi> = []"
  hence "((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>))) = {}"
    by blast
  hence e1_eq_0: "expr_1 (HML_conj \<Phi> \<Psi>) = 0"
    using Sup_enat_def expr_1.simps(1)
    by force
  from assms have "({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>}) = {0}"
    by simp
  hence "Max ({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>}) = 0"
    using Max_singleton
    by metis
  with e1_eq_0 show ?thesis
    by presburger
next
  fix a tail
  assume assms: "\<Phi> = []" "\<Psi> = a # tail"
  have eq: "((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>))) = ({expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
    by blast
  have fin_\<Psi>: "finite (set \<Psi>)"
    by auto
  from assms(2) have ne_\<Psi>: "(set \<Psi>) \<noteq> {}"
    by simp
  with assms(1) fin_\<Psi> have max_insert_0: "Max ({expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>}) = 
Max({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
    using Max_insert
    by auto
  from assms fin_\<Psi> ne_\<Psi> Sup_enat_def have "expr_1 (HML_conj \<Phi> \<Psi>) = Max ((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>)))"
    by auto
  with eq max_insert_0 show ?thesis using expr_1.simps(1)
    by presburger
next
  fix a tail
  assume \<Phi>_eq: "\<Phi> = a # tail"
  have eq: "((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>))) = ({expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
    by blast
  have fin_\<Phi>: "finite (set \<Phi>)"
    by auto
  from \<Phi>_eq have ne_\<Phi>: "(set \<Phi>) \<noteq> {}"
    by simp
  with fin_\<Phi> have max_insert_0: "Max ({expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>}) = 
Max({0} \<union> {expr_1 x | x. x \<in> set \<Phi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
    using Max_insert
    by auto
  from  fin_\<Phi> ne_\<Phi> Sup_enat_def have "expr_1 (HML_conj \<Phi> \<Psi>) = Max ((expr_1 ` (set \<Phi>)) \<union> (expr_1 ` (set \<Psi>)))"
    by auto
  with eq max_insert_0 show ?thesis using expr_1.simps(1)
    by presburger
qed

fun expr_2 :: "('a)formula_list \<Rightarrow> enat"
  where
expr_2_conj: \<open>expr_2 (HML_conj \<Phi> \<Psi>) = 1 + Sup ((expr_2 ` (set \<Phi>)) \<union> (expr_2 ` (set \<Psi>)))\<close> |
expr_2_pos: \<open>expr_2 (HML_poss \<alpha> \<phi>) = expr_2 \<phi>\<close>

(*TODO*)
lemma expr_2_set: "expr_2 (HML_conj \<Phi> \<Psi>) =
Max({1} \<union> {1 + expr_2 x | x. x \<in> set \<Phi>} \<union> {1 + expr_2 y | y. y \<in> set \<Psi>})"
  sorry

fun pos_r :: "('a)formula_list list \<Rightarrow> ('a)formula_list list"
  where
"pos_r xs = (
let max_val = (Sup (expr_1 ` (set xs))); 
max_elem = hd(filter (\<lambda>y. expr_1 y = max_val) xs);
xs_new = filter(\<lambda>y. y \<noteq> max_elem) xs
in xs_new)"


fun r :: "('a)formula_list list \<Rightarrow> enat"
  where
\<open>r xs = Max (set (map(\<lambda>x. expr_1 x) xs))\<close>


fun expr_3 :: "('a) formula_list \<Rightarrow> enat"
where
 expr_3_pos: \<open>expr_3 (HML_poss \<alpha> \<phi>) = expr_3 \<phi>\<close>
| expr_3_conj_right: \<open>expr_3 (HML_conj \<Phi> \<Psi>) = (Sup ((expr_1 ` (set \<Phi>)) \<union> (expr_3 ` (set \<Phi>)) \<union> (expr_3 ` (set \<Psi>))))\<close>

(*TODO*)
lemma expr_3_set: "expr_3 (HML_conj \<Phi> \<Psi>) =
Max({0} \<union> {expr_3 x | x. x \<in> set \<Phi>} \<union> {expr_3 y | y. y \<in> set \<Psi>} \<union> {expr_1 x | x. x \<in> set \<Phi>})"
  sorry

(* Neg := {i \<in> I| \<exists>\<phi>\<^sub>i. \<psi>\<^sub>i = \<not>\<phi>\<^sub>i}*)

fun 
  expr_4 :: "('a)formula_list \<Rightarrow> enat" 
where
"expr_4 (HML_poss a \<phi>) = expr_4 \<phi>" |
"expr_4 (HML_conj \<Phi> \<Psi>) = Sup ({expr_1 (HML_conj (pos_r \<Phi>) [])} \<union> (expr_4 ` (set \<Phi>)) \<union> (expr_4 ` (set \<Psi>)))"


(*Done*)
lemma expr_4_set: "expr_4 (HML_conj \<Phi> \<Psi>) =
Max ({expr_1 (HML_conj (pos_r \<Phi>)[])} \<union> {expr_4 x|x. x \<in> set \<Phi>} \<union> {expr_4 y|y. y \<in> set \<Psi>})"
  sorry

fun expr_5 :: "('a)formula_list \<Rightarrow> enat"
where
expr_5_pos:\<open>expr_5 (HML_poss \<alpha> \<phi>) = expr_5 \<phi>\<close>|
expr_5_conj: \<open>expr_5 (HML_conj \<Phi> \<Psi>) = 
(Sup ((expr_5 ` (set \<Phi>)) \<union> (expr_5 ` (set \<Psi>)) \<union> (expr_1 ` (set \<Psi>))))\<close> 

lemma expr_5_set: "expr_5 (HML_conj \<Phi> \<Psi>) = 
Max({0} \<union> {expr_5 x | x. x \<in> set \<Phi>} \<union> {expr_5 y | y. y \<in> set \<Psi>} \<union> {expr_1 y | y. y \<in> set \<Psi>})"
  sorry

find_theorems "enat" "Suc"

fun expr_6 :: "('a)formula_list \<Rightarrow> enat"
where
expr_6_pos: \<open>expr_6 (HML_poss \<alpha> \<phi>) = expr_6 \<phi>\<close>|
expr_6_conj: \<open>expr_6 (HML_conj \<Phi> \<Psi>) = 
(Sup ((expr_6 ` (set \<Phi>)) \<union> ((eSuc \<circ> expr_6) ` (set \<Psi>))))\<close>

(*TODO*)
lemma expr_6_set: "expr_6 (HML_conj \<Phi> \<Psi>) = 
Max({0} \<union> {expr_6 x | x. x \<in> set \<Phi>} \<union> {1 + expr_6 y | y. y \<in> set \<Psi>})"
  sorry

fun expr :: "('a)formula_list \<Rightarrow> enat \<times> enat \<times> enat \<times>  enat \<times> enat \<times> enat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>

find_theorems expr
thm Sup
thm Max_def
end