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
"(\<phi>, \<psi>) \<in> subformula_rel \<Longrightarrow> (\<phi> ,(HML_poss \<alpha> \<psi>)) \<in> subformula_rel"

lemma wf_subformula_rel: "wf {(\<phi>, \<psi>). (\<phi>, \<psi>) \<in> subformula_rel \<and> modal_depth \<phi> < modal_depth \<psi>}"
  by (metis (mono_tags, lifting) case_prod_conv in_measure mem_Collect_eq wfUNIVI wf_induct_rule wf_measure)
  
thm wf_measure
thm HML_list.formula_list.exhaust

fun expr_1 :: "('a)formula_list \<Rightarrow>  nat"
  where
expr_1_conj_empty:\<open>expr_1 (HML_conj [] []) = 0\<close> |
expr_1_conj: \<open>expr_1 (HML_conj (x#xs) \<Psi>) = (Max ({0} \<union> {expr_1 x} \<union> {expr_1 (HML_conj xs \<Psi>)}))\<close> |
expr_1_conj_right:\<open>expr_1 (HML_conj [] (y#ys)) = (Max ({0} \<union> {expr_1 y} \<union> {expr_1 (HML_conj [] ys)}))\<close> |
expr_1_pos: \<open>expr_1 (HML_poss \<alpha> \<phi>) = 
  1 + (expr_1 \<phi>)\<close>

value "expr_1 (HML_conj ([]::nat formula_list list) ([]::nat formula_list list))"
value"set ([HML_conj [] []]::nat formula_list list)"

value "expr_1 (HML_conj [] [a])" (* 0 *)
(*TODO: überprüfen*)
fun expr_2 :: "('a)formula_list \<Rightarrow>  nat"
  where
expr_2_conj_empty:\<open>expr_2 (HML_conj [] []) = 1\<close> |
expr_2_conj: \<open>expr_2 (HML_conj (x#xs) \<Psi>) = (Max ({1 + expr_2 x} \<union> {expr_2 (HML_conj xs \<Psi>)}))\<close> |
expr_2_conj_right:\<open>expr_2 (HML_conj [] (y#ys)) = (Max ({1 + expr_2 y} \<union> {expr_2 (HML_conj [] ys)}))\<close> |
expr_2_pos: \<open>expr_2 (HML_poss \<alpha> \<phi>) = expr_2 \<phi>\<close>

(*Für formula_list Definition: Menge Pos ist \<Phi>, Menge Ng ist \<Phi>.?!*)

(*Pos\R ist (pos_comp_r Pos)*)
fun pos_comp_r :: "('a)formula_list list \<Rightarrow> ('a)formula_list list"
  where
\<open>pos_comp_r [] = []\<close> |
\<open>pos_comp_r [x] = []\<close> |
\<open>pos_comp_r (x # y # zs) = (if expr_1 x > expr_1 y then y # (pos_comp_r (x#zs)) else x # (pos_comp_r (y # zs)))\<close>

fun r :: "('a)formula_list list \<Rightarrow> nat"
  where
\<open>r xs = Max (set (map(\<lambda>x. expr_1 x) xs))\<close>


(*TODO: überprüfen*)
fun expr_3 :: "('a) formula_list \<Rightarrow> nat"
where
 expr_3_pos: \<open>expr_3 (HML_poss \<alpha> \<phi>) = expr_3 \<phi>\<close>
| expr_3_conj_emtpy: \<open>expr_3 (HML_conj [] []) = 0\<close>
| expr_3_conj_right: \<open>expr_3 (HML_conj [] (y#ys)) = Max ({0} \<union> {expr_3 y} \<union> {expr_3 (HML_conj [] ys)})\<close>
| expr_3_conj: \<open>expr_3 (HML_conj (x#xs) \<Psi>) = 
Max ({0} \<union> {expr_1 x} \<union> {expr_3 (HML_conj xs \<Psi>)} \<union> {expr_3 x})\<close>


(* Neg := {i \<in> I| \<exists>\<phi>\<^sub>i. \<psi>\<^sub>i = \<not>\<phi>\<^sub>i}*)

fun expr_4 :: "('a)formula_list \<Rightarrow> nat"
where
 expr_4_pos: \<open>expr_4 (HML_poss \<alpha> \<phi>) = expr_4 \<phi>\<close> |
expr_4_conj_empty: \<open>expr_4 (HML_conj [] []) = 0\<close>|
expr_4_conj_right: \<open>expr_4 (HML_conj [] (y#ys)) = Max ({0} \<union> {expr_4 y} \<union> {expr_4 (HML_conj [] ys)})\<close>|
expr_4_conj: \<open>expr_4 (HML_conj (x#xs) \<Psi>) = 
Max ({0} \<union> {expr_4 x} \<union> {expr_4 (HML_conj xs \<Psi>)})\<close>

fun expr_4_r :: "('a)formula_list \<Rightarrow> nat"
  where
\<open>expr_4_r (HML_conj (x#xs) \<Psi>) = Max({expr_1 x} \<union> {expr_4_r (HML_conj xs \<Psi>)})\<close>|
\<open>expr_4_r _ = 0\<close>

fun expr_4_pre :: "('a)formula_list \<Rightarrow> nat" 
  where
pre_conj: \<open>expr_4_pre (HML_conj \<Phi> \<Psi>) = 
Max ({expr_4 (HML_conj \<Phi> \<Psi>)} \<union> {expr_4_r (HML_conj (pos_comp_r \<Phi>) \<Psi>)})\<close> |
\<open>expr_4_pre \<phi> = expr_4 \<phi>\<close>


fun expr_5 :: "('a)formula_list \<Rightarrow> nat"
where
expr_5_pos:\<open>expr_5 (HML_poss \<alpha> \<phi>) = expr_5 \<phi>\<close>|
expr_5_conj_empty: \<open>expr_5 (HML_conj [] []) = 0\<close> |
expr_5_conj: \<open>expr_5 (HML_conj (x#xs) \<Psi>) = Max ({0} \<union> {expr_5 x} \<union> {expr_5 (HML_conj xs \<Psi>)})\<close> |
expr_5_conj_2: 
\<open>expr_5 (HML_conj [] (y#ys)) = Max ({0} \<union> {expr_5 y} \<union> {expr_5 (HML_conj [] ys)} \<union> {expr_1 y})\<close>


fun expr_6 :: "('a)formula_list \<Rightarrow> nat"
where
expr_6_pos: \<open>expr_6 (HML_poss \<alpha> \<phi>) = expr_6 \<phi>\<close>|
expr_6_conj_empty: \<open>expr_6 (HML_conj [] []) = 0\<close>|
expr_6_conj: \<open>expr_6 (HML_conj (x#xs) \<Psi>) = Max({0} \<union> {expr_6 x} \<union> {expr_6 (HML_conj xs \<Psi>)})\<close> |
expr_6_conj_2: \<open>expr_6 (HML_conj [] (y#ys)) = Max({0}  \<union> {1 + expr_6 y} \<union> {expr_6 (HML_conj [] ys)})\<close>

fun expr :: "('a)formula_list \<Rightarrow> nat \<times> nat \<times> nat \<times>  nat \<times> nat \<times> nat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4_pre \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>

(*<a>\<And>{\<not><a>}*)

value "expr (HML_conj_2 {} F)"
value "expr ((HML_poss_2 a) HML_true)" 


thm Sup
thm Max_def

value "Max {}"
value "(Max \<emptyset>)"
end