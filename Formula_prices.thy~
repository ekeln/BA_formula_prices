theory Formula_prices
imports HML_def Main
begin

function expr_1 :: "('a, 'x) HML_formula \<Rightarrow>  nat"
and expr_neg_1 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
  where
expr_pos: \<open>expr_1 (HML_poss_2 \<alpha> \<phi>) = 1 + (expr_1 \<phi>)\<close>
| expr_1_conj: \<open>expr_1 (HML_conj_2 I F) = (Max ({(expr_neg_1 (F i)) |i. i\<in>I} \<union> {0}))\<close>
| expr_1_neg: \<open>expr_neg_1 (HML_neg_2 \<phi>) = expr_1 \<phi>\<close>
| expr_1_no_neg: \<open>expr_neg_1 (HML_no_neg \<phi>) = expr_1 \<phi>\<close>
| expr_1_true: \<open>expr_1 HML_true = 0\<close>
  apply (metis HML_formula.exhaust HML_neg_formula.exhaust old.sum.exhaust)
                apply simp+
  done
termination sorry

value "expr_1 (HML_conj_2 {} F)" (* 0 *)

function (sequential) expr_2 :: "('a, 'x) HML_formula \<Rightarrow> nat"
and expr_neg_2 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
where
expr_2_true: \<open>expr_2 HML_true = 1\<close>
| expr_2_pos: \<open>expr_2 (HML_poss_2 \<alpha> \<phi>) = expr_2 \<phi>\<close>
| expr_2_conj: \<open>expr_2 (HML_conj_2 I F) = (if I = {} then 1 else
  (Max ({(expr_neg_2 (F i)) |i. i\<in>I} \<union> {1+(Max {(expr_neg_2 (F i)) |i. i\<in>I})})))\<close> 
| expr_2_neg: \<open>expr_neg_2 (HML_neg_2 \<phi>) = expr_2 \<phi>\<close>
| expr_2_no_neg: \<open>expr_neg_2 (HML_no_neg \<phi>) = expr_2 \<phi>\<close>
  apply (metis HML_neg_formula.exhaust expr_1.cases old.sum.exhaust)
                apply simp+
  done
termination sorry

value "expr_2 (HML_poss_2 a HML_true)"
value "expr_2 (HML_conj_2 {} F)"

(* value "Max ({}::nat set)" *)


(*abbreviation neg_set :: "('a, 'x)HML_formula  \<Rightarrow> ('a, 'x) HML_neg_formula set"
  where
\<open>neg_set (HML_conj_2 I F) \<equiv> ({(F i) |i. i\<in>I \<and> (\<exists>f. (F i) = HML_neg_2 f)})\<close>*)

function (sequential) neg_set :: "('a, 'x)HML_formula \<Rightarrow> ('a, 'x) HML_neg_formula set"
  where
    "neg_set (HML_conj_2 I F) = (if I = {} then {} else {(F i) | i. i \<in> I \<and> (\<exists>f. (F i) = HML_neg_2 f)})"
  | "neg_set _ = {}"
  using expr_1.cases by blast+
termination sorry

value "card ({}::(nat set))"

lemma "neg_set (HML_poss_2 a HML_true) = {}"
  by simp

function (sequential) pos_set :: "('a, 'x)HML_formula \<Rightarrow> ('a, 'x) HML_neg_formula set" 
  where
\<open>pos_set (HML_conj_2 I F) = {(F i) |i. i\<in>I} - (neg_set (HML_conj_2 I F))\<close>
| \<open>pos_set _ = {}\<close>
  using neg_set.cases apply blast
       apply fastforce+
  done
termination sorry

value "pos_set (HML_conj_2 {} F)" 

function (sequential) r_set :: "('a, 'x)HML_formula \<Rightarrow>  ('a, 'x) HML_neg_formula set"
  where
\<open>r_set (HML_conj_2 I F) = 
(if (pos_set (HML_conj_2 I F)) = {} then {}
else {(F i) 
    |i. (F i) \<in> (pos_set (HML_conj_2 I F)) 
      \<and> (expr_neg_1 (F i)) = (Max {(expr_neg_1 (F j)) |j. (F j)\<in>(pos_set (HML_conj_2 I F))})})\<close> 
| \<open>r_set _ = {}\<close>
  using expr_1.cases apply blast
       apply simp+
  done
termination sorry

function expr_3 :: "('a, 'x) HML_formula \<Rightarrow> nat"
and expr_neg_3 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
where
expr_3_true: \<open>expr_3 HML_true = 0\<close>
| expr_3_pos: \<open>expr_3 (HML_poss_2 \<alpha> \<phi>) = expr_3 \<phi>\<close>
| expr_3_conj: \<open>expr_3 (HML_conj_2 I F) = (if I = {} then 0 else 
(Max ({(expr_neg_3 (F i)) |i. i\<in>I} \<union> {Max {(expr_neg_1 (F i))|i. (F i) \<in> (pos_set (HML_conj_2 I F))}})))\<close> (*TODO*)
| expr_3_neg: \<open>expr_neg_3 (HML_neg_2 \<phi>) = expr_3 \<phi>\<close>
| expr_3_no_neg: \<open>expr_neg_3 (HML_no_neg \<phi>) = expr_3 \<phi>\<close>
apply (metis expr_1.cases expr_neg_2.cases obj_sumE)
                apply simp+
  done
termination sorry

value "expr_3 (HML_poss_2 a HML_true)"
value "expr_3 (HML_conj_2 {} F)"


(* Neg := {i \<in> I| \<exists>\<phi>\<^sub>i. \<psi>\<^sub>i = \<not>\<phi>\<^sub>i}*)


function expr_4 :: "('a, 'x) HML_formula \<Rightarrow> nat"
and expr_neg_4 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
where
expr_4_true: \<open>expr_4 HML_true = 1\<close>
| expr_4_pos: \<open>expr_4 (HML_poss_2 \<alpha> \<phi>) = expr_4 \<phi>\<close>
| expr_4_conj: \<open>expr_4 (HML_conj_2 I F) = (if I = {} then 0 else 
 (Max ({(expr_neg_4 (F i)) |i. i\<in>I} \<union> {Max {(expr_neg_1 (F i))|i. (F i) \<in> ((pos_set (HML_conj_2 I F)) - (r_set (HML_conj_2 I F)))}})))\<close> (*TODO*)
| expr_4_neg: \<open>expr_neg_4 (HML_neg_2 \<phi>) = expr_4 \<phi>\<close>
| expr_4_no_neg: \<open>expr_neg_4 (HML_no_neg \<phi>) = expr_4 \<phi>\<close>
apply (metis expr_1.cases expr_neg_3.cases obj_sumE)
apply simp+
  done
termination sorry

function expr_5 :: "('a, 'x) HML_formula \<Rightarrow> nat"
and expr_neg_5 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
where
expr_5_true: \<open>expr_5 HML_true = 0\<close>
| expr_5_pos: \<open>expr_5 (HML_poss_2 \<alpha> \<phi>) = expr_5 \<phi>\<close>
| expr_5_conj: \<open>expr_5 (HML_conj_2 I F) = (if I = {} then 0 else 
(Max ({(expr_neg_5 (F i)) |i. i\<in>I} \<union> {Max {(expr_neg_1 (F i))|i. (F i) \<in> (neg_set (HML_conj_2 I F))}})))\<close> (*TODO*)
| expr_5_neg: \<open>expr_neg_5 (HML_neg_2 \<phi>) = expr_5 \<phi>\<close>
| expr_5_no_neg: \<open>expr_neg_5 (HML_no_neg \<phi>) = expr_5 \<phi>\<close>
                 apply (metis HML_neg_formula.exhaust expr_4.cases sumE)
                apply simp+
  done
termination sorry


function expr_6 :: "('a, 'x) HML_formula \<Rightarrow> nat"
and expr_neg_6 :: "('a, 'x)HML_neg_formula \<Rightarrow> nat"
where
expr_6_true: \<open>expr_6 HML_true = 0\<close>
| expr_6_pos: \<open>expr_6 (HML_poss_2 \<alpha> \<phi>) = expr_6 \<phi>\<close>
| expr_6_conj: \<open>expr_6 (HML_conj_2 I F) = (Max ({0} \<union> {(expr_neg_6 (F i)) |i. i\<in>I}))\<close> (*TODO*)
| expr_6_neg: \<open>expr_neg_6 (HML_neg_2 \<phi>) = 1 + expr_6 \<phi>\<close>
| expr_6_no_neg: \<open>expr_neg_6 (HML_no_neg \<phi>) = expr_6 \<phi>\<close>
                 apply (metis HML_neg_formula.exhaust expr_5.cases obj_sumE)
                apply simp+
  done

fun expr :: "('a, 'x)HML_formula \<Rightarrow> nat \<times> nat \<times> nat \<times>  nat \<times> nat \<times> nat" 
  where
\<open>expr \<phi> = (expr_1 \<phi>, expr_2 \<phi>, expr_3 \<phi>, expr_4 \<phi>, expr_5 \<phi>, expr_6 \<phi>)\<close>

(*<a>\<And>{\<not><a>}*)
value "expr (HML_conj_2 {} F)"
value "expr ((HML_poss_2 a) HML_true)" 


thm Sup
thm Max_def

value "Max {}"
value "(Max \<emptyset>)"

end