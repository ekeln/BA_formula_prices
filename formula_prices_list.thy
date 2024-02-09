theory formula_prices_list
  imports 
    Main
    HML_list
    "HOL-Library.Extended_Nat"
begin

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
                                 
end