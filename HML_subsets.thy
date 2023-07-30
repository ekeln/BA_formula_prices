theory HML_subsets
  imports 
    Main
    HML_list
  formula_prices_list
begin

datatype inat = N nat | Inf

value "(Inf, N 1, N 0) :: inat \<times> inat \<times> inat"

fun less_eq :: "nat \<Rightarrow> inat \<Rightarrow> bool"
where
  "less_eq n (N m) = (n \<le> m)" |
  "less_eq _ Inf = True"

fun less_eq_t :: "(nat \<times> nat \<times> nat \<times> nat \<times> nat \<times> nat) \<Rightarrow> (inat \<times> inat \<times> inat \<times> inat \<times> inat \<times> inat) \<Rightarrow> bool"
  where
"less_eq_t (n1, n2, n3, n4, n5, n6) (i1, i2, i3, i4, i5, i6) =
    (less_eq n1 i1 \<and> less_eq n2 i2 \<and> less_eq n3 i3 \<and> less_eq n4 i4 \<and> less_eq n5 i5 \<and> less_eq n6 i6)"

lemma "(\<phi> \<in> HML_traces) = (less_eq_t (expr \<phi>) (Inf, N 1, N 0, N 0, N 0, N 0))"
  oops

end