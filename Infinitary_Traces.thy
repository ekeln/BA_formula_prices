theory Infinitary_Traces
  imports Transition_Systems
Relational_Equivalences
"HOL-Library.Stream"
begin

(*Taken from https://isabelle.in.tum.de/dist/Isabelle2023/doc/datatypes.pdf section 4
Statt streams, weil es in der Isabelle definition keinen leeren stream gibt?!*)
codatatype (lset: 'a) llist =
lnull: LNil ("l[]")
| LCons (lhd: 'a) (ltl: "'a llist ") (infixr \<open>##\<close> 65)
for
map:lmap
rel: llist_all2
where
"lhd LNil = undefined" |
"ltl LNil = LNil"

find_theorems lset

fun list_to_llist :: "'a list \<Rightarrow> 'a llist" where
"list_to_llist [] = LNil" |
"list_to_llist (x#xs) = LCons x (list_to_llist xs)"

fun length_bound_llist :: "nat \<Rightarrow> 'a llist \<Rightarrow> bool" where
  "length_bound_llist 0 l[] = True" |
  "length_bound_llist (Suc v) l[] = False" |
  "length_bound_llist (Suc n) (x##xs) = length_bound_llist n xs" |
  "length_bound_llist 0 (v ## va) = False"

definition finite_llist where
"finite_llist xs = (\<exists>n. length_bound_llist n xs)"

lemma n_lower_bound: 
  assumes "length_bound_llist n xs" "m < n"
  shows "\<not> (length_bound_llist m xs)"
  using assms proof (induction n arbitrary: xs m)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain y ys where "xs = y##ys" 
    using length_bound_llist.simps(2) llist.exhaust_sel by blast
  hence "length_bound_llist n ys" using Suc 
    by (meson length_bound_llist.simps(3))
  hence "\<forall>m < n. \<not> length_bound_llist m ys" using Suc by blast
  then show ?case using Suc \<open>xs = y##ys\<close> 
    by (metis length_bound_llist.simps(3) length_bound_llist.simps(4) less_Suc_eq_0_disj)
qed

function llist_to_list :: "'a llist \<Rightarrow> 'a list" where
  "llist_to_list xs = (if finite_llist xs then (case xs of l[] \<Rightarrow> [] | (x##xs') \<Rightarrow> x # llist_to_list xs') else [])"
  by simp+

find_theorems llist_to_list

primcorec llist_app :: "'a llist \<Rightarrow> 'a llist \<Rightarrow> 'a llist" where
  "llist_app xs ys = (case xs of LNil \<Rightarrow> ys | LCons x xs' \<Rightarrow> LCons x (llist_app xs' ys))"

context lts begin

(*Für infinite traces*)
coinductive inf_step_sequence :: \<open>'s \<Rightarrow> 'a llist \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>$\<infinity> _ _\<close>[70,70,70] 80) where
\<open>p \<mapsto>$\<infinity> LNil p\<close> |
\<open>p \<mapsto>$\<infinity> (LCons a rt) p''\<close> if \<open>\<exists>p'. p \<mapsto> a p' \<and> p' \<mapsto>$\<infinity> rt p''\<close> 

definition finite_inf_step_sequence :: "'s \<Rightarrow> 'a llist \<Rightarrow> 's \<Rightarrow> bool" where
"finite_inf_step_sequence p xs p' \<equiv> inf_step_sequence p xs p' \<and> finite_llist xs"

primcorec infinite_a_llist :: "'a \<Rightarrow> 'a llist" where
  "infinite_a_llist x = LCons x (infinite_a_llist x)"

find_theorems infinite_a_llist

lemma "infinite (lset (infinite_a_llist a))"
  oops

definition llist_has_last_elem where
"llist_has_last_elem xs \<equiv> \<exists>hd e. xs = (llist_app (hd) (LCons e LNil))"

lemma infinite_llist_is_inf: "\<not> (llist_has_last_elem (infinite_a_llist a))"
  unfolding llist_has_last_elem_def
proof
  assume "\<exists>hd e. infinite_a_llist a = llist_app hd (e ## l[])"
  then obtain hd e where "infinite_a_llist a = llist_app hd (e ## l[])" by auto
  hence "... = llist_app hd (LCons e l[])" by simp
  have "finite (lset hd)" using \<open>infinite_a_llist a = llist_app hd (e ## l[])\<close> sorry
  then have "(e ## l[]) = infinite_a_llist a" using infinite_a_llist.simps  sorry
  thus False 
    by (metis infinite_a_llist.simps(3) llist.distinct(1) llist.sel(3)) 
qed

lemma "\<not> (finite_llist (infinite_a_llist a))"
proof
  assume "finite_llist (infinite_a_llist a)"
  then show False 
    by (metis finite_llist_def length_bound_llist.simps(3) lessI lts.infinite_a_llist.code n_lower_bound)
qed

lemma list_has_last_elem:
  assumes "xs \<noteq> []"
  shows "\<exists>hd e. xs = hd@(e#[])"
using assms proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof(cases xs)
    case Nil
    then show ?thesis 
      by blast
  next
    case (Cons b list)
    then obtain hd e where "xs = hd @ [e]" 
      using Cons.IH by blast
    hence "a#xs = [a]@hd@[e]" using Cons 
      by simp
    then show ?thesis 
      using \<open>xs = hd @ [e]\<close> by simp
  qed
qed

lemma list_to_llist_has_last_element:
  assumes "xs \<noteq> []"
  shows "\<exists>ys. \<exists>zs. list_to_llist xs = LCons ys zs \<and> (\<forall>zs'. zs \<noteq> zs' \<longrightarrow> list_to_llist xs \<noteq> LCons ys zs')"
  using assms proof(induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof(cases xs)
    case Nil
    then have "list_to_llist (a # xs) = LCons a (LNil)" using list_to_llist.simps by auto
    hence "\<exists>ys zs. list_to_llist (a # xs) = LCons ys zs " by blast
    have "\<nexists>ys. list_to_llist (a # xs) = LCons a (ys) \<and> (ys \<noteq> LNil)"
      using \<open>list_to_llist (a # xs) = LCons a LNil\<close> by force
    then show ?thesis using \<open>list_to_llist (a # xs) = LCons a (LNil)\<close> 
      by blast
  next
    case (Cons a list)
    then have "xs \<noteq> []" by simp
  hence "\<exists>ys zs. list_to_llist xs = LCons ys zs \<and> (\<forall>zs'. zs \<noteq> zs' \<longrightarrow> list_to_llist xs \<noteq> LCons ys zs')"
    using Cons.IH by blast
  then show ?thesis by simp
  qed
qed


(*Problem: LNil ist verschachtelt*)
lemma list_has_last_elem:
  shows "\<forall>xs::'a list. (\<exists>a tail. xs = a#tail) \<longrightarrow> (\<exists>ys. list_to_llist xs = LCons ys LNil)"
  oops

lemma no_list_like_infinite_llist:
  assumes "infinite_a_llist a = tr"
  shows "\<nexists>fin_tr. list_to_llist fin_tr = tr"
proof
  assume "\<exists>fin_tr. list_to_llist fin_tr = tr"
  then obtain fin_tr where "list_to_llist fin_tr = tr" by auto
  then show False proof(cases "fin_tr = []")
    case True
    then show ?thesis 
      using \<open>list_to_llist fin_tr = tr\<close> assms infinite_a_llist.disc_iff llist.discI(1) by fastforce
  next
    case False
    hence "\<exists>hd e. fin_tr = hd @ [e]"
      using list_has_last_elem by blast
    hence "\<exists>hd e. list_to_llist fin_tr = llist_app hd (e ## l[])"
    proof
      fix hd
      assume "\<exists>e. fin_tr = hd @ [e]"
      then show ?thesis
        sorry
    qed
    have "\<not> (\<exists>hd e. list_to_llist fin_tr = (llist_app (hd) (LCons e LNil)))"
      using infinite_llist_is_inf
      using \<open>list_to_llist fin_tr = tr\<close> assms llist_has_last_elem_def by fastforce
    thus False using \<open>\<exists>hd e. list_to_llist fin_tr = llist_app hd (e ## l[])\<close>
      by blast
  qed
qed

find_theorems inf_step_sequence

abbreviation inf_traces :: "'s \<Rightarrow> 'a llist set" where
\<open>inf_traces p \<equiv> {tr. \<exists>p'. p \<mapsto>$\<infinity> tr p'}\<close>

abbreviation all_inf_traces :: "'a llist set" where
"all_inf_traces \<equiv>{tr. \<exists>p p'. p \<mapsto>$\<infinity> tr p'}"

text \<open>Trace preorder as inclusion of trace sets\<close>

definition inf_trace_preordered (infix \<open>\<lesssim>T\<infinity>\<close> 60)where
\<open>inf_trace_preordered p q \<equiv> inf_traces p \<subseteq> inf_traces q\<close>

text \<open>Trace equivalence as mutual preorder\<close>

abbreviation inf_trace_equivalent (infix \<open>\<simeq>T\<infinity>\<close> 60) where
\<open>p \<simeq>T\<infinity> q \<equiv> p \<lesssim>T\<infinity> q \<and> q \<lesssim>T\<infinity> p\<close>

lemma traces_in_inf_traces:
  "\<forall>tr \<in> traces p. \<exists>itr. itr \<in> inf_traces p \<and> list_to_llist tr = itr"
proof
  fix tr
  assume "tr \<in> traces p"
  then show "\<exists>itr. itr \<in> inf_traces p \<and> list_to_llist tr = itr" proof(induction tr arbitrary: p)
    case Nil
    have "list_to_llist [] = LNil" 
      using list_to_llist.simps(1) by blast
    have "LNil \<in> inf_traces p" 
      using lts.inf_step_sequence.intros(1) by force
    then show ?case using \<open>list_to_llist [] = LNil\<close> by blast
  next
    case (Cons a rt)
    then obtain p' p'' where "p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''" 
      using step_sequence.cases by force
    with Cons obtain itr where "itr \<in> inf_traces p'" "list_to_llist rt = itr"
      by fastforce
    have "list_to_llist (a#rt) = (a##itr)" 
      using \<open>list_to_llist rt = itr\<close> by auto
    have "(a##itr) \<in> inf_traces p" using \<open>itr \<in> inf_traces p'\<close> \<open>p \<mapsto> a p' \<and> p' \<mapsto>$ rt p''\<close>
      using inf_step_sequence.intros(2) by blast
    then show ?case using \<open>list_to_llist (a#rt) = (a##itr)\<close> by blast
  qed
qed

lemma list_is_finite_llist: "finite_llist (list_to_llist tr)"
  by((induction tr), (metis finite_llist_def length_bound_llist.simps list_to_llist.simps)+)

lemma finite_inf_trace_to_trace:
  assumes "finite_llist itr" "itr \<in> inf_traces p"
  shows "llist_to_list itr \<in> traces p"
proof(rule ccontr)
  assume "llist_to_list tr \<notin> traces p"
  obtain 

lemma inf_trace_implies_trace_preorder:
  assumes "p \<lesssim>T\<infinity> q"
  shows "p \<lesssim>T q"
  using assms unfolding inf_trace_preordered_def trace_preordered_def 
proof-
  assume "inf_traces p \<subseteq> inf_traces q"
  have "\<forall>tr \<in> traces p. tr \<in> traces q" proof
    fix tr
    assume "tr \<in> traces p"
    then obtain itr where "itr \<in> inf_traces p \<and> list_to_llist tr = itr"
      using traces_in_inf_traces by blast
    hence "itr \<in> inf_traces q" 
      using assms \<open>inf_traces p \<subseteq> inf_traces q\<close> by blast
    have "finite_llist itr"
      using finite_llist_def length_bound_llist.simps(1) list_is_finite_llist \<open>itr \<in> inf_traces p \<and> list_to_llist tr = itr\<close> 
      by blast 
    then have "llist_to_list itr = tr"sorry
    then show "tr \<in> traces q" using \<open>itr \<in> inf_traces q\<close> \<open>itr \<in> inf_traces p \<and> list_to_llist tr = itr\<close> \<open>tr \<in> traces p\<close>
      \<open>finite_llist itr\<close> \<open>llist_to_list itr = tr\<close>
      sorry
      by (metis )
  qed
  then show "traces p \<subseteq> traces q"
    by blast
qed



lemma inf_trace_implies_trace_equivalence:
  assumes "p \<simeq>T\<infinity> q"
  shows "p \<simeq>T q"
  using assms inf_trace_implies_trace_preorder by blast

lemma
"\<exists>p. traces p \<noteq> "


lemma 
  fixes p q a
  shows "\<not> (p \<simeq>T q \<longrightarrow> p \<simeq>T\<infinity> q)"
proof
  assume "p \<simeq>T q \<longrightarrow> p \<simeq>T\<infinity> q" 
  assume "p \<simeq>T q"
  hence "\<forall>tr \<in> inf_traces p. tr \<in> inf_traces q" 
    using lts.inf_trace_preordered_def \<open>p \<simeq>T q \<longrightarrow> p \<simeq>T\<infinity> q\<close> by fastforce
  have "infinite_llist a \<in> "
  then obtain tr where 
  show "p \<simeq>T q \<longrightarrow> p \<simeq>T\<infinity> q \<Longrightarrow> False" sledgehammer
  
  sorry
end
end