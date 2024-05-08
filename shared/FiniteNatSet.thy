theory FiniteNatSet
  imports Main HOL.Finite_Set

begin

definition fset_sum :: "'a set \<Rightarrow> ('a \<Rightarrow> nat) \<Rightarrow> nat" where
  "fset_sum s f = Finite_Set.fold (\<lambda> x acc. (f x) + acc) 0 s"

interpretation fset_commute: \<comment> \<open>We need this to make \<open>fset_sum\<close> commute.\<close>
  comp_fun_commute_on "UNIV" "(\<lambda> a b. (f a) + b) :: 'a \<Rightarrow> nat \<Rightarrow> nat"
  by unfold_locales auto

lemma fset_sum_empty: "fset_sum {} f = 0"
  by (simp add: fset_sum_def)

lemma fset_sum_single: "fset_sum {x} f = f x"
  by (simp add: fset_sum_def)

lemma fset_sum_pair:
  assumes "x \<noteq> y"
  shows "fset_sum {x, y} f = f x + f y"
  by (simp add: assms fset_sum_def)


lemma fset_sum_union_one: 
  assumes "x \<notin> A" and "finite A"
  shows "fset_sum (A \<union> {x}) f = fset_sum A f + f x"
proof -
  have "fset_sum (A \<union> {x}) f = f x + fset_sum A f"
    by (simp add: assms(1) assms(2) fset_sum_def)
  then show ?thesis
    by presburger
qed

lemma fset_sum_union:
  assumes "A \<inter> B = {}" and "finite A" and "finite B"
  shows "fset_sum (A \<union> B) f = fset_sum A f + fset_sum B f"
proof -
  have ?thesis using assms(3) assms(1)
  proof (induction B rule: finite_induct)
    case empty
    then show ?case by (simp add: fset_sum_empty)
  next
    case (insert x F)
    have "fset_sum (F \<union> {x}) f = fset_sum F f + fset_sum {x} f"
      by (metis fset_sum_single fset_sum_union_one insert.hyps(1) insert.hyps(2))
    have "fset_sum (A \<union> F) f = fset_sum A f + fset_sum F f"
      using insert.IH insert.prems by force
    have "x \<notin> A"
       using insert.hyps(1) assms(1) insert.prems by fastforce 
    then have "fset_sum (A \<union> (F \<union> {x})) f = fset_sum A f + fset_sum (F \<union> {x}) f"
      by (smt (verit, del_insts) Un_iff \<open>fset_sum (A \<union> F) f = fset_sum A f + fset_sum F f\<close> add.assoc assms(2) finite_Un fold_infinite fset_sum_def fset_sum_union_one insert.hyps(2) sup_assoc)
    thus ?case
      by auto
  qed

  thus ?thesis
    by simp
qed

lemma fset_sum_diff:
  assumes "B \<subseteq> A" and "finite A" and "finite B"
  shows "fset_sum (A - B) f = fset_sum A f - fset_sum B f"
  by (metis Diff_disjoint Diff_partition add_diff_cancel_left' assms(1) assms(2) assms(3) finite_Diff2 fset_sum_union)

lemma nat_sum_ge_any_elem:
  fixes S :: "'a set"
    and e :: "'a"
    and f :: "('a \<Rightarrow> nat)" 
  assumes "S \<noteq> {}"
    and "finite S"
    and "e \<in> S"
  shows "(fset_sum S f) \<ge> (f e)"
  by (metis (mono_tags, lifting) add_le_cancel_left assms(2) assms(3) bot.extremum fset_sum_def nat_arith.rule0 fset_commute.fold_rec top_greatest)

lemma fset_sum_over_positives_is_positive:
  assumes nonempty: "S \<noteq> {}"
    and fin: "finite S"
    and pos: "\<forall>x \<in> S. f x > 0"
  shows "fset_sum S f > 0"
  by (metis bot_nat_0.not_eq_extremum ex_in_conv fin linorder_not_le nat_sum_ge_any_elem nonempty pos)

definition fset_unique :: "'o set \<Rightarrow> ('o \<Rightarrow> 'i) \<Rightarrow> bool" where 
  "fset_unique S id_func = (\<forall>o1 o2. o1 \<in> S \<and> o2 \<in> S \<and> o1 \<noteq> o2 \<longrightarrow> id_func o1 \<noteq> id_func o2)"

definition fset_injective :: "'o set \<Rightarrow> ('o \<Rightarrow> 'i) \<Rightarrow> bool" where 
  "fset_injective S id_func = (\<forall>o1 o2. o1 \<in> S \<and> o2 \<in> S \<and> id_func o1 = id_func o2 \<longrightarrow> o1 = o2)"

lemma fset_unique_implies_injective_on:
  assumes "fset_unique S f"
  shows "fset_injective S f"
unfolding fset_injective_def fset_unique_def
using assms
  by (meson fset_unique_def)


definition fset_intersect :: "'o set \<Rightarrow> 'o set \<Rightarrow> ('o \<Rightarrow> 'i) \<Rightarrow> 'o set" where
  "fset_intersect S1 S2 id_func = {o1 \<in> S1. \<exists>o2 \<in> S2. id_func o1 = id_func o2}"

definition fset_map :: "'o set \<Rightarrow> ('o \<Rightarrow> 'a) \<Rightarrow> 'a set" where
  "fset_map S f = {f a | a. a \<in> S}"

lemma fset_sum_injective_uses_fset_map:
  assumes "finite S"
    and "fset_injective S f"
  shows "fset_sum (f ` S) id = fset_sum S f"
proof -
  have fin_fS: 
    "finite (f ` S)"
    by (simp add: assms(1))
  have inj_on_f: "inj_on f S"
    unfolding fset_injective_def inj_on_def
    by (meson assms(2) fset_injective_def)
  have "fset_sum (f ` S) id = Finite_Set.fold (\<lambda>x y. id x + y) 0 (f ` S)"
    unfolding fset_sum_def by simp
  also have "... = Finite_Set.fold (\<lambda>x y. x + y) 0 (f ` S)"
    by simp
  also from inj_on_f have "... = Finite_Set.fold (\<lambda>x y. (f x) + y) 0 S"
    using assms(1) fin_fS fold_image
    by (smt (verit, best) UNIV_I comp_eq_dest_lhs fold_closed_eq) 
  also have "... = fset_sum S f"
    unfolding fset_sum_def by simp
  finally show ?thesis .
qed

definition fset_filter :: "'o set \<Rightarrow> ('o \<Rightarrow> bool) \<Rightarrow> 'o set" where
  "fset_filter S p = {e \<in> S. p e}"

lemma diff_subset:
  fixes A :: "'t set"
    and B :: "'t set"
  assumes "diff = A - B"
  shows "diff = A - B \<Longrightarrow> diff \<subseteq> A"
  by simp

lemma fset_map_linear:
  fixes A :: "'u set"
    and B :: "'u set"
    and f :: "'u \<Rightarrow> 'i"
  shows "(fset_map A f \<union> fset_map B f) = fset_map (A \<union> B) f"
proof
  show "fset_map A f \<union> fset_map B f \<subseteq> fset_map (A \<union> B) f"
    by (smt (verit, del_insts) Un_iff fset_map_def mem_Collect_eq subsetI)
  show "fset_map (A \<union> B) f \<subseteq> fset_map A f \<union> fset_map B f"
    by (smt (verit, ccfv_threshold) Un_iff fset_map_def mem_Collect_eq subsetI)
qed

lemma fset_unique_linear:
  fixes A :: "'u set"
    and B :: "'u set"
    and f :: "'u \<Rightarrow> 'i"
  assumes "fset_unique A f"
    and "fset_unique B f"
    and "(fset_map A f) \<inter> (fset_map B f) = {}"
  shows "fset_unique (A \<union> B) f"
proof-
  have "(fset_map A f) \<union> (fset_map B f) = fset_map (A \<union> B) f"
    by (simp add: fset_map_linear)
  then have "\<exists>u. u \<in> A \<longrightarrow> f u \<notin> (fset_map B f)"
    using assms(3) fset_map_def by fastforce
  then have "\<exists>u. u \<in> B \<longrightarrow> f u \<notin> (fset_map A f)"
    by (metis UnI2 Un_Int_eq(3) \<open>fset_map A f \<union> fset_map B f = fset_map (A \<union> B) f\<close> assms(3) empty_iff set_eq_iff)
  thus ?thesis
    by (smt (verit, del_insts) IntI Un_iff assms(1) assms(2) assms(3) empty_iff fset_map_def fset_unique_def mem_Collect_eq)
qed

lemma fset_unique_unfold:
  assumes "fset_unique A f"
    and "a1 \<in> A \<and> a2 \<in> A"
    and "a1 \<noteq> a2"
  shows "f a1 \<noteq> f a2"
  by (meson assms(1) assms(2) assms(3) fset_unique_def)

lemma fset_map_preserves_finite:
  assumes "finite A"
  shows "finite (fset_map A f)"
proof -
  from assms show ?thesis
    unfolding fset_map_def
    by simp
qed

lemma fset_map_empty:
  assumes "A = {}"
  shows "fset_map A f = {}"
  by (simp add: assms fset_map_def)
              
lemma fset_map_single:
  assumes "A = {a}"
  shows "fset_map A f = { (f a) }"
  by (simp add: assms fset_map_def)

lemma fset_sum_map_transitive_pair:
  assumes "A = {a, b}"
      and "f a \<noteq> f b"
    shows "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
  by (metis (mono_tags, lifting) assms(1) assms(2) fset_map_linear fset_map_single fset_sum_pair insert_is_Un)

lemma fset_sum_map_transitive_pair2:
  assumes "A = {a, b}"
      and "fset_unique A f"
    shows "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
  by (metis (mono_tags, lifting) assms(1) assms(2) fset_map_single fset_sum_map_transitive_pair fset_sum_single fset_unique_unfold insertCI insert_absorb2)


lemma fset_sum_map_transitive_union:
  assumes "finite A"
      and "fset_unique A f"
      and "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
      and "x \<notin> A"
      and "AN = A \<union> {x}"
      and "fset_unique AN f"
    shows "fset_sum (fset_map AN f) g = fset_sum AN (\<lambda>x. g (f x))"
proof-
  have "fset_sum (fset_map AN f) g
    = fset_sum (fset_map A f) g + g (f x)"
    using assms fset_map_def fset_map_linear fset_map_preserves_finite fset_map_single fset_sum_union_one fset_unique_def
  proof -
    have f1: "finite (fset_map A f)"
      using assms(1) fset_map_preserves_finite by blast
    obtain aa :: "'b \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a" where
      f2: "\<forall>x0 x1 x2. (\<exists>v3. x0 = x1 v3 \<and> v3 \<in> x2) = (x0 = x1 (aa x0 x1 x2) \<and> aa x0 x1 x2 \<in> x2)"
      by moura
    have "\<forall>a aa. a \<notin> A \<union> {x} \<or> aa \<notin> A \<union> {x} \<or> a = aa \<or> f a \<noteq> f aa"
      by (metis (full_types) assms(5) assms(6) fset_unique_def)
    then have "\<nexists>a. f x = f a \<and> a \<in> A"
      using f2 assms(4) by blast
    then have "f x \<notin> fset_map A f"
      by (simp add: fset_map_def)
    then show ?thesis
      using f1 by (smt (z3) assms(5) fset_map_linear fset_map_single fset_sum_union_one)
  qed
    
  thus ?thesis
    by (metis assms(1) assms(3) assms(4) assms(5) fset_sum_union_one)
qed

lemma fset_sum_map_transitive:
  assumes "finite A"
      and "fset_unique A f"
    shows "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
proof-
  have ?thesis
    using assms
  proof (induction A)
    case empty
    then show ?case
      by (simp add: fset_map_empty fset_sum_empty)
  next
    case (insert x A)
    have "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
      by (metis (mono_tags, lifting) fset_unique_def insert.IH insert.prems insertCI)
    obtain AN where AN: "AN = insert x A" 
      by simp
    have "finite A"
      by (simp add: insert.hyps(1))
    have "fset_unique A f"
      by (smt (verit, ccfv_threshold) fset_unique_def insert.prems(1) subsetD subset_insertI)
    have "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
      by (simp add: \<open>fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))\<close>)
    have "x \<notin> A"
      by (simp add: insert.hyps(2))
    have "AN = A \<union> {x}"
      using AN by auto
    have "fset_unique AN f"
      by (simp add: AN insert.prems(1))
    have "fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))"
      by (simp add: \<open>fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))\<close>)
    show ?case using fset_sum_map_transitive_union
      using \<open>fset_sum (fset_map A f) g = fset_sum A (\<lambda>x. g (f x))\<close> \<open>fset_unique A f\<close> insert.hyps(1) insert.hyps(2) insert.prems(1) by fastforce
  qed
  thus ?thesis
    by auto
qed

lemma fset_filter_preserves_finite:
  assumes "finite A"
  shows "finite (fset_filter A p)"
proof -
  from assms show ?thesis
    unfolding fset_filter_def
    by simp
qed

lemma fset_intersect_empty:
  assumes "finite A \<and> finite B"
    and "fset_intersect A B p = {}"
  shows "\<forall>a b. a \<in> A \<and> b \<in> B \<longrightarrow> p a \<noteq> p b"
  using assms(2) fset_intersect_def by fastforce

lemma fset_intersect_simplification:
  assumes "fset_map A f \<inter> fset_map B f = {}"
  shows "fset_intersect A B f = {}"
proof
  show "fset_intersect A B f \<subseteq> {}"
    unfolding fset_intersect_def
  proof
    fix x
    assume a: "x \<in> {o1 \<in> A. \<exists>o2\<in>B. f o1 = f o2}"
    show "x \<in> {}"
      by (smt (verit, del_insts) Int_iff a assms empty_iff fset_map_def mem_Collect_eq)
  qed
  show "{} \<subseteq> fset_intersect A B f"
    by simp
qed
  
end