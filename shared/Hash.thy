theory Hash
  imports Main
begin

text \<open>An opaque hash type.\<close>
typedecl hash

locale hashes =
  fixes H :: "hash set"
    and U :: "hash set"
assumes h_inf: "infinite H"
    and u_fin: "finite U"
begin

definition take_hash :: "hash set \<Rightarrow> hash" where
"take_hash excl \<equiv> (SOME h :: hash. h \<in> H \<and> h \<notin> U \<and> h \<notin> excl)"

lemma takes_new:
  fixes h and excl
assumes "h = take_hash excl"
    and "finite excl"
  shows "h \<notin> U \<and> h \<notin> excl"
proof -
  have h_exist: "\<exists>hh. hh \<in> H \<and> hh \<notin> U \<and> hh \<notin> excl"
    using assms h_inf
    by (metis Diff_iff finite_Diff2 rev_finite_subset subsetI u_fin)
  thus ?thesis
    by (simp add: assms(1) take_hash_def verit_sko_ex_indirect)
qed

end

end