theory AbstractIotaAliasUtxoLedger
    imports Main AbstractBasicUtxoLedger
begin 

locale alias_output_set = 
  fixes alias_outs :: "'ao set"
    and aid :: "'ao \<Rightarrow> 'id"
  assumes aliases_unique: "fset_unique alias_outs aid"
begin

end

locale alias_transaction = 
  fixes inp_alias_outs :: "'ao set"
    and out_alias_outs :: "'ao set"
    and aid :: "'ao \<Rightarrow> 'id"
  assumes inp_valid: "alias_output_set inp_alias_outs aid"
    and out_valid: "alias_output_set out_alias_outs aid"
begin

definition inp_alias_ids where
  "inp_alias_ids = fset_map inp_alias_outs aid" 

definition out_alias_ids where
  "out_alias_ids = fset_map out_alias_outs aid" 

end 

(* A transaction where a new alias ID is added is a valid transaction *)
lemma alias_creation_valid:
  assumes 
      "alias_output_set out_aliases aid" 
      and "alias_output_set inp_aliases aid"
      and "new_alias \<in> out_aliases"
      and "aid new_alias \<in> (fset_map out_aliases aid)"
      and "aid new_alias \<notin> (fset_map inp_aliases aid)" 
  shows "alias_transaction inp_aliases out_aliases aid"
  by (simp add: alias_transaction_def assms(1) assms(2))

(* Exists a valid transaction, where an Alias with a new Alias ID is created *)
lemma alias_creation_possible:
  shows 
    "\<exists>inp_aliases out_aliases aid new_alias. 
        alias_transaction inp_aliases out_aliases aid 
        \<and> new_alias \<in> out_aliases
        \<and> aid new_alias \<in> (fset_map out_aliases aid) 
        \<and> aid new_alias \<notin> (fset_map inp_aliases aid)"
proof-
  obtain inp_aliases where inp_aliases: "(inp_aliases :: nat set) = {}"
    by simp
  obtain new_alias where new_alias: "(new_alias :: nat ) = 1"
    by simp 
  obtain out_aliases where out_aliases: "out_aliases = {new_alias}"
    by simp
  obtain aid where aid: "(aid :: nat \<Rightarrow> nat) = (\<lambda>x. x)"
    by simp

  have new_alias_in_out: "new_alias \<in> out_aliases"
    by (simp add: \<open>out_aliases = {new_alias}\<close>)
  have new_alias_id_unique: "aid new_alias \<in> (fset_map out_aliases aid)"
    using fset_map_def new_alias_in_out by fastforce
  have new_alias_not_in_inp: "aid new_alias \<notin> (fset_map inp_aliases aid)"
    by (simp add: \<open>inp_aliases = {}\<close> fset_map_def)

  interpret inp: alias_output_set inp_aliases aid
    by (simp add: \<open>inp_aliases = {}\<close> alias_output_set.intro fset_unique_def)
  interpret out: alias_output_set out_aliases aid
    by (simp add: \<open>aid = (\<lambda>x. x)\<close> alias_output_set.intro fset_unique_def) 

  have valid_alias_transaction: "alias_transaction inp_aliases out_aliases aid"
    by (simp add: alias_transaction_def inp.alias_output_set_axioms out.alias_output_set_axioms)

  have exists: "alias_transaction inp_aliases out_aliases aid 
        \<and> new_alias \<in> out_aliases
        \<and> aid new_alias \<in> (fset_map out_aliases aid) 
        \<and> aid new_alias \<notin> (fset_map inp_aliases aid)"
    using new_alias_id_unique new_alias_in_out new_alias_not_in_inp valid_alias_transaction by blast

  then have "\<exists>inp_aliases out_aliases aid new_alias. alias_transaction inp_aliases out_aliases aid 
        \<and> new_alias \<in> out_aliases
        \<and> aid new_alias \<in> (fset_map out_aliases aid) 
        \<and> aid new_alias \<notin> (fset_map inp_aliases aid)"
    using exists inp_aliases out_aliases aid new_alias
    by (smt (z3) alias_output_set_def alias_transaction.intro all_not_in_conv fset_map_def fset_unique_def mem_Collect_eq singletonD)

  thus ?thesis
    using exists
    by blast
qed

locale alias_ledger = 
  fixes ledger :: "'ao set"
    and aid :: "'ao \<Rightarrow> 'id"
  assumes unique_ids: "fset_unique ledger aid"
begin

definition ledger_ids where
  "ledger_ids = fset_map ledger aid" 

end

locale alias_transaction_in_ledger = 
  alias_transaction + 
  alias_ledger +
  assumes inp_in_ledger: "inp_alias_outs \<subseteq> ledger"
    and out_ids_not_in_ledger:
      (* The alias IDs in outputs that are in the ledger are only those which are in the inputs *)
      "fset_intersect out_alias_outs ledger aid \<subseteq> fset_intersect inp_alias_outs out_alias_outs aid"
begin

definition apply_transaction where
  "apply_transaction = (ledger - inp_alias_outs) \<union> out_alias_outs"

lemma apply_transaction_preserves_validity:
  shows "alias_ledger (apply_transaction) aid"
proof -
  have "fset_unique ledger aid"
    by (simp add: unique_ids)
  have "fset_unique (ledger - inp_alias_outs) aid" 
    using inp_in_ledger unique_ids by (simp add: fset_unique_def)
  moreover have "fset_unique out_alias_outs aid" 
    using out_valid by (simp add: alias_output_set_def)
  ultimately have target_contr: "\<not> (fset_unique ((ledger - inp_alias_outs) \<union> out_alias_outs) aid) \<Longrightarrow> False"
  proof-
    assume "\<not> (fset_unique ((ledger - inp_alias_outs) \<union> out_alias_outs) aid)"
    then obtain x y where xy_def: "x \<in> (ledger - inp_alias_outs) \<union> out_alias_outs"
                                    "y \<in> (ledger - inp_alias_outs) \<union> out_alias_outs"
                                    "x \<noteq> y" 
                                    "aid x = aid y"
      by (auto simp add: fset_unique_def)
    then consider (case1) "x \<in> ledger - inp_alias_outs" "y \<in> ledger - inp_alias_outs"
                | (case2) "x \<in> out_alias_outs" "y \<in> out_alias_outs"
                | (case3) "x \<in> ledger - inp_alias_outs" "y \<in> out_alias_outs"
                | (case4) "x \<in> out_alias_outs" "y \<in> ledger - inp_alias_outs"
      by blast
    then show False
    proof cases
      case case1
      then show ?thesis using \<open>fset_unique (ledger - inp_alias_outs) aid\<close> xy_def(3,4)
        by (simp add: fset_unique_def)
    next
      case case2
      then show ?thesis using \<open>fset_unique out_alias_outs aid\<close> xy_def(3,4)
        by (simp add: fset_unique_def)
    next
      case case3
      then have "y \<in> fset_intersect out_alias_outs ledger aid"
        using xy_def(4)
        by (metis (mono_tags, lifting) DiffD1 fset_intersect_def mem_Collect_eq)
      then have "y \<in> fset_intersect inp_alias_outs out_alias_outs aid"
        using out_ids_not_in_ledger by blast
      then have "y \<in> inp_alias_outs \<and> y \<in> out_alias_outs"
        by (simp add: case3(2) fset_intersect_def)
      moreover have "x \<notin> inp_alias_outs"
        using case3(1) by blast
      ultimately show ?thesis using xy_def(4)
        by (metis DiffD1 case3(1) fset_unique_unfold inp_in_ledger subsetD unique_ids)
    next
      (* Symmetrical to case3 *)
      case case4
      then have "x \<in> fset_intersect out_alias_outs ledger aid"
        using xy_def(4)
        by (metis (mono_tags, lifting) DiffD1 fset_intersect_def mem_Collect_eq)
      then have "x \<in> fset_intersect inp_alias_outs out_alias_outs aid"
        using out_ids_not_in_ledger by blast
      then have "x \<in> inp_alias_outs \<and> x \<in> out_alias_outs"
        by (simp add: case4(1) fset_intersect_def)
      moreover have "y \<notin> inp_alias_outs"
        using case4(2) by blast
      ultimately show ?thesis using xy_def(4)
        by (metis DiffD1 case4(2) fset_unique_unfold inp_in_ledger subsetD unique_ids)
    qed
  qed
  thus ?thesis
    using alias_ledger_def apply_transaction_def by auto
qed

end (* locale alias_transaction_in_ledger *)

end (* theory AbstractIotaUtxoLedger *)