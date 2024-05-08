theory AbstractIotaFoundryUtxoLedger
  imports Main AbstractBasicUtxoLedger HOL.Map
begin

locale foundry_output_set =
  fixes foundry_outs :: "'fo set"
    and fid :: "'fo \<Rightarrow> 'fid"
    and total_supply :: "'fo \<Rightarrow> nat"
  assumes foundries_unique: "fset_unique foundry_outs fid"
begin

end

locale native_utxo_set = 
  fixes native_utxos :: "'nuo set"
    and id :: "'nuo \<Rightarrow> 'nid"
    and tokens :: "'nuo \<Rightarrow> ('fid \<rightharpoonup> nat)"
  assumes utxos_unique: "fset_unique native_utxos id"
    and fin: "finite native_utxos"
begin
end

definition sum_nuo_tokens :: "'nuo set \<Rightarrow> ('nuo \<Rightarrow> ('fid \<rightharpoonup> nat)) \<Rightarrow> 'fid \<Rightarrow> nat" where
  "sum_nuo_tokens nuos nuo_tokens token_id =
    fset_sum nuos (\<lambda>nuo. case nuo_tokens nuo token_id of Some x \<Rightarrow> x | None \<Rightarrow> 0)"

lemma sum_token_zero:
  shows "sum_nuo_tokens {} tokens token_id = 0"
  by (simp add: fset_sum_empty sum_nuo_tokens_def)

lemma sum_nuo_tokens_insert:
  assumes "finite A" "x \<notin> A"
  shows "sum_nuo_tokens (A \<union> {x}) tokens token_id =
         sum_nuo_tokens A tokens token_id + (case tokens x token_id of Some v \<Rightarrow> v | None \<Rightarrow> 0)"
  by (metis assms(1) assms(2) fset_sum_union_one sum_nuo_tokens_def)

lemma sum_nuo_tokens_union:
  assumes "finite A" "finite B" "A \<inter> B = {}"
  shows "sum_nuo_tokens (A \<union> B) tokens token_id = 
         sum_nuo_tokens A tokens token_id + sum_nuo_tokens B tokens token_id"
  by (simp add: assms(1) assms(2) assms(3) fset_sum_union sum_nuo_tokens_def)

lemma sum_nuo_tokens_diff:
  assumes "B \<subseteq> A" "finite A" "finite B"
  shows "sum_nuo_tokens (A - B) tokens token_id = 
         sum_nuo_tokens A tokens token_id - sum_nuo_tokens B tokens token_id"
  by (simp add: assms(1) assms(2) assms(3) fset_sum_diff sum_nuo_tokens_def)

lemma sum_nuo_tokens_transitive:
  assumes "finite A" and "finite B" and "A \<inter> B = {}"
  shows "sum_nuo_tokens (A \<union> B) tokens token_id = 
         sum_nuo_tokens A tokens token_id + sum_nuo_tokens B tokens token_id"
  by (simp add: assms(1) assms(2) assms(3) fset_sum_union sum_nuo_tokens_def)

locale foundry_transaction_definitions =
  fixes inp_foundry_outs :: "'fo set"
    and out_foundry_outs :: "'fo set"
    and inp_native_outs :: "'nuo set"
    and out_native_outs :: "'nuo set"
    and fid :: "'fo \<Rightarrow> 'fid"
    and id :: "'nuo \<Rightarrow> 'nid"
    and tokens :: "'nuo \<Rightarrow> ('fid \<rightharpoonup> nat)"
    and total_supply :: "'fo \<Rightarrow> nat"
begin

definition input_tokens :: "'fid \<Rightarrow> nat" where 
  "input_tokens token_id = sum_nuo_tokens inp_native_outs tokens token_id"

definition output_tokens :: "'fid \<Rightarrow> nat"  where 
  "output_tokens token_id = sum_nuo_tokens out_native_outs tokens token_id"

definition foundry_not_present_input_output_tokens_equal where 
  "foundry_not_present_input_output_tokens_equal \<equiv> \<forall>token_id. token_id \<notin> fset_map inp_foundry_outs fid \<longrightarrow> 
    input_tokens token_id = output_tokens token_id"

definition foundry_present_total_supply_updated where
  "foundry_present_total_supply_updated \<equiv> \<forall>token_id. \<forall>fi \<in> inp_foundry_outs. fid fi = token_id \<longrightarrow> 
    (
      (\<exists>fo \<in> out_foundry_outs. fid fo = token_id \<and> total_supply fo = total_supply fi + output_tokens token_id - input_tokens token_id)
      \<or> \<not>(\<exists>fo \<in> out_foundry_outs. fid fo = token_id)
    )"

definition foundry_ids_persisted where
  "foundry_ids_persisted \<equiv> \<forall>fo. fo \<in> out_foundry_outs \<longrightarrow> (\<exists>fi \<in> inp_foundry_outs. fid fi = fid fo)"

end 

locale foundry_transaction = foundry_transaction_definitions +
  assumes inp_valid: "foundry_output_set inp_foundry_outs fid"
    and "native_utxo_set inp_native_outs id"
    and out_valid: "foundry_output_set out_foundry_outs fid"
    and "native_utxo_set out_native_outs id"
    and foundry_not_present_input_output_tokens_equal
    and "foundry_ids_persisted"
    and foundry_present_total_supply_updated
begin

lemma input_output_tokens_relationship:
  shows "\<forall>token_id. input_tokens token_id = output_tokens token_id \<or>
                    (\<exists>ifo \<in> inp_foundry_outs. fid ifo = token_id)"
  by (smt (verit, best) CollectD foundry_not_present_input_output_tokens_equal_def foundry_transaction_axioms foundry_transaction_def fset_map_def)

lemma single_input_foundry_for_output_foundry:
  assumes "fo \<in> out_foundry_outs"
  shows "\<exists>!fi \<in> inp_foundry_outs. fid fi = fid fo"  
proof-
  have "\<exists>fi \<in> inp_foundry_outs. fid fi = fid fo"
  proof (cases "input_tokens (fid fo) = output_tokens (fid fo)")
    case True
    then have "\<exists>ifo \<in> inp_foundry_outs. fid ifo = fid fo"
      using input_output_tokens_relationship foundry_ids_persisted_def assms
      using foundry_transaction_axioms foundry_transaction_def by blast
    thus ?thesis by blast
  next
    case False
    then have "\<exists>ifo \<in> inp_foundry_outs. fid ifo = fid fo"
      using foundry_present_total_supply_updated_def assms
      using input_output_tokens_relationship by blast 
    thus ?thesis by blast
  qed
  thus ?thesis
    by (metis foundry_output_set.foundries_unique fset_unique_unfold inp_valid)
qed

end

locale foundry_ledger = 
  fixes fo_ledger :: "'fo set"
    and nuo_ledger :: "'nuo set"
    and fid :: "'fo \<Rightarrow> 'fid"
    and id :: "'nuo \<Rightarrow> 'nid"
    and total_supply :: "'fo \<Rightarrow> nat"
    and tokens :: "'nuo \<Rightarrow> ('fid \<rightharpoonup> nat)"
  assumes "foundry_output_set fo_ledger fid"
      and "native_utxo_set nuo_ledger id"
      and total_supply_token_sums_consistency: "\<forall>f. f \<in> fo_ledger \<longrightarrow> total_supply f = sum_nuo_tokens nuo_ledger tokens (fid f)"
begin

end

locale foundry_transaction_in_ledger =
  foundry_transaction inp_foundry_outs out_foundry_outs inp_native_outs out_native_outs fid id tokens total_supply +
  foundry_ledger fo_ledger nuo_ledger fid id total_supply tokens
  (* Since we are joining two locales with possibly different generic types, we explicitly join them*)
  for fid :: "'fo \<Rightarrow> 'fid"
    and id :: "'nuo \<Rightarrow> 'nid"
    and total_supply :: "'fo \<Rightarrow> nat" 
    and tokens :: "'nuo \<Rightarrow> ('fid \<rightharpoonup> nat)"
    and inp_foundry_outs out_foundry_outs :: "'fo set" 
    and inp_native_outs out_native_outs :: "'nuo set"
    and fo_ledger :: "'fo set" 
    and nuo_ledger :: "'nuo set"
  +
  assumes inp_in_ledger: "inp_foundry_outs \<subseteq> fo_ledger \<and> inp_native_outs \<subseteq> nuo_ledger"
    and foundry_ids_persisted:
      "fset_intersect out_foundry_outs fo_ledger fid \<subseteq> fset_intersect inp_foundry_outs out_foundry_outs fid"
    and out_not_in_ledger: "fset_intersect out_native_outs nuo_ledger id = {}"
begin


definition apply_transaction_foundry :: "'fo set" where
  "apply_transaction_foundry = (fo_ledger - inp_foundry_outs) \<union> out_foundry_outs"

definition apply_transaction_native_tokens :: "'nuo set" where
  "apply_transaction_native_tokens = (nuo_ledger - inp_native_outs) \<union> out_native_outs"


lemma total_supply_consistent_if_foundry_not_present:
  assumes "f \<in> apply_transaction_foundry \<and> (f \<in> fo_ledger - inp_foundry_outs)"
  shows "total_supply f = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
proof-
    have "f \<in> fo_ledger \<and> f \<notin> inp_foundry_outs"
      using apply_transaction_foundry_def assms by auto
    then have "total_supply f = sum_nuo_tokens nuo_ledger tokens (fid f)"
      using total_supply_token_sums_consistency by blast
    have "finite nuo_ledger \<and> finite inp_native_outs"
      by (meson finite_subset foundry_ledger_axioms foundry_ledger_def inp_in_ledger native_utxo_set.fin)
    moreover have "sum_nuo_tokens (nuo_ledger - inp_native_outs) tokens (fid f) = sum_nuo_tokens nuo_ledger tokens (fid f) - sum_nuo_tokens inp_native_outs tokens (fid f)"
      using sum_nuo_tokens_diff inp_in_ledger
      by (metis calculation)
    moreover have "\<not>((\<exists>ifo \<in> inp_foundry_outs. fid ifo = (fid f)))"
      by (metis \<open>f \<in> fo_ledger \<and> f \<notin> inp_foundry_outs\<close> foundry_ledger_axioms foundry_ledger_def foundry_output_set.foundries_unique fset_unique_unfold inp_in_ledger subsetD)
    moreover have "sum_nuo_tokens inp_native_outs tokens (fid f) = sum_nuo_tokens out_native_outs tokens (fid f)"
      using input_output_tokens_relationship
      using calculation(3) input_tokens_def output_tokens_def by auto
    ultimately have "total_supply f = sum_nuo_tokens (nuo_ledger - inp_native_outs) tokens (fid f) + sum_nuo_tokens out_native_outs tokens (fid f)"
      by (metis Diff_disjoint Int_Diff_Un \<open>total_supply f = sum_nuo_tokens nuo_ledger tokens (fid f)\<close> add.commute finite_Diff inf.absorb_iff2 inp_in_ledger sum_nuo_tokens_transitive)
    then show ?thesis
    proof -
      have "nuo_ledger \<inter> out_native_outs = {}"
        using fset_intersect_def out_not_in_ledger by fastforce
      then have "(nuo_ledger - inp_native_outs) \<inter> out_native_outs = {}"
        by blast
      then have "sum_nuo_tokens (nuo_ledger - inp_native_outs) tokens (fid f) + sum_nuo_tokens out_native_outs tokens (fid f) =
            sum_nuo_tokens ((nuo_ledger - inp_native_outs) \<union> out_native_outs) tokens (fid f)"
        using sum_nuo_tokens_union
        by (metis \<open>finite nuo_ledger \<and> finite inp_native_outs\<close> finite_Diff foundry_transaction_axioms foundry_transaction_def native_utxo_set.fin)
      also have "... = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
        by (simp add: apply_transaction_native_tokens_def)
      finally show ?thesis
        using \<open>total_supply f = sum_nuo_tokens (nuo_ledger - inp_native_outs) tokens (fid f) + sum_nuo_tokens out_native_outs tokens (fid f)\<close> by presburger
    qed
  qed

lemma total_supply_constant_if_foundry_in_transaction:
  assumes "f \<in> apply_transaction_foundry \<and> (f \<in> out_foundry_outs)"
  shows "total_supply f = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
proof-
  have "\<exists>!fi. fi \<in> inp_foundry_outs \<and> (fid fi = fid f)"
    by (simp add: assms single_input_foundry_for_output_foundry)
  then obtain fi where fi: "fi \<in> inp_foundry_outs \<and> (fid fi = fid f)"
    by auto

  have "fi \<in> fo_ledger"
    using fi inp_in_ledger by blast

  have "total_supply fi = sum_nuo_tokens nuo_ledger tokens (fid f)"
    by (simp add: \<open>fi \<in> fo_ledger\<close> fi total_supply_token_sums_consistency)

  have "total_supply f = total_supply fi + output_tokens (fid fi) - input_tokens (fid fi)"
    by (metis assms fi foundry_output_set.foundries_unique foundry_present_total_supply_updated_def foundry_transaction_axioms foundry_transaction_def fset_unique_unfold)

  have "inp_native_outs \<subseteq> nuo_ledger"
    by (simp add: inp_in_ledger)
  have "nuo_ledger \<inter> out_native_outs = {}"
    using fset_intersect_def out_not_in_ledger by fastforce
  then have "(nuo_ledger - inp_native_outs) \<inter> out_native_outs = {}"
    by (simp add: Diff_Int_distrib2)

  have "finite inp_native_outs \<and> finite nuo_ledger \<and> finite nuo_ledger"
    by (metis finite_subset foundry_ledger_axioms foundry_ledger_def inp_in_ledger native_utxo_set.fin)


  have "sum_nuo_tokens apply_transaction_native_tokens tokens (fid f) =
      sum_nuo_tokens ((nuo_ledger - inp_native_outs) \<union> out_native_outs) tokens (fid f)"
    using apply_transaction_native_tokens_def by auto
  then have "... = sum_nuo_tokens nuo_ledger tokens (fid f)
          - sum_nuo_tokens inp_native_outs tokens (fid f)
          + sum_nuo_tokens out_native_outs tokens (fid f)"
    using sum_nuo_tokens_diff sum_nuo_tokens_transitive
    by (metis Diff_subset \<open>(nuo_ledger - inp_native_outs) \<inter> out_native_outs = {}\<close> \<open>finite inp_native_outs \<and> finite nuo_ledger \<and> finite nuo_ledger\<close> \<open>inp_native_outs \<subseteq> nuo_ledger\<close> foundry_transaction_axioms foundry_transaction_def native_utxo_set.fin rev_finite_subset)

  thus ?thesis
    by (smt (verit, ccfv_threshold) Diff_disjoint Diff_subset Nat.diff_add_assoc2 Un_Diff_cancel2 \<open>finite inp_native_outs \<and> finite nuo_ledger \<and> finite nuo_ledger\<close> \<open>inp_native_outs \<subseteq> nuo_ledger\<close> \<open>sum_nuo_tokens apply_transaction_native_tokens tokens (fid f) = sum_nuo_tokens (nuo_ledger - inp_native_outs \<union> out_native_outs) tokens (fid f)\<close> \<open>total_supply f = total_supply fi + output_tokens (fid fi) - input_tokens (fid fi)\<close> \<open>total_supply fi = sum_nuo_tokens nuo_ledger tokens (fid f)\<close> double_diff fi finite_Diff2 foundry_transaction_definitions.input_tokens_def foundry_transaction_definitions.output_tokens_def le_add2 sum_nuo_tokens_transitive sup.boundedI sup.orderE)
qed


lemma total_supply_consistency_after_transaction:
  fixes f
  assumes "f \<in> apply_transaction_foundry" 
  shows "total_supply f = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
proof-
  have "f \<in> fo_ledger - inp_foundry_outs \<or> f \<in> out_foundry_outs"
    using apply_transaction_foundry_def assms by auto
  then have "total_supply f = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
  proof (cases "f \<in> fo_ledger - inp_foundry_outs")
    case True
    show ?thesis using total_supply_consistent_if_foundry_not_present
      using True \<open>f \<in> apply_transaction_foundry\<close> by blast
  next
    case False
    show ?thesis using total_supply_constant_if_foundry_in_transaction
      using False \<open>f \<in> apply_transaction_foundry\<close> \<open>f \<in> fo_ledger - inp_foundry_outs \<or> f \<in> out_foundry_outs\<close> by blast
  qed
  thus ?thesis
    by auto
qed

print_locale foundry_ledger
lemma apply_transaction_preserves_validity:
  shows "foundry_ledger apply_transaction_foundry apply_transaction_native_tokens fid id total_supply tokens"
proof
  have "fset_unique fo_ledger fid"
    by (meson foundry_ledger_axioms foundry_ledger_def foundry_output_set.foundries_unique)
  have "fset_unique (fo_ledger - inp_foundry_outs) fid"
    by (metis (mono_tags, lifting) DiffD1 \<open>fset_unique fo_ledger fid\<close> fset_unique_def) 
  moreover have "fset_unique out_foundry_outs fid" 
    using out_valid by (simp add: foundry_output_set_def)

  have unique_union: "fset_unique ((fo_ledger - inp_foundry_outs) \<union> out_foundry_outs) fid"
  proof-
    have "fset_unique (fo_ledger - inp_foundry_outs) fid"
      by (simp add: calculation)
    have "fset_unique out_foundry_outs fid"
      using \<open>fset_unique out_foundry_outs fid\<close> by auto
    have "fset_intersect (fo_ledger - inp_foundry_outs) out_foundry_outs fid = {}"
    proof -
      have "\<And>x y. x \<in> out_foundry_outs \<Longrightarrow>  y \<in> (fo_ledger - inp_foundry_outs) \<Longrightarrow> fid x \<noteq> fid y"
      proof-
        fix x
        assume "x \<in> out_foundry_outs"

        show "\<And>y. y \<in> (fo_ledger - inp_foundry_outs) \<Longrightarrow> fid x \<noteq> fid y"
        proof-
          fix y
          assume "y \<in> fo_ledger - inp_foundry_outs"

          have "fset_intersect out_foundry_outs fo_ledger fid \<subseteq> fset_intersect inp_foundry_outs out_foundry_outs fid"
            using foundry_ids_persisted by auto
          
          have "y \<notin> inp_foundry_outs"
            using \<open>y \<in> fo_ledger - inp_foundry_outs\<close> by auto
  
          have "x \<notin> (fo_ledger - inp_foundry_outs)"
            by (smt (verit) DiffD1 DiffD2 \<open>x \<in> out_foundry_outs\<close> foundry_ids_persisted fset_intersect_def mem_Collect_eq subsetD)
  
          have "fid x \<noteq> fid y"
            by (smt (verit, del_insts) Collect_mono_iff Diff_partition Un_iff \<open>fset_unique fo_ledger fid\<close> \<open>x \<in> out_foundry_outs\<close> \<open>x \<notin> fo_ledger - inp_foundry_outs\<close> \<open>y \<in> fo_ledger - inp_foundry_outs\<close> foundry_ids_persisted fset_intersect_def fset_unique_unfold inp_in_ledger)  

          thus "fid x \<noteq> fid y"
            by simp
        qed
      qed

      thus ?thesis
        by (smt (verit, best) Collect_empty_eq fset_intersect_def)
    qed
    thus ?thesis
      by (smt (verit, del_insts) Diff_empty Diff_iff Un_iff \<open>fset_unique out_foundry_outs fid\<close> calculation fset_intersect_def fset_unique_def mem_Collect_eq)
  qed

  show "fset_unique apply_transaction_foundry fid"
    by (simp add: apply_transaction_foundry_def unique_union)

  show "finite apply_transaction_native_tokens"
    by (metis apply_transaction_native_tokens_def finite_Diff finite_Un foundry_ledger_axioms foundry_ledger_def foundry_transaction_axioms foundry_transaction_def native_utxo_set.fin)

  show "fset_unique apply_transaction_native_tokens id"
    unfolding fset_unique_def apply_transaction_native_tokens_def
  proof-
    have "\<And>o1 o2.
       o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and>
       o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2 \<Longrightarrow>
       id o1 \<noteq> id o2"
    proof-
      fix o1 o2
      assume "o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and>
       o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2"
      then have "o1 \<in> nuo_ledger \<or> o1 \<in> out_native_outs \<and> o2 \<in> nuo_ledger \<or> o2 \<in> out_native_outs"
        by blast
      (* Now we just do case by case *)
      moreover
      { assume "o1 \<in> nuo_ledger" and "o2 \<in> nuo_ledger"
        have "id o1 \<noteq> id o2"
          unfolding fset_unique_def
          by (meson \<open>o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2\<close> \<open>o1 \<in> nuo_ledger\<close> \<open>o2 \<in> nuo_ledger\<close> foundry_ledger_axioms foundry_ledger_def fset_unique_def native_utxo_set.utxos_unique)
      }
      moreover
      { assume "o1 \<in> out_native_outs" and "o2 \<in> out_native_outs"
        have "id o1 \<noteq> id o2"
          unfolding fset_unique_def
          by (meson \<open>o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2\<close> \<open>o1 \<in> out_native_outs\<close> \<open>o2 \<in> out_native_outs\<close> foundry_transaction_axioms foundry_transaction_def fset_unique_unfold native_utxo_set.utxos_unique)
      }
      moreover
      { assume "o1 \<in> nuo_ledger" and "o2 \<in> out_native_outs"
        have "id o1 \<noteq> id o2"
          by (smt (verit, best) Collect_empty_eq \<open>o1 \<in> nuo_ledger\<close> \<open>o2 \<in> out_native_outs\<close> fset_intersect_def out_not_in_ledger)
      }
      moreover
      { assume "o1 \<in> out_native_outs" and "o2 \<in> nuo_ledger"
        have "id o1 \<noteq> id o2"
          using \<open>o1 \<in> out_native_outs\<close> \<open>o2 \<in> nuo_ledger\<close> fset_intersect_def out_not_in_ledger by fastforce
      }
      ultimately show "id o1 \<noteq> id o2"
        using \<open>o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2\<close> by fastforce 

    qed
    thus "\<forall>o1 o2.
       o1 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and>
       o2 \<in> nuo_ledger - inp_native_outs \<union> out_native_outs \<and> o1 \<noteq> o2 \<longrightarrow>
       id o1 \<noteq> id o2"
      by fastforce
  qed

  show "\<forall>f. f \<in> apply_transaction_foundry \<longrightarrow> total_supply f = sum_nuo_tokens apply_transaction_native_tokens tokens (fid f)"
    using total_supply_consistency_after_transaction
    by auto

qed

end (* locale foundry_transaction_in_ledger *)

end (* theory AbstractIotaFoundryUtxoLedger *)
