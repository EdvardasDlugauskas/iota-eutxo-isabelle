theory IotaUtxoLedgerFoundry
  imports IotaUtxoLedger
begin

context iota_utxo_ledger_implementation
begin

section "FoundryDB is a foundry_ledger"

lemma sum_maps: "sum_nuo_tokens (take_basics DB)
          native_tokens (foundry_id f) = 
        sum_nuo_tokens DB
          utxo_to_native_tokens (foundry_id f)"
proof -
  have "sum_nuo_tokens (take_basics DB) native_tokens (foundry_id f) =
        fset_sum (take_basics DB) (\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
    by (simp add: sum_nuo_tokens_def)
  also have "... = fset_sum DB (\<lambda>u. case utxo_to_native_tokens u (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
  proof -
    have "fset_sum (take_basics DB) (\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0) =
          fset_sum (fset_map DB take_single_basic) (\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
      by (simp add: take_basics_def)
    also have "... = fset_sum DB (\<lambda>u. case native_tokens (take_single_basic u) (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
    proof-
      have "fset_unique DB take_single_basic"
        by (metis DB_valid_def UTXO_set_valid_def db_valid fset_unique_def utxo_to_id_def)
      have "\<forall>u \<in> DB. \<exists>!ub. ub \<in> (fset_map DB take_single_basic) \<and> ub = take_single_basic u"
        using fset_map_def by fastforce
      have "\<forall>ub \<in> (fset_map DB take_single_basic). \<exists>u \<in> DB. ub = take_single_basic u"
        by (smt (verit, ccfv_threshold) fset_map_def mem_Collect_eq)
      have "\<forall>ub \<in> (fset_map DB take_single_basic). \<exists>!u \<in> DB. ub = take_single_basic u"
        by (metis \<open>\<forall>ub\<in>fset_map DB take_single_basic. \<exists>u\<in>DB. ub = take_single_basic u\<close> \<open>fset_unique DB take_single_basic\<close> fset_unique_def)

      have "finite DB"
        using DB_valid_def UTXO_set_valid_def db_valid by blast
      have "fset_unique DB take_single_basic"
        by (simp add: \<open>fset_unique DB take_single_basic\<close>)
      obtain my_f where my_f: "my_f \<equiv>(\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
        by simp
      then have "fset_sum (fset_map DB take_single_basic) my_f
          = fset_sum DB (\<lambda>x. my_f (take_single_basic x))"
        using fset_sum_map_transitive
        using \<open>finite DB\<close> \<open>fset_unique DB take_single_basic\<close> by blast
      thus ?thesis
        using my_f by blast
    qed
    also have "... = fset_sum DB (\<lambda>u. case utxo_to_native_tokens u (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
    proof -
      have "\<forall>u \<in> DB. native_tokens (take_single_basic u) (foundry_id f) = utxo_to_native_tokens u (foundry_id f)"
      proof
        fix u assume "u \<in> DB"
        then show "native_tokens (take_single_basic u) (foundry_id f) = utxo_to_native_tokens u (foundry_id f)"
          by (cases u) (auto simp add: take_single_basic_def utxo_to_native_tokens_def)
      qed
      then show ?thesis
        using utxo_to_native_tokens_def by presburger
    qed
    finally show ?thesis .
  qed
  also have "... = sum_nuo_tokens DB utxo_to_native_tokens (foundry_id f)"
    by (simp add: sum_nuo_tokens_def)
  finally show ?thesis .
qed

print_locale foundry_ledger
interpretation concrete_iota_foundry_ledger: foundry_ledger FoundryDB "(take_basics DB)" foundry_id basic_id total_supply native_tokens
proof
  have "foundry_ids_unique DB"
    using DB_valid_def FoundryDB_valid_def db_valid by auto
  then have "\<forall>f1 \<in> FoundryDB. \<forall> f2 \<in> FoundryDB. f1 \<noteq> f2 \<longrightarrow> foundry_id f1 \<noteq> foundry_id f2"
  proof-
    have "take_foundry DB = FoundryDB"
      using iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def by blast
    then have "\<forall>u1 b1 f1. u1 \<in> DB \<and> u1 = FoundryU b1 f1 \<longrightarrow> f1 \<in> FoundryDB"
      using take_foundry_def by force
    thus ?thesis
      using \<open>foundry_ids_unique DB\<close> \<open>take_foundry DB = FoundryDB\<close> foundry_ids_unique_def take_foundry_def by force
  qed
  thus "fset_unique FoundryDB foundry_id"
    by (simp add: fset_unique_def)

  show "fset_unique (take_basics DB) basic_id"
    using DB_valid_def UTXO_set_valid_def db_valid
    by (smt (verit, ccfv_SIG) fset_map_def fset_unique_def mem_Collect_eq take_basics_def utxo_to_id_def) 
  show "finite (take_basics DB)"
    by (metis DB_valid_def UTXO_set_valid_def db_valid fset_map_preserves_finite take_basics_def)
  show "\<forall>f. f \<in> FoundryDB \<longrightarrow> total_supply f = sum_nuo_tokens (take_basics DB) native_tokens (foundry_id f)"
  proof-
    have "\<And>f. f \<in> FoundryDB \<Longrightarrow>
         total_supply f =
         sum_nuo_tokens (take_basics DB)
          native_tokens (foundry_id f)"
    proof-
      fix f
      assume "f \<in> FoundryDB"
      have "FoundryDB = take_foundry DB"
        using iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def by blast
      have "total_supply f = fset_sum DB (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)"
        using db_valid
        unfolding DB_valid_def FoundryDB_valid_def native_token_totals_valid_def
        using \<open>FoundryDB = take_foundry DB\<close> \<open>f \<in> FoundryDB\<close> by blast
      thus "total_supply f =
         sum_nuo_tokens (take_basics DB)
          native_tokens (foundry_id f)"
        by (metis sum_maps sum_nuo_tokens_def)
    qed
    thus ?thesis by auto
  qed
qed

section "Valid Transaction is a valid foundry_transaction"

print_locale foundry_output_set
theorem concrete_inputs_foundry_output_set:
  "foundry_output_set (take_foundry (tx_inp ValidTransaction)) foundry_id"
proof
  have "foundry_ids_unique (tx_inp ValidTransaction)"
    using transaction_unique_foundry_inputs_def transaction_valid_def tx_valid by blast
  show "fset_unique (take_foundry (tx_inp ValidTransaction)) foundry_id"
    by (smt (verit, ccfv_threshold) UTXO.inject(3) \<open>foundry_ids_unique (tx_inp ValidTransaction)\<close> foundry_ids_unique_def fset_unique_def mem_Collect_eq take_foundry_def)
qed

theorem concrete_outputs_foundry_output_set:
  "foundry_output_set (take_foundry (tx_out ValidTransaction)) foundry_id"
  by (smt (verit, ccfv_SIG) UTXO.inject(3) foundry_ids_unique_def foundry_output_set.intro fset_unique_def mem_Collect_eq take_foundry_def transaction_unique_foundry_outputs_def transaction_valid_def tx_valid)

print_locale foundry_transaction
interpretation concrete_foundry_transaction: 
  foundry_transaction 
    "(take_foundry (tx_inp ValidTransaction))" 
    "(take_foundry (tx_out ValidTransaction))" 
    "(take_basics (tx_inp ValidTransaction))" 
    "(take_basics (tx_out ValidTransaction))" 
    foundry_id
    basic_id
    native_tokens
    total_supply
proof
  show "fset_unique (take_foundry (tx_inp ValidTransaction)) foundry_id"
    by (simp add: concrete_inputs_foundry_output_set foundry_output_set.foundries_unique)
  show "fset_unique (take_foundry (tx_out ValidTransaction)) foundry_id"
    by (simp add: concrete_outputs_foundry_output_set foundry_output_set.foundries_unique)
  show "fset_unique (take_basics (tx_inp ValidTransaction)) basic_id" 
    using tx_valid transaction_valid_def UTXO_set_valid_def basic_output_set.outs_unique fset_map_def fset_unique_def mem_Collect_eq take_basics_def utxo_to_id_def
    by (smt (verit, best) basic_output_set.outs_unique is_concrete_basic_transaction fset_map_def fset_unique_def mem_Collect_eq take_basics_def utxo_to_id_def)
  show "finite (take_basics (tx_inp ValidTransaction))"
    using is_concrete_basic_transaction basic_output_set.fin fset_map_preserves_finite take_basics_def
    by (metis basic_transaction.input_basic_output_set)
  show "fset_unique (take_basics (tx_out ValidTransaction)) basic_id" 
    using tx_valid transaction_valid_def UTXO_set_valid_def
    by (smt (verit, best) basic_output_set.outs_unique is_concrete_basic_transaction fset_map_def fset_unique_def mem_Collect_eq take_basics_def utxo_to_id_def) 
  show "finite (take_basics (tx_out ValidTransaction))"
    using basic_output_set.fin is_concrete_basic_transaction fset_map_preserves_finite take_basics_def
    by (metis basic_transaction.output_basic_output_set)
  show "foundry_transaction_definitions.foundry_not_present_input_output_tokens_equal (take_foundry (tx_inp ValidTransaction)) (take_basics (tx_inp ValidTransaction))      
    (take_basics (tx_out ValidTransaction)) foundry_id native_tokens"
    using tx_valid transaction_valid_def native_tokens_transaction_valid_def foundry_not_present_input_output_tokens_equal_def foundry_not_present_input_output_tokens_equal_def
  proof-
    have "transaction_valid DB ValidTransaction"
      by (simp add: tx_valid)
    then have "native_tokens_transaction_valid ValidTransaction"
      unfolding transaction_valid_def
      by blast
    have "\<forall>token_id. token_id \<notin> fset_map (take_foundry (tx_inp ValidTransaction)) foundry_id \<longrightarrow>
      input_tokens ValidTransaction token_id = output_tokens ValidTransaction token_id"
      unfolding native_tokens_transaction_valid_def
      using \<open>native_tokens_transaction_valid ValidTransaction\<close> foundry_not_present_input_output_tokens_equal_def native_tokens_transaction_valid_def by blast
    then have "\<forall>token_id.
       token_id
       \<notin> fset_map (take_foundry (tx_inp ValidTransaction)) foundry_id \<longrightarrow>
       foundry_transaction_definitions.input_tokens
        (take_basics (tx_inp ValidTransaction)) native_tokens token_id =
       foundry_transaction_definitions.output_tokens
        (take_basics (tx_out ValidTransaction)) native_tokens token_id"
      unfolding input_tokens_def output_tokens_def foundry_transaction_definitions.input_tokens_def foundry_transaction_definitions.output_tokens_def
      by (simp add: sum_nuo_tokens_def sum_tokens_def)
    thus ?thesis
      using foundry_transaction_definitions.foundry_not_present_input_output_tokens_equal_def by blast
  qed
  show "foundry_transaction_definitions.foundry_ids_persisted (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id"
  proof-
    have "transaction_valid DB ValidTransaction"
      by (simp add: tx_valid)
    then have "native_tokens_transaction_valid ValidTransaction"
      unfolding transaction_valid_def
      by blast
    then have "\<forall>fo. fo \<in> take_foundry (tx_out ValidTransaction) \<longrightarrow>
         (\<exists>fi\<in>take_foundry (tx_inp ValidTransaction).
             foundry_id fi = foundry_id fo)"
      unfolding transaction_valid_def foundry_ids_persisted_def
      using foundry_ids_persisted_def native_tokens_transaction_valid_def 
      by blast
    thus ?thesis
      using foundry_transaction_definitions.foundry_ids_persisted_def by blast
  qed
  show "foundry_transaction_definitions.foundry_present_total_supply_updated (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction))      (take_basics (tx_inp ValidTransaction)) (take_basics (tx_out ValidTransaction)) foundry_id native_tokens total_supply"
  proof-
    have "transaction_valid DB ValidTransaction"
      by (simp add: tx_valid)
    then have "native_tokens_transaction_valid ValidTransaction"
      unfolding transaction_valid_def
      by blast
    then have "\<forall>token_id.
       \<forall>fi\<in>take_foundry (tx_inp ValidTransaction).
          foundry_id fi = token_id \<longrightarrow>
          (\<exists>fo\<in>take_foundry (tx_out ValidTransaction).
              foundry_id fo = token_id \<and>
              total_supply fo =
              total_supply fi + foundry_transaction_definitions.output_tokens (take_basics (tx_out ValidTransaction)) native_tokens token_id -
              foundry_transaction_definitions.input_tokens (take_basics (tx_inp ValidTransaction)) native_tokens token_id) \<or>
          \<not> (\<exists>fo\<in>take_foundry (tx_out ValidTransaction). foundry_id fo = token_id)"
      unfolding transaction_valid_def native_tokens_transaction_valid_def
      using foundry_present_total_supply_updated_def
      by (simp add: foundry_transaction_definitions.input_tokens_def foundry_transaction_definitions.output_tokens_def input_tokens_def output_tokens_def sum_nuo_tokens_def sum_tokens_def)
    thus ?thesis
      by (simp add: foundry_transaction_definitions.foundry_present_total_supply_updated_def)
  qed
qed

section "Valid Transaction and FoundryDB is foundry_transaction_in_ledger"

lemma foundry_backwards:
  assumes "DB_valid A" and "DB_valid B"
    and "u = FoundryU b f"
    and "u \<in> A" and "u \<in> B"
    and "newA = A - B"
  shows "f \<notin> take_foundry newA"
  by (smt (verit, ccfv_SIG) CollectD DB_valid_def DiffD1 DiffD2 FoundryDB_valid_def assms(1) assms(3) assms(4) assms(5) assms(6) foundry_ids_unique_def take_foundry_def)

lemma take_foundry_diff:
  assumes "B \<subseteq> A"
    and "DB_valid A" and "DB_valid B"
  shows "take_foundry (A - B) = take_foundry A - take_foundry B"
proof
  have "\<forall>x f. FoundryU f x \<in> B \<longrightarrow> FoundryU f x \<in> A"
    using assms by blast
  then have "\<forall>x. x \<in> take_foundry B \<longrightarrow> x \<in> take_foundry A"
    using take_foundry_def by auto
  then have "take_foundry B \<inter> take_foundry A = take_foundry B"
    by blast

  show "take_foundry (A - B) \<subseteq> take_foundry A - take_foundry B"
  proof
    fix x
    assume "x \<in> take_foundry (A - B)"
    show "x \<in> take_foundry A - take_foundry B"
    proof
      show "x \<in> take_foundry A"
        using \<open>x \<in> take_foundry (A - B)\<close> take_foundry_def by auto
      show "x \<notin> take_foundry B"
      proof
        assume "x \<in> take_foundry B"
        have "\<forall>uf ub. FoundryU ub uf \<in> B \<longrightarrow> FoundryU ub uf \<in> A"
          using \<open>\<forall>x f. FoundryU f x \<in> B \<longrightarrow> FoundryU f x \<in> A\<close> by blast
        have "take_foundry A \<inter> take_foundry B = take_foundry B"
          using \<open>take_foundry B \<inter> take_foundry A = take_foundry B\<close> by blast

        obtain u where u: "\<exists>b. u = FoundryU b x" and "u \<in> B"
          using \<open>x \<in> take_foundry B\<close> take_foundry_def by moura
        have "u \<in> A"
          using \<open>u \<in> B\<close> assms(1) by auto
        have "u \<notin> (A - B)"
          using \<open>u \<in> B\<close> by auto

        then have "\<exists>buniq. FoundryU buniq x \<in> (A - B) = False"
          using u by blast
        then have "\<forall>b f. FoundryU b f \<in> (A - B) \<longrightarrow> f \<in> take_foundry (A - B)"
          using take_foundry_def by auto
        then have "\<forall>b. FoundryU b x \<in> (A - B) \<longrightarrow> x \<in> take_foundry (A - B) "
          by blast 

        then have "\<exists>b. (let un = FoundryU b x in un \<in> (A - B))"
        proof -
          obtain bb :: "UTXO set \<Rightarrow> FoundryT \<Rightarrow> bool" where
            f1: "\<forall>X0 X1. bb X0 X1 = (\<exists>Y0. FoundryU Y0 X1 \<in> X0)"
            by moura
          then have "bb (A - B) x"
            using \<open>x \<in> take_foundry (A - B)\<close> take_foundry_def by auto
          then show ?thesis
            using f1 by meson
        qed

        then obtain u2 where u2: "\<exists>b. u2 = FoundryU b x" and "u2 \<in> (A - B)"
          by metis

        thus False
          using \<open>u \<in> A\<close> \<open>u \<in> B\<close> \<open>x \<in> take_foundry (A - B)\<close> assms(2) assms(3) foundry_backwards iota_utxo_ledger_implementation_axioms u by blast
      qed
    qed
  qed
  show "take_foundry A - take_foundry B \<subseteq> take_foundry (A - B)"
    using take_foundry_def by force
qed

lemma take_foundry_union:
  shows "take_foundry (A \<union> B) = take_foundry A \<union> take_foundry B"
  using take_foundry_def by auto 

lemma take_foundry_disjoint_transitive:
  shows "take_foundry (DB - (tx_inp ValidTransaction)) = take_foundry DB - take_foundry (tx_inp ValidTransaction)"
  by (meson subsetI take_foundry_diff transaction_inputs_exist_in_ledger_def transaction_valid_def tx_valid db_valid)

lemma take_foundry_union_transitive:
  shows "take_foundry (DB \<union> (tx_out ValidTransaction)) = take_foundry DB \<union> take_foundry (tx_out ValidTransaction)"
  using take_foundry_union transaction_valid_def tx_valid by presburger
                  
lemma apply_tx_transitive_foundry_unfolded:
  assumes "newDB = apply_valid_transaction"
    and "foundry_inputs = (take_foundry (tx_inp ValidTransaction))"
    and "foundry_outputs = (take_foundry (tx_out ValidTransaction))"
  shows "take_foundry newDB = 
        take_foundry DB - take_foundry (tx_inp ValidTransaction) \<union> take_foundry (tx_out ValidTransaction)"
  using apply_valid_transaction_def
  by (simp add: apply_tx_def assms(1) take_foundry_disjoint_transitive take_foundry_union)

lemma apply_tx_transitive_foundry:
  assumes "newDB = apply_valid_transaction"
    and "foundry_inputs = (take_foundry (tx_inp ValidTransaction))"
    and "foundry_outputs = (take_foundry (tx_out ValidTransaction))"
  shows "take_foundry newDB = (FoundryDB - foundry_inputs) \<union> foundry_outputs"
proof -
  have "iota_utxo_ledger_implementation_axioms DB AliasDB FoundryDB ValidTransaction"
    using iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms by force
  then show ?thesis
    by (simp add: apply_tx_transitive_foundry_unfolded assms(1) assms(2) assms(3) iota_utxo_ledger_implementation_axioms_def)
qed


print_locale foundry_transaction_in_ledger
interpretation concrete_foundry_transaction_in_ledger: 
  foundry_transaction_in_ledger
    foundry_id
    basic_id
    total_supply
    native_tokens
    "(take_foundry (tx_inp ValidTransaction))" 
    "(take_foundry (tx_out ValidTransaction))" 
    "(take_basics (tx_inp ValidTransaction))" 
    "(take_basics (tx_out ValidTransaction))" 
    FoundryDB
    "take_basics DB"
proof
  have is_ledger: "foundry_ledger FoundryDB (take_basics DB)
     foundry_id basic_id total_supply
     native_tokens"
    by (simp add: concrete_iota_foundry_ledger.foundry_ledger_axioms)
  show "fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id
    \<subseteq> fset_intersect (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id"
  proof-
    have "\<And>x. x \<in> fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id \<Longrightarrow>
         x \<in> fset_intersect (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id"
    proof-
      fix x
      assume "x \<in> fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id"
      have "x \<in> (take_foundry (tx_inp ValidTransaction)) \<or>
            x \<in> (take_foundry (tx_out ValidTransaction))"
        using \<open>x \<in> fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id\<close> fset_intersect_def by fastforce
      have "x \<in> (take_foundry (tx_inp ValidTransaction))"
        by (smt (verit) CollectD Un_upper2 \<open>x \<in> fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id\<close> disjoint_iff_not_equal foundry_ids_unique_def fset_intersect_def iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def subset_eq sup_commute take_foundry_def transaction_valid_def utxo_sets_independent_def)
      have "x \<in> (take_foundry (tx_out ValidTransaction))"
        using \<open>x \<in> fset_intersect (take_foundry (tx_out ValidTransaction)) FoundryDB foundry_id\<close> fset_intersect_def by fastforce
      have "x \<in> fset_intersect (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id"
        using \<open>x \<in> take_foundry (tx_inp ValidTransaction)\<close> \<open>x \<in> take_foundry (tx_out ValidTransaction)\<close> fset_intersect_def by fastforce
      show "x \<in> fset_intersect (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id"
        by (simp add: \<open>x \<in> fset_intersect (take_foundry (tx_inp ValidTransaction)) (take_foundry (tx_out ValidTransaction)) foundry_id\<close>)
    qed
    thus ?thesis
      by blast
  qed

  show "take_foundry (tx_inp ValidTransaction) \<subseteq> FoundryDB \<and> take_basics (tx_inp ValidTransaction) \<subseteq> take_basics DB"
  proof
    show "take_foundry (tx_inp ValidTransaction) \<subseteq> FoundryDB"
      using tx_valid
      unfolding transaction_valid_def
      by (metis iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def subsetI sup.absorb_iff2 take_foundry_union transaction_inputs_exist_in_ledger_def)
    show "take_basics (tx_inp ValidTransaction) \<subseteq> take_basics DB"
      using tx_valid
      unfolding transaction_valid_def
      by (metis subset_iff sup.order_iff take_basics_union transaction_inputs_exist_in_ledger_def)
  qed
  show "fset_intersect (take_basics (tx_out ValidTransaction)) (take_basics DB) basic_id = {}" 
  proof-
    have "fset_intersect (tx_out ValidTransaction) DB utxo_to_id = {}"
      using tx_valid
      unfolding transaction_valid_def
      by (simp add: Int_commute sup.commute utxo_sets_independent_def utxo_sets_inp_out_no_intersect)
    have "fset_map DB utxo_to_id = fset_map (take_basics DB) basic_id"
      by (smt (verit, ccfv_threshold) fset_map_def fset_map_def fset_map_def mem_Collect_eq mem_Collect_eq subsetI subset_antisym take_basics_def utxo_to_id_def)

    then have "fset_map (tx_out ValidTransaction) utxo_to_id = fset_map (take_basics (tx_out ValidTransaction)) basic_id"
      unfolding fset_map_def fset_map_def fset_map_def mem_Collect_eq mem_Collect_eq subsetI subset_antisym take_basics_def utxo_to_id_def
      by blast

    then have "fset_intersect (tx_out ValidTransaction) DB utxo_to_id = {} \<longrightarrow>
      fset_intersect (take_basics (tx_out ValidTransaction)) (take_basics DB) basic_id = {}"
      using fset_intersect_def fset_map_def inj_on_def
      unfolding take_basics_def utxo_to_id_def basic_id_def
      by (smt (verit) Collect_empty_eq mem_Collect_eq)

    thus ?thesis
      by (simp add: \<open>fset_intersect (tx_out ValidTransaction) DB utxo_to_id = {}\<close>)
  qed
qed

section "Apply produces valid implementation DB"

lemma apply_produces_valid_abstract_foundrydb:
  assumes "newDB = apply_valid_transaction"
  shows "foundry_ledger (take_foundry newDB) (take_basics newDB) foundry_id basic_id total_supply native_tokens"
proof
  have "newDB = apply_tx DB ValidTransaction tx_inp tx_out"
    by (simp add: apply_valid_transaction_def assms)
  have "foundry_transaction_in_ledger
    foundry_id
    basic_id
    total_supply
    native_tokens
    (take_foundry (tx_inp ValidTransaction)) 
    (take_foundry (tx_out ValidTransaction)) 
    (take_basics (tx_inp ValidTransaction)) 
    (take_basics (tx_out ValidTransaction))
    FoundryDB
    (take_basics DB)"
    by (simp add: concrete_foundry_transaction_in_ledger.foundry_transaction_in_ledger_axioms) 

 show "fset_unique (take_foundry newDB) foundry_id"
   using apply_tx_transitive_foundry assms concrete_foundry_transaction_in_ledger.apply_transaction_foundry_def concrete_foundry_transaction_in_ledger.apply_transaction_preserves_validity foundry_ledger_def foundry_output_set.foundries_unique by fastforce

  show "fset_unique (take_basics newDB) basic_id"
    by (smt (verit, ccfv_threshold) Int_Diff_Un Un_iff apply_tx_def apply_valid_transaction_def assms concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.apply_transaction_preserves_validity concrete_foundry_transaction_in_ledger.out_not_in_ledger concrete_iota_foundry_ledger.foundry_ledger_axioms finite_Un foundry_ledger_def fset_intersect_empty fset_map_linear fset_unique_def native_utxo_set_def take_basics_def) 
 show "finite (take_basics newDB)"
   by (metis Un_Diff_Int apply_tx_def apply_valid_transaction_def assms concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.apply_transaction_preserves_validity concrete_iota_foundry_ledger.foundry_ledger_axioms finite_Un foundry_ledger_def fset_map_linear native_utxo_set_def take_basics_def)
  show "\<forall>f. f \<in> take_foundry newDB \<longrightarrow>
        total_supply f = sum_nuo_tokens (take_basics newDB) native_tokens (foundry_id f)"
    using concrete_iota_foundry_ledger.foundry_ledger_axioms concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.apply_transaction_preserves_validity
    using apply_tx_transitive_foundry assms concrete_foundry_transaction_in_ledger.apply_transaction_foundry_def concrete_foundry_transaction_in_ledger.total_supply_consistency_after_transaction db_basics_apply_transaction by presburger
qed

theorem apply_produces_valid_foundrydb:
  assumes "newDB = apply_valid_transaction"
  shows "FoundryDB_valid newDB"
proof-
  have valid_initial: "FoundryDB_valid DB"
    using db_valid DB_valid_def by auto
  then have "foundry_ids_unique (DB - tx_inp ValidTransaction)"
    using FoundryDB_valid_def foundry_ids_unique_def
    by (meson DiffD1)
  then have "foundry_ids_unique (tx_out ValidTransaction)"
    using transaction_unique_foundry_outputs_def transaction_valid_def tx_valid by blast
  then have "foundry_ids_unique ((DB - tx_inp ValidTransaction) \<union> (tx_out ValidTransaction))"
    by (smt (verit, ccfv_threshold) DiffD1 Un_iff foundry_ids_unique_def transaction_valid_def tx_valid)
  thus ?thesis
  proof-
    have "foundry_ids_unique newDB"
      by (simp add: \<open>foundry_ids_unique (DB - tx_inp ValidTransaction \<union> tx_out ValidTransaction)\<close> apply_tx_def apply_valid_transaction_def assms)
    have "native_token_totals_valid newDB"
    proof-
      have "(\<forall>f. f \<in> take_foundry newDB \<longrightarrow> total_supply f = fset_sum (fset_map newDB take_single_basic) 
        (\<lambda>b. case native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"
        by (metis apply_tx_transitive_foundry assms concrete_foundry_transaction_in_ledger.apply_transaction_foundry_def concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.total_supply_consistency_after_transaction db_basics_apply_transaction sum_nuo_tokens_def take_basics_def)
      then have "(\<And>f. f \<in> take_foundry newDB \<Longrightarrow> (total_supply f = fset_sum newDB 
        (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)))"
      proof
        fix f
        assume "f \<in> take_foundry newDB"
        obtain my_f where my_f: "my_f \<equiv>(\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
          by simp
        have "fset_unique newDB take_single_basic"
          using apply_tx_ids_unique
          by (simp add: assms)
        have "finite newDB"
          by (metis DB_valid_def UTXO_set_valid_def apply_tx_def apply_valid_transaction_def assms basic_output_set_def basic_transaction.output_basic_output_set db_valid finite_Diff finite_Un is_concrete_basic_transaction)
        have "total_supply f = fset_sum (fset_map newDB take_single_basic) my_f"
          by (simp add: \<open>\<forall>f. f \<in> take_foundry newDB \<longrightarrow> total_supply f = fset_sum (fset_map newDB take_single_basic) (\<lambda>b. case native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)\<close> \<open>f \<in> take_foundry newDB\<close> my_f)
        then have "fset_sum (fset_map newDB take_single_basic) my_f
          = fset_sum newDB (\<lambda>x. my_f (take_single_basic x))"
        using fset_sum_map_transitive
        using \<open>finite newDB\<close> \<open>fset_unique newDB take_single_basic\<close> by blast

      thus "(total_supply f = fset_sum newDB (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"
        by (simp add: \<open>total_supply f = fset_sum (fset_map newDB take_single_basic) my_f\<close> my_f utxo_to_native_tokens_def)
      qed
      thus ?thesis
        using native_token_totals_valid_def by blast
      qed
      thus ?thesis
        by (simp add: FoundryDB_valid_def \<open>foundry_ids_unique newDB\<close>)
    qed
qed
  
section "Thus, applying Valid Transaction results in a valid Abstract Foundry Ledger"

print_locale foundry_ledger
theorem apply_produces_valid_foundry_ledger:
  assumes newDB: "newDB = apply_valid_transaction"
      and newFoundryDB: "newFoundryDB = take_foundry newDB"
    shows "foundry_ledger newFoundryDB (take_basics newDB) foundry_id basic_id total_supply native_tokens"
proof
  have refines: "foundry_transaction_in_ledger
    foundry_id
    basic_id
    total_supply
    native_tokens
    (take_foundry (tx_inp ValidTransaction))
    (take_foundry (tx_out ValidTransaction))
    (take_basics (tx_inp ValidTransaction))
    (take_basics (tx_out ValidTransaction))
    FoundryDB
    (take_basics DB)"
    using concrete_foundry_transaction_in_ledger.foundry_transaction_in_ledger_axioms
    by simp

  show "fset_unique newFoundryDB foundry_id"
    by (smt (verit, best) CollectD FoundryDB_valid_def UTXO.inject(3) apply_produces_valid_foundrydb foundry_ids_unique_def fset_unique_def newDB newFoundryDB take_foundry_def)
  show "fset_unique (take_basics newDB) basic_id"
    using apply_produces_valid_abstract_foundrydb foundry_ledger_def native_utxo_set.utxos_unique newDB by fastforce
  show "finite (take_basics newDB)"
    using apply_produces_valid_abstract_foundrydb foundry_ledger_def native_utxo_set_def newDB by fastforce


  have token_totals: "native_token_totals_valid newDB"
  proof-
    have "(\<forall>f. f \<in> take_foundry newDB \<longrightarrow> total_supply f = fset_sum (fset_map newDB take_single_basic) 
      (\<lambda>b. case native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"
      by (metis apply_tx_transitive_foundry assms concrete_foundry_transaction_in_ledger.apply_transaction_foundry_def concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.total_supply_consistency_after_transaction db_basics_apply_transaction sum_nuo_tokens_def take_basics_def)
    then have "(\<And>f. f \<in> take_foundry newDB \<Longrightarrow> (total_supply f = fset_sum newDB 
      (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)))"
    proof
      fix f
      assume "f \<in> take_foundry newDB"
      obtain my_f where my_f: "my_f \<equiv>(\<lambda>utxo. case native_tokens utxo (foundry_id f) of Some x \<Rightarrow> x | None \<Rightarrow> 0)"
        by simp
      have "fset_unique newDB take_single_basic"
        using apply_tx_ids_unique
        by (simp add: assms)
      have "finite newDB"
        by (metis DB_valid_def UTXO_set_valid_def apply_tx_def apply_valid_transaction_def basic_output_set_def basic_transaction.output_basic_output_set db_valid finite_Diff finite_Un is_concrete_basic_transaction newDB)
      have "total_supply f = fset_sum (fset_map newDB take_single_basic) my_f"
        by (simp add: \<open>\<forall>f. f \<in> take_foundry newDB \<longrightarrow> total_supply f = fset_sum (fset_map newDB take_single_basic) (\<lambda>b. case native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x)\<close> \<open>f \<in> take_foundry newDB\<close> my_f)
      then have "fset_sum (fset_map newDB take_single_basic) my_f
        = fset_sum newDB (\<lambda>x. my_f (take_single_basic x))"
      using fset_sum_map_transitive
      using \<open>finite newDB\<close> \<open>fset_unique newDB take_single_basic\<close> by blast

    thus "(total_supply f = fset_sum newDB (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"
      by (simp add: \<open>total_supply f = fset_sum (fset_map newDB take_single_basic) my_f\<close> my_f utxo_to_native_tokens_def)
    qed
    thus ?thesis
      using native_token_totals_valid_def by blast
  qed


  show "\<forall>f. f \<in> newFoundryDB \<longrightarrow> total_supply f = sum_nuo_tokens (take_basics newDB) native_tokens (foundry_id f)"
  proof-
    have "newFoundryDB = (FoundryDB - (take_foundry (tx_inp ValidTransaction))) \<union> (take_foundry (tx_out ValidTransaction))"
      using apply_tx_transitive_foundry
      by (simp add: newDB newFoundryDB)
    have "(\<forall>f. f \<in> take_foundry newDB \<longrightarrow> total_supply f = fset_sum (fset_map newDB take_single_basic) 
      (\<lambda>b. case native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"
      by (metis apply_tx_transitive_foundry assms concrete_foundry_transaction_in_ledger.apply_transaction_foundry_def concrete_foundry_transaction_in_ledger.apply_transaction_native_tokens_def concrete_foundry_transaction_in_ledger.total_supply_consistency_after_transaction db_basics_apply_transaction sum_nuo_tokens_def take_basics_def)
    thus ?thesis
      unfolding sum_nuo_tokens_def take_basics_def
      using newFoundryDB by blast
  qed
qed
  
end

end