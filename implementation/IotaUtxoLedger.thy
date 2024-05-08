theory IotaUtxoLedger
  imports 
    Main  
    "../shared/Hash" 
    "../abstract/AbstractIotaAliasUtxoLedger"
    "../abstract/AbstractIotaFoundryUtxoLedger"    
    "../shared/FiniteNatSet"
begin

datatype BasicT = Basic (basic_id : hash) (basic_amount : nat) (native_tokens : "(hash \<rightharpoonup> nat)")
datatype AliasT = Alias (alias_id : hash)
datatype FoundryT = Foundry (foundry_id : hash)  (total_supply : nat) 

datatype UTXO = BasicU BasicT
              | AliasU BasicT AliasT
              | FoundryU BasicT FoundryT

datatype TransactionT = TransactionT (tx_inp: "UTXO set") (tx_out: "UTXO set")
type_synonym Ledger = "UTXO set"
type_synonym AliasLedger = "AliasT set"

definition is_alias :: "UTXO \<Rightarrow> bool" where
  "is_alias utxo = (case utxo of AliasU _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition take_alias :: "UTXO set \<Rightarrow> AliasT set" where
  "take_alias utxos = {a. \<exists>b. AliasU b a \<in> utxos}"

definition is_foundry :: "UTXO \<Rightarrow> bool" where
  "is_foundry utxo = (case utxo of FoundryU  _ _ \<Rightarrow> True | _ \<Rightarrow> False)"

definition take_foundry :: "UTXO set \<Rightarrow> FoundryT set" where
  "take_foundry utxos = {f. \<exists>b. FoundryU b f \<in> utxos}"

definition take_single_basic :: "UTXO \<Rightarrow> BasicT" where
  "take_single_basic utxo = (case utxo of BasicU b \<Rightarrow> b | AliasU b _ \<Rightarrow> b | FoundryU b _ \<Rightarrow> b)"

definition take_basics :: "UTXO set \<Rightarrow> BasicT set" where
  "take_basics utxos = fset_map utxos take_single_basic"

definition utxo_to_id :: "UTXO \<Rightarrow> hash" where
  "utxo_to_id u = basic_id (take_single_basic u)"

definition utxo_to_amount :: "UTXO \<Rightarrow> nat" where
  "utxo_to_amount u = basic_amount (take_single_basic u)"

definition utxo_to_native_tokens :: "UTXO \<Rightarrow> (hash \<rightharpoonup> nat)" where
  "utxo_to_native_tokens u = native_tokens (take_single_basic u)"

definition UTXO_valid :: "UTXO \<Rightarrow> bool" where
  "UTXO_valid u \<equiv> 
    utxo_to_amount u > 0"

definition UTXO_set_valid :: "UTXO set \<Rightarrow> bool" where
  "UTXO_set_valid utxos \<equiv> 
      finite utxos \<and>
      utxos \<noteq> {} \<and>
      (\<forall>u \<in> utxos. UTXO_valid u) \<and>
      fset_unique utxos utxo_to_id"

definition apply_tx :: "Ledger \<Rightarrow> TransactionT \<Rightarrow> (TransactionT \<Rightarrow> UTXO set) \<Rightarrow> (TransactionT \<Rightarrow> UTXO set) \<Rightarrow> Ledger" where
  "apply_tx DB tx tinp tout = (DB - tinp tx) \<union> tout tx"

definition sum_amount :: "Ledger \<Rightarrow> nat" where
  "sum_amount ledger = fset_sum ledger utxo_to_amount"

definition transaction_inputs_exist_in_ledger :: "Ledger \<Rightarrow> TransactionT \<Rightarrow> bool" where
  "transaction_inputs_exist_in_ledger db tx = (\<forall>u \<in> tx_inp tx. u \<in> db)"

definition transaction_amounts_constant :: "TransactionT \<Rightarrow> bool" where
  "transaction_amounts_constant tx = (sum_amount (tx_inp tx) = sum_amount (tx_out tx))"

definition transaction_unique_basic_outputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_basic_outputs tx \<equiv> 
    fset_unique (tx_out tx) utxo_to_id"

definition transaction_unique_basic_inputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_basic_inputs tx \<equiv> 
    fset_unique (tx_inp tx) utxo_to_id"

definition alias_ids_unique :: "Ledger \<Rightarrow> bool" where
  "alias_ids_unique db = (
    \<forall>u1 u2 b1 a1 b2 a2. u1 \<in> db \<and> u2 \<in> db \<and> u1 = AliasU b1 a1 \<and> u2 = AliasU b2 a2 \<and> u1 \<noteq> u2 
      \<longrightarrow> alias_id a1 \<noteq> alias_id a2)"

definition foundry_ids_unique :: "Ledger \<Rightarrow> bool" where
  "foundry_ids_unique db = (
    \<forall>u1 u2 b1 f1 b2 f2. u1 \<in> db \<and> u2 \<in> db \<and> u1 = FoundryU b1 f1 \<and> u2 = FoundryU b2 f2 \<and> u1 \<noteq> u2 
      \<longrightarrow> foundry_id f1 \<noteq> foundry_id f2)"

definition basic_ids_unique :: "Ledger \<Rightarrow> bool" where
  "basic_ids_unique db = (fset_unique db utxo_to_id)"

definition transaction_unique_alias_outputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_alias_outputs tx \<equiv> alias_ids_unique (tx_out tx)"

definition transaction_unique_alias_inputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_alias_inputs tx \<equiv> alias_ids_unique (tx_inp tx)"

definition transaction_unique_foundry_outputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_foundry_outputs tx \<equiv> foundry_ids_unique (tx_out tx)"

definition transaction_unique_foundry_inputs :: "TransactionT \<Rightarrow> bool" where
  "transaction_unique_foundry_inputs tx \<equiv> foundry_ids_unique (tx_inp tx)"

definition utxo_sets_independent :: "UTXO set \<Rightarrow> UTXO set \<Rightarrow> bool" where
  "utxo_sets_independent set1 set2 \<equiv> 
     (set1 \<inter> set2 = {})
     \<and> alias_ids_unique (set1 \<union> set2) 
     \<and> basic_ids_unique (set1 \<union> set2)"

definition sum_tokens :: "BasicT set \<Rightarrow> hash \<Rightarrow> nat" where
  "sum_tokens utxos token_id = fset_sum utxos (\<lambda>utxo. case native_tokens utxo token_id of 
    Some x \<Rightarrow> x | None \<Rightarrow> 0)"

definition input_tokens :: "TransactionT \<Rightarrow> hash \<Rightarrow> nat" where
  "input_tokens tx token_id = sum_tokens (take_basics (tx_inp tx)) token_id"

definition output_tokens :: "TransactionT \<Rightarrow> hash \<Rightarrow> nat" where
  "output_tokens tx token_id = sum_tokens (take_basics (tx_out tx)) token_id"

definition foundry_not_present_input_output_tokens_equal :: "TransactionT \<Rightarrow> bool" where
  "foundry_not_present_input_output_tokens_equal tx \<equiv>
    \<forall>token_id. token_id \<notin> fset_map (take_foundry (tx_inp tx)) foundry_id \<longrightarrow>
      input_tokens tx token_id = output_tokens tx token_id"

definition foundry_present_total_supply_updated :: "TransactionT \<Rightarrow> bool" where
  "foundry_present_total_supply_updated tx \<equiv>
    \<forall>token_id. \<forall>fi \<in> take_foundry (tx_inp tx). foundry_id fi = token_id \<longrightarrow>
      (
        (\<exists>fo \<in> take_foundry (tx_out tx). foundry_id fo = token_id \<and>
          total_supply fo = total_supply fi + output_tokens tx token_id - input_tokens tx token_id)
        \<or> \<not>(\<exists>fo \<in> take_foundry (tx_out tx). foundry_id fo = token_id)
      )"

definition foundry_ids_persisted :: "TransactionT \<Rightarrow> bool" where
  "foundry_ids_persisted tx \<equiv> \<forall>fo. fo \<in> take_foundry (tx_out tx) \<longrightarrow> (\<exists>fi \<in> take_foundry (tx_inp tx). foundry_id fi = foundry_id fo)"

definition native_tokens_transaction_valid :: "TransactionT \<Rightarrow> bool" where
  "native_tokens_transaction_valid tx \<equiv> 
    foundry_not_present_input_output_tokens_equal tx 
    \<and> foundry_present_total_supply_updated tx
    \<and> foundry_ids_persisted tx"

definition native_token_totals_valid :: "Ledger \<Rightarrow> bool" where
  "native_token_totals_valid db \<equiv> 
    (\<forall>f. f \<in> take_foundry db \<longrightarrow> total_supply f = fset_sum db (\<lambda>b. case utxo_to_native_tokens b (foundry_id f) of None \<Rightarrow> 0 | Some x \<Rightarrow> x))"

lemma utxo_sets_inp_not_in_out:
  assumes "utxo_sets_independent s1 s2"
    and "u1 \<in> s1"
  shows "\<forall>u2 \<in> s2. utxo_to_id u1 \<noteq> utxo_to_id u2"
  by (smt (verit, best) Un_upper2 assms(1) assms(2) basic_ids_unique_def disjoint_iff_not_equal fset_unique_unfold subsetD sup_ge1 utxo_sets_independent_def)

lemma utxo_sets_inp_out_no_intersect:
  assumes "utxo_sets_independent s1 s2"
  shows "fset_intersect s1 s2 utxo_to_id = {}"
  using assms fset_intersect_def utxo_sets_inp_not_in_out by fastforce
  
definition AliasDB_valid :: "Ledger \<Rightarrow> bool" where
  "AliasDB_valid db = alias_ids_unique db"

definition FoundryDB_valid :: "Ledger \<Rightarrow> bool" where
  "FoundryDB_valid db \<equiv> foundry_ids_unique db \<and> native_token_totals_valid db"
                              
definition DB_valid :: "Ledger \<Rightarrow> bool" where
  "DB_valid db \<equiv> UTXO_set_valid db \<and> AliasDB_valid db \<and> FoundryDB_valid db"

definition transaction_valid :: "Ledger \<Rightarrow> TransactionT \<Rightarrow> bool" where
  "transaction_valid db tx \<equiv>
      UTXO_set_valid (tx_out tx) \<and> 
      UTXO_set_valid (tx_inp tx) \<and>
      
      utxo_sets_independent (tx_out tx) (tx_inp tx) \<and> 
      utxo_sets_independent db (tx_out tx) \<and>
      transaction_inputs_exist_in_ledger db tx \<and>
      transaction_amounts_constant tx \<and>

      transaction_unique_basic_outputs tx \<and>
      transaction_unique_basic_inputs tx \<and>

      DB_valid (tx_inp tx) \<and>
      DB_valid (tx_out tx) \<and>
          
      transaction_unique_alias_inputs tx \<and>
      transaction_unique_alias_outputs tx \<and>

      transaction_unique_foundry_inputs tx \<and>
      transaction_unique_foundry_outputs tx \<and>
      foundry_ids_unique ((tx_out tx) \<union> db) \<and>
      native_tokens_transaction_valid tx
      "

lemma inputs_not_in_outputs:
  assumes "transaction_valid db tx"
  shows "(tx_inp tx \<inter> tx_out tx = {})"
  by (metis Int_commute assms transaction_valid_def utxo_sets_independent_def)

lemma input_ids_not_in_outputs:
  assumes "transaction_valid db tx"
  shows "fset_intersect (tx_inp tx) (tx_out tx) utxo_to_id = {}"
  by (metis assms inf_sup_aci(5) inputs_not_in_outputs transaction_valid_def utxo_sets_independent_def utxo_sets_inp_out_no_intersect)

locale iota_utxo_ledger_implementation = hashes +
  fixes DB :: Ledger
    and AliasDB :: "AliasT set"
    and FoundryDB :: "FoundryT set"
    and ValidTransaction :: "TransactionT"
  assumes db_valid: "DB_valid DB"
    and "AliasDB = take_alias DB"
    and "FoundryDB = take_foundry DB"
    and tx_valid: "transaction_valid DB ValidTransaction"
begin

definition apply_valid_transaction :: "Ledger"  where
  "apply_valid_transaction = apply_tx DB ValidTransaction tx_inp tx_out"


lemma take_basics_union:
  shows "take_basics (A \<union> B) = take_basics A \<union> take_basics B"
  using take_basics_def
  by (simp add: fset_map_linear) 

lemma take_basics_diff:
    assumes "B \<subseteq> A"
    and "DB_valid A"
  shows "take_basics (A - B) = take_basics A - take_basics B"
proof
  have "\<forall>x. x \<in> take_basics B \<longrightarrow> x \<in> take_basics A"
    using take_basics_def
    by (smt (verit, ccfv_threshold) DiffD1 assms(1) double_diff dual_order.refl fset_map_def mem_Collect_eq)
  then have "take_basics B \<inter> take_basics A = take_basics B"
    using \<open>\<forall>x. x \<in> take_basics B \<longrightarrow> x \<in> take_basics A\<close> by blast

  show "take_basics (A - B) \<subseteq> take_basics A - take_basics B"
  proof
    fix x
    assume "x \<in> take_basics (A - B)"
    show "x \<in> take_basics A - take_basics B"
    proof
      show "x \<in> take_basics A"
        by (metis Diff_partition UnCI \<open>x \<in> take_basics (A - B)\<close> assms(1) fset_map_linear take_basics_def)     
      show "x \<notin> take_basics B"
        by (smt (verit, best) DB_valid_def DiffD1 DiffD2 UTXO_set_valid_def \<open>x \<in> take_basics (A - B)\<close> assms(1) assms(2) fset_map_def fset_unique_def mem_Collect_eq subset_iff take_basics_def utxo_to_id_def)
    qed
  qed

  show "take_basics A - take_basics B \<subseteq> take_basics (A - B)"
    using take_basics_def
    by (smt (verit, ccfv_threshold) Diff_iff fset_map_def mem_Collect_eq subsetI)
  
qed

lemma db_basics_apply_transaction: 
  assumes "newDB = apply_valid_transaction"
  shows "(take_basics newDB) = ((take_basics DB) - (take_basics (tx_inp ValidTransaction))) \<union> (take_basics (tx_out ValidTransaction))"
proof-
  have "newDB = (DB - (tx_inp ValidTransaction)) \<union> (tx_out ValidTransaction)"
    by (simp add: apply_tx_def apply_valid_transaction_def assms)
  then have "\<forall>u\<in>DB. \<exists>!ub. ub \<in> fset_map DB take_single_basic \<and> ub = take_single_basic u"
    using fset_map_def by fastforce
  then have "take_basics newDB = take_basics (DB - (tx_inp ValidTransaction)) \<union> take_basics (tx_out ValidTransaction)"
    using take_basics_union
    using apply_tx_def apply_valid_transaction_def assms by presburger
  then have "(DB) \<supseteq> ((tx_inp ValidTransaction))"
    using tx_valid
    unfolding transaction_valid_def
    using transaction_inputs_exist_in_ledger_def by auto
  then have "(take_basics DB) \<supseteq> (take_basics (tx_inp ValidTransaction))"
    by (metis subset_Un_eq take_basics_union)
  then have "take_basics newDB = ((take_basics DB) - (take_basics (tx_inp ValidTransaction))) \<union> (take_basics (tx_out ValidTransaction))"
    using take_basics_diff
    by (simp add: \<open>newDB = DB - tx_inp ValidTransaction \<union> tx_out ValidTransaction\<close> \<open>tx_inp ValidTransaction \<subseteq> DB\<close> db_valid take_basics_union)
  thus ?thesis
    by (simp add: \<open>take_basics newDB = take_basics (DB - tx_inp ValidTransaction) \<union> take_basics (tx_out ValidTransaction)\<close>)
qed


section "Basic UTXO Ledger"

subsection "DB is a Basic UTXO Ledger"

interpretation concrete_basic_UTXO_ledger: 
  basic_UTXO_ledger DB utxo_to_id utxo_to_amount apply_tx 
proof                                                     
  show "basic_UTXO_DB_definitions.utxos_unique utxo_to_id DB"
    using DB_valid_def basic_UTXO_DB_definitions.utxos_unique_def db_valid
    using UTXO_set_valid_def by auto
  show "0 < basic_UTXO_DB_definitions.db_amt_sum utxo_to_amount DB"
    by (metis DB_valid_def UTXO_set_valid_def UTXO_valid_def basic_UTXO_DB_definitions.db_amt_sum_def db_valid fset_sum_over_positives_is_positive)
  show "finite DB"
    using DB_valid_def db_valid
    by (simp add: UTXO_set_valid_def)
  show "\<And>some_DB tx tx_inp tx_out. apply_tx some_DB tx tx_inp tx_out = some_DB - tx_inp tx \<union> tx_out tx"
    by (simp add: apply_tx_def)
qed

subsection "ValidTransaction is a Basic Transaction"

interpretation concrete_basic_transaction:
  basic_transaction ValidTransaction tx_inp tx_out utxo_to_id utxo_to_amount
proof
  show "finite (tx_inp ValidTransaction)"
     using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "tx_inp ValidTransaction \<noteq> {}"
     using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "\<And>out. out \<in> tx_inp ValidTransaction \<Longrightarrow> 0 < utxo_to_amount out"
     using UTXO_set_valid_def transaction_valid_def tx_valid
     by (meson UTXO_valid_def)
  show "fset_unique (tx_inp ValidTransaction) utxo_to_id"
    using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "finite (tx_out ValidTransaction)"
    using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "tx_out ValidTransaction \<noteq> {}"
    using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "\<And>out. out \<in> tx_out ValidTransaction \<Longrightarrow> 0 < utxo_to_amount out"
    using UTXO_set_valid_def UTXO_valid_def transaction_valid_def tx_valid by auto
  show "fset_unique (tx_out ValidTransaction) utxo_to_id"
    using UTXO_set_valid_def transaction_valid_def tx_valid by presburger
  show "fset_sum (tx_inp ValidTransaction) utxo_to_amount = fset_sum (tx_out ValidTransaction) utxo_to_amount"
    using sum_amount_def transaction_amounts_constant_def transaction_valid_def tx_valid by presburger
  show "fset_intersect (tx_inp ValidTransaction) (tx_out ValidTransaction) utxo_to_id = {}"
    by (smt (verit, ccfv_SIG) Collect_empty_eq Diff_iff Un_Diff_Int Un_iff basic_ids_unique_def fset_intersect_def fset_unique_unfold sup_bot.right_neutral transaction_valid_def tx_valid utxo_sets_independent_def)
qed

(* Trivially follows from above, but we need this lemma to use the conclusion in other files*)
lemma is_concrete_basic_transaction: 
  "basic_transaction ValidTransaction tx_inp tx_out utxo_to_id utxo_to_amount"
  by (simp add: concrete_basic_transaction.basic_transaction_axioms)

subsection "Thus, Basic Ledger properties hold"

theorem apply_tx_amount_constant: 
  assumes "newDB = apply_valid_transaction"
  shows "fset_sum newDB utxo_to_amount = fset_sum DB utxo_to_amount"
  using concrete_basic_UTXO_ledger.apply_uses_inp_out concrete_basic_UTXO_ledger.db_amt_sum_def concrete_basic_UTXO_ledger.db_sum_linear apply_valid_transaction_def
  by (smt (verit, del_insts) DB_valid_def Diff_iff Diff_partition UTXO_set_valid_def Un_commute assms disjoint_iff_not_equal finite_Un subset_iff sum_amount_def transaction_amounts_constant_def transaction_inputs_exist_in_ledger_def transaction_valid_def tx_valid db_valid utxo_sets_independent_def)

theorem apply_tx_ids_unique: 
  assumes "newDB = apply_valid_transaction"
  shows "fset_unique newDB take_single_basic"
proof-
  have "fset_unique newDB utxo_to_id"
  proof-
    have "newDB = (DB - (tx_inp ValidTransaction)) \<union> (tx_out ValidTransaction)"
      using assms apply_valid_transaction_def apply_tx_def by auto
    moreover have "fset_unique DB utxo_to_id"
      using db_valid DB_valid_def UTXO_set_valid_def by blast
    moreover have "fset_unique (tx_inp ValidTransaction) utxo_to_id"
      using tx_valid transaction_valid_def DB_valid_def UTXO_set_valid_def by blast  
    moreover have "fset_unique (tx_out ValidTransaction) utxo_to_id"
      using tx_valid transaction_valid_def transaction_unique_basic_outputs_def by blast
    moreover have "utxo_sets_independent DB (tx_out ValidTransaction)"
      using tx_valid transaction_valid_def by blast
    moreover have "utxo_sets_independent (tx_inp ValidTransaction) (tx_out ValidTransaction)"
      using tx_valid transaction_valid_def 
      unfolding transaction_valid_def
      by (metis inputs_not_in_outputs sup.commute tx_valid utxo_sets_independent_def)
    ultimately show ?thesis
      by (smt (verit, best) DiffD1 Un_iff fset_unique_def utxo_sets_inp_not_in_out)
  qed
  
  have "fset_unique (take_basics newDB) basic_id"
  proof-
    have "take_basics newDB = (take_basics DB) - (take_basics (tx_inp ValidTransaction)) \<union> (take_basics (tx_out ValidTransaction))"
      using db_basics_apply_transaction assms by blast
    show ?thesis
      by (smt (verit, best) \<open>fset_unique newDB utxo_to_id\<close> fset_map_def fset_unique_def mem_Collect_eq take_basics_def utxo_to_id_def)  
  qed
  
  thus ?thesis
    by (metis \<open>fset_unique newDB utxo_to_id\<close> fset_unique_def utxo_to_id_def)
qed

end

end
