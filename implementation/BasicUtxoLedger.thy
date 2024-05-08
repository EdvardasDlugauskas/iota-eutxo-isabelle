theory BasicUtxoLedger
  imports Main "../shared/Hash" "../abstract/AbstractBasicUtxoLedger"
begin

type_synonym UTXO_id_type = hash
type_synonym addr_type = nat
type_synonym amount_type = nat

datatype UTXO_type = UTXO (UTXO_id: UTXO_id_type) (UTXO_addr: addr_type) (UTXO_amount: amount_type)

datatype TX_type = TX (inp: "UTXO_type set") (out: "UTXO_type set")

definition inputs_in_db :: "UTXO_type set \<Rightarrow> TX_type \<Rightarrow> bool" where
  "inputs_in_db db tx = (\<forall>u. u \<in> inp tx \<longrightarrow> u \<in> db)"

definition outputs_not_in_db :: "UTXO_type set \<Rightarrow> TX_type \<Rightarrow> bool" where
  "outputs_not_in_db db tx = (\<forall>u. u \<in> out tx \<longrightarrow> u \<notin> db)"

definition inputs_not_in_outputs :: "TX_type \<Rightarrow> bool" where
  "inputs_not_in_outputs tx = (inp tx \<inter> out tx = {} \<and> fset_intersect (inp tx) (out tx) UTXO_id = {})"

definition sum_amount :: "UTXO_type set \<Rightarrow> nat" where
  "sum_amount UTXOs = fset_sum UTXOs UTXO_amount"

definition inp_out_same_amount_sum :: "TX_type \<Rightarrow> bool" where
  "inp_out_same_amount_sum t  = (sum_amount (inp t) = sum_amount (out t))"

definition nonzero_outputs :: "TX_type \<Rightarrow> bool" where
  "nonzero_outputs t = (\<forall> u. u \<in> (out t) \<longrightarrow> (UTXO_amount u) > 0)"

definition apply_transaction_to_db :: "UTXO_type set \<Rightarrow> TX_type \<Rightarrow> (TX_type \<Rightarrow> UTXO_type set) \<Rightarrow> (TX_type \<Rightarrow> UTXO_type set) \<Rightarrow> UTXO_type set" where
  "apply_transaction_to_db DB tx tx_inp tx_out = (DB - tx_inp tx) \<union> tx_out tx"

definition UTXO_id_unique :: "UTXO_type set \<Rightarrow> bool" where
"UTXO_id_unique db = fset_unique db UTXO_id"

definition UTXO_amt_positive :: "UTXO_type set \<Rightarrow> bool" where
  "UTXO_amt_positive db = (\<forall>u. u \<in> db \<longrightarrow> UTXO_amount u > 0)"

definition UTXO_set_valid :: "UTXO_type set \<Rightarrow> bool" where
  "UTXO_set_valid db = (db \<noteq> {} \<and> finite db \<and> UTXO_id_unique db \<and> UTXO_amt_positive db)"

definition tx_valid :: "UTXO_type set \<Rightarrow> TX_type \<Rightarrow> bool" where
  "tx_valid db tx = 
    (UTXO_set_valid (inp tx) 
    \<and> UTXO_set_valid (out tx)
    \<and> nonzero_outputs tx
    \<and> inputs_in_db db tx 
    \<and> inp_out_same_amount_sum tx 
    \<and> inputs_not_in_outputs tx
    \<and> outputs_not_in_db db tx)"

locale basic_utxo_ledger_implementation = hashes + 
  fixes DB :: "UTXO_type set"
    and tx :: "TX_type"
  assumes db_valid: "UTXO_set_valid DB"
    and tx_valid: "tx_valid DB tx"
begin

definition apply_valid_transaction :: "UTXO_type set"  where
  "apply_valid_transaction = apply_transaction_to_db DB tx inp out"

lemma db_sums_additivity:
  fixes db_one :: "UTXO_type set"
    and db_two :: "UTXO_type set"
  assumes a1: "db_one \<inter> db_two = {}"
      and a2: "union_db = db_one \<union> db_two"
      and a3: "finite db_one"
      and a4: "finite db_two"
    shows "sum_amount union_db = sum_amount db_one + sum_amount db_two"
  using a3 a2 a4 a1
proof (induct db_one arbitrary: union_db)
  case empty
  have "sum_amount {} = 0"
    unfolding sum_amount_def fset_sum_def
    by auto
  thus ?case
    using empty by simp
next
  case c2: (insert x F)
  obtain prev_db where prev_db: "prev_db = F \<union> db_two"
    by simp
  have pu_db: "union_db = insert x prev_db"
    by (simp add: c2.prems(1) prev_db)
  have ins_xF: "sum_amount (insert x F) = UTXO_amount x + sum_amount F"
    unfolding sum_amount_def fset_sum_def
    by (simp add: c2.hyps(1) c2.hyps(2))
  have "sum_amount prev_db = sum_amount F + sum_amount db_two"
    using a4 c2.hyps(3) c2.prems(3) prev_db by blast
  thus ?case
    using pu_db prev_db ins_xF
    by (metis UNIV_I Un_iff c2(1) c2(2) c2(5) c2(6) finite_Un fset_commute.fold_insert fset_sum_def group_cancel.add1 insert_disjoint(1) subsetI sum_amount_def)
qed

lemma db_sums_additivity_minus:
  fixes db_one :: "UTXO_type set"
    and db_two :: "UTXO_type set"
  assumes "db_two \<subseteq> db_one"
      and a3: "finite db_one"
      and a4: "finite db_two"
  shows "sum_amount (db_one - db_two) = sum_amount db_one - sum_amount db_two"
proof-
  show ?thesis
    by (metis Diff_disjoint Diff_partition a3 a4 assms(1) db_sums_additivity diff_add_inverse finite_Diff)
qed


lemma apply_tx_amt_constant:
  fixes new_DB :: "UTXO_type set"
  assumes "new_DB = apply_valid_transaction"
    and "old_sum = sum_amount DB"
    and "new_sum = sum_amount new_DB"
    and "tx_valid DB tx"
  shows "old_sum = new_sum"
proof-
  have a: "sum_amount (inp tx) = sum_amount (out tx)"
    using inp_out_same_amount_sum_def tx_valid tx_valid_def by auto
  have b: "new_DB = (DB - inp tx) \<union> out tx"
    by (simp add: apply_valid_transaction_def apply_transaction_to_db_def assms(1))
  have c_preq: "sum_amount ((DB - inp tx) \<union> out tx) = (sum_amount DB - sum_amount (inp tx)) + sum_amount (out tx)"
  proof-
    have "(DB - inp tx) \<inter> out tx = {}"
      using outputs_not_in_db_def tx_valid tx_valid_def by fastforce
    have first: "sum_amount ((DB - inp tx) \<union> out tx) = (sum_amount (DB - (inp tx))) + sum_amount (out tx)"
      using outputs_not_in_db_def tx_valid tx_valid_def
      using UTXO_set_valid_def \<open>(DB - inp tx) \<inter> out tx = {}\<close> db_sums_additivity db_valid by auto
    show ?thesis
      by (metis UTXO_set_valid_def db_sums_additivity_minus db_valid first inputs_in_db_def subsetI tx_valid tx_valid_def)
  qed
  have c_one: "sum_amount new_DB = (sum_amount DB - sum_amount (inp tx)) + sum_amount (out tx)"
    using b c_preq by blast
   have d: "old_sum = new_sum"
     by (metis (no_types, lifting) Diff_disjoint Diff_partition UTXO_set_valid_def a assms(2) assms(3) c_one db_sums_additivity db_valid finite_Diff inputs_in_db_def le_add1 le_add_diff_inverse2 subsetI tx_valid tx_valid_def)
  thus ?thesis
    by simp
qed

interpretation concrete_basic_transaction:
  basic_transaction tx inp out UTXO_id UTXO_amount
proof
  show "finite (inp tx)"
    using UTXO_set_valid_def tx_valid tx_valid_def by auto
  show "inp tx \<noteq> {}"
    using UTXO_set_valid_def tx_valid tx_valid_def by auto
  show "\<And>out. out \<in> inp tx \<Longrightarrow> 0 < UTXO_amount out"
    using UTXO_amt_positive_def UTXO_set_valid_def db_valid inputs_in_db_def tx_valid tx_valid_def by auto
  show "finite (out tx)"
    using UTXO_set_valid_def tx_valid tx_valid_def by auto
  show "out tx \<noteq> {}"
    using UTXO_set_valid_def tx_valid tx_valid_def by auto
  show "\<And>outa. outa \<in> out tx \<Longrightarrow> 0 < UTXO_amount outa"
    using nonzero_outputs_def tx_valid tx_valid_def by auto
  show "fset_sum (inp tx) UTXO_amount = fset_sum (out tx) UTXO_amount"
    using inp_out_same_amount_sum_def sum_amount_def tx_valid tx_valid_def by force
  show "fset_unique (inp tx) UTXO_id"
    using UTXO_id_unique_def UTXO_set_valid_def tx_valid tx_valid_def by auto
  show "fset_unique (out tx) UTXO_id"
    using UTXO_set_valid_def tx_valid tx_valid_def
    by (simp add: UTXO_id_unique_def)
  show "fset_intersect (inp tx) (out tx) UTXO_id = {}"
    using inputs_not_in_outputs_def tx_valid tx_valid_def by blast
qed

interpretation concrete_basic_UTXO: 
  basic_UTXO_ledger DB UTXO_id UTXO_amount apply_transaction_to_db
proof
  show "basic_UTXO_DB_definitions.utxos_unique
     UTXO_id
     DB"
    using UTXO_id_unique_def UTXO_set_valid_def basic_UTXO_DB_definitions.utxos_unique_def db_valid by auto
  show "0 < basic_UTXO_DB_definitions.db_amt_sum 
          UTXO_amount
         DB"
  proof-
    have "DB \<noteq> {}"
      using UTXO_set_valid_def db_valid by blast
    then have u_gt_0: "\<forall>u. u \<in> DB \<longrightarrow> (UTXO_amount u > 0)"
      using UTXO_amt_positive_def UTXO_set_valid_def db_valid by presburger
    obtain utxo_sum where utxo_sum: "utxo_sum = fset_sum DB UTXO_amount"
      by simp
    then have "utxo_sum \<ge> 0"
      by blast
    then have "utxo_sum \<noteq> 0"
      using db_valid UTXO_amount_def UTXO_amt_positive_def u_gt_0
      by (metis UTXO_set_valid_def linorder_not_less nat_sum_ge_any_elem subset_empty subset_emptyI utxo_sum)
    then have "utxo_sum > 0"
      by simp
    thus ?thesis
      by (simp add: basic_UTXO_DB_definitions.db_amt_sum_def utxo_sum)
  qed
  show "finite DB"
    using UTXO_set_valid_def db_valid by blast
  show "\<And>some_DB tx tx_inp tx_out. apply_transaction_to_db some_DB tx tx_inp tx_out = some_DB - tx_inp tx \<union> tx_out tx"
    by (simp add: apply_transaction_to_db_def)
qed 

end

end


