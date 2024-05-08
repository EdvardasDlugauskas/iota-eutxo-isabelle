theory IotaUtxoLedgerProperties
  imports Main IotaUtxoLedger IotaUtxoLedgerAlias IotaUtxoLedgerFoundry
begin

locale using_iota_utxo_ledger = 
  iota_utxo_ledger_implementation
begin

section \<open>1. Basic UTXO Properties\<close>

subsection \<open>1.1. Constant Supply\<close>

theorem constant_supply:
  shows "sum_amount DB = sum_amount (apply_valid_transaction)"
  using apply_tx_amount_constant sum_amount_def 
  by presburger

subsection \<open>1.2. Unspent Output Consumption\<close>

theorem unspent_outputs_consumption:
  shows "\<forall>u \<in> tx_inp ValidTransaction. u \<in> DB \<and> u \<notin> apply_valid_transaction"
  using apply_tx_def apply_valid_transaction_def transaction_valid_def transaction_inputs_exist_in_ledger_def tx_valid utxo_sets_inp_not_in_out
    unfolding transaction_inputs_exist_in_ledger_def
    by fastforce

subsection \<open>1.3. No Double Spending\<close>

theorem no_double_spending:
  assumes "transaction_valid DB tx1"
      and "nextDB = (apply_tx DB tx1 tx_inp tx_out)"
      and "transaction_valid nextDB tx2"
    shows "tx_inp tx1 \<inter> tx_inp tx2 = {}"
  using apply_tx_def assms(1) assms(2) assms(3) transaction_inputs_exist_in_ledger_def transaction_valid_def utxo_sets_independent_def 
  by auto

section \<open>2. Alias UTXO Properties\<close>

definition transaction_removes_alias :: "AliasT \<Rightarrow> UTXO set \<Rightarrow> UTXO set \<Rightarrow> bool" where
  "transaction_removes_alias alias inputs outputs = (alias \<in> take_alias inputs \<and> alias \<notin> take_alias outputs)"

subsection \<open>2.1 Alias Chain Constraint\<close>

theorem alias_continuity:
  assumes "alias \<in> AliasDB"
      and "inputs = (tx_inp ValidTransaction)"
      and "outputs = (tx_out ValidTransaction)"
      and "nextDB = apply_valid_transaction"
    shows "alias \<in> take_alias (nextDB) \<or> transaction_removes_alias alias inputs outputs"
  using Diff_iff UnI1 apply_tx_def apply_valid_transaction_def assms(1) assms(2) assms(3) assms(4) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def iota_utxo_ledger_implementation_def take_alias_def transaction_removes_alias_def by auto

section \<open>3. Foundry UTXO Properties\<close>

definition transaction_removes_foundry :: "FoundryT \<Rightarrow> UTXO set \<Rightarrow> UTXO set \<Rightarrow> bool" where
  "transaction_removes_foundry foundry inputs outputs = (foundry \<in> take_foundry inputs \<and> foundry \<notin> take_foundry outputs)"

definition ledger_total_token_sum :: "Ledger \<Rightarrow> hash \<Rightarrow> nat" where
  "ledger_total_token_sum ledger token_id = sum_nuo_tokens (take_basics ledger) native_tokens token_id"

subsection \<open>3.1 Foundry Chain Constraint\<close>

theorem foundry_continuity:
  assumes "foundry \<in> FoundryDB"
      and "inputs = (tx_inp ValidTransaction)"
      and "outputs = (tx_out ValidTransaction)"
      and "nextDB = apply_valid_transaction"
    shows "foundry \<in> take_foundry (nextDB) \<or> transaction_removes_foundry foundry inputs outputs"
  by (simp add: apply_tx_transitive_foundry assms(1) assms(2) assms(3) assms(4) transaction_removes_foundry_def)

subsection \<open>3.2 Foundry Native Token Supply Consistent\<close>

theorem foundry_native_token_amount_constant:
  assumes "nextDB = apply_valid_transaction"
      and "f \<in> (take_foundry nextDB)"
  shows "total_supply f = ledger_total_token_sum nextDB (foundry_id f)"
  using apply_produces_valid_foundry_ledger assms(1) assms(2) foundry_ledger_def ledger_total_token_sum_def by fastforce

end (* locale *)

end (* theory *)