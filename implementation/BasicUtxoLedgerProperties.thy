theory BasicUtxoLedgerProperties
  imports Main IotaUtxoLedgerAlias "./BasicUtxoLedger" 
begin


locale using_basic_utxo_ledger = 
  basic_utxo_ledger_implementation
begin

section \<open>1. Basic UTXO properties\<close>

subsection \<open>1.1. Constant Supply\<close>

theorem constant_supply:
  shows "sum_amount DB = sum_amount (apply_valid_transaction)"
  by (simp add: apply_tx_amt_constant tx_valid)

subsection \<open>1.2. Unspent Output Consumption\<close>

theorem unspent_outputs_consumption:
  shows "\<forall>u \<in> inp tx. u \<in> DB \<and> u \<notin> apply_valid_transaction"
  using apply_valid_transaction_def apply_transaction_to_db_def inputs_not_in_outputs_def tx_valid tx_valid_def inputs_in_db_def 
  by auto 

subsection \<open>1.3. No Double Spending\<close>

theorem no_double_spending:
  assumes "tx_valid DB tx1" 
      and "tx_valid (apply_transaction_to_db DB tx1 inp out) tx2"
  shows "inp tx1 \<inter> inp tx2 = {}"
  using apply_transaction_to_db_def assms(1) assms(2) inputs_in_db_def outputs_not_in_db_def tx_valid_def 
  by fastforce

end

end