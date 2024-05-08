theory AbstractBasicUtxoLedger
    imports Main "../shared/FiniteNatSet"
begin 

locale basic_output =
  fixes out :: "'o"
    and amount :: "nat"
  assumes nonzero_amount: "amount > 0"
begin
end

locale basic_output_set =
  fixes outs :: "'o set"
    and o_oid :: "'o \<Rightarrow> 'oid"
    and o_amt :: "'o \<Rightarrow> nat"
  assumes fin: "finite outs"
    and not_empty: "outs \<noteq> {}"
    and outs_basic_output: "\<And> out. out \<in> outs \<Longrightarrow> (basic_output (o_amt out))"
    and outs_unique: "fset_unique outs o_oid"
begin

definition amt_sum :: "nat" where
"amt_sum = fset_sum outs o_amt"

lemma total_amt_positive: "amt_sum > 0"
  using amt_sum_def basic_output_set_axioms basic_output_set_def
  by (metis all_not_in_conv basic_output.nonzero_amount bot.not_eq_extremum bot_nat_0.extremum_unique bot_nat_def nat_sum_ge_any_elem outs_basic_output)

lemma total_amt_non_0: "amt_sum \<noteq> 0"
  using total_amt_positive
  by blast

lemma total_amt_bounded: "\<exists> b :: nat. amt_sum \<le> b"
  using amt_sum_def basic_output_set_axioms basic_output_set_def Finite_Set.fold_def
  by blast

end

locale basic_transaction =
  fixes tx :: "'tx"
    and tx_inp :: "'tx \<Rightarrow> 'o set"
    and tx_out :: "'tx \<Rightarrow> 'o set"
    and o_oid  :: "'o \<Rightarrow> 'oid"
    and o_amt  :: "'o \<Rightarrow> nat"
  assumes input_basic_output_set: "basic_output_set (tx_inp tx) o_oid o_amt"
      and output_basic_output_set: "basic_output_set (tx_out tx) o_oid o_amt"
      and total_amount_unchanged: "fset_sum (tx_inp tx) o_amt = fset_sum (tx_out tx) o_amt"
      and input_output_dont_intersect: "fset_intersect (tx_inp tx) (tx_out tx) o_oid = {}"

begin

end


\<comment> \<open>Use a helper locale to define the definitions, 
as we cannot use definitions from inside the locale in the 
assumptions of the same locale\<close>
locale basic_UTXO_DB_definitions = 
  fixes DB :: "'o set"
    and utxo_id :: "'o \<Rightarrow> 'oid"
    and utxo_amt  :: "'o \<Rightarrow> nat"
begin

definition utxos_unique :: "'o set \<Rightarrow> bool" where 
  "utxos_unique db = fset_unique db utxo_id"

definition db_amt_sum :: "'o set \<Rightarrow> nat" where
  "db_amt_sum db = fset_sum db utxo_amt"

lemma db_sum_linear:
  fixes db_one :: "'o set"
    and db_two :: "'o set"
  assumes a1: "db_one \<inter> db_two = {}"
      and a2: "union_db = db_one \<union> db_two"
      and a3: "finite db_one"
      and a4: "finite db_two"
    shows "db_amt_sum union_db = db_amt_sum db_one + db_amt_sum db_two"
  using a3 a2 a4 a1
proof (induct db_one arbitrary: union_db)
  case empty
  have "db_amt_sum {} = 0"
    unfolding db_amt_sum_def fset_sum_def
    by auto
  thus ?case
    using empty by simp
next
  case c2: (insert x F)
  obtain prev_db where prev_db: "prev_db = F \<union> db_two"
    by simp
  have pu_db: "union_db = insert x prev_db"
    by (simp add: c2.prems(1) prev_db)
  have ins_xF: "db_amt_sum (insert x F) = utxo_amt x + db_amt_sum F"
    unfolding db_amt_sum_def fset_sum_def
    by (simp add: c2.hyps(1) c2.hyps(2))
  have "db_amt_sum prev_db = db_amt_sum F + db_amt_sum db_two"
    using a4 c2.hyps(3) c2.prems(3) prev_db by blast
  thus ?case
    using pu_db prev_db ins_xF
    by (metis UNIV_I Un_iff c2(1) c2(2) c2(5) c2(6) finite_Un fset_commute.fold_insert fset_sum_def group_cancel.add1 insert_disjoint(1) subsetI db_amt_sum_def)
qed

lemma db_diff_linear:
  fixes db_one :: "'o set"
    and db_two :: "'o set"
  assumes "db_two \<subseteq> db_one"
      and a3: "finite db_one"
      and a4: "finite db_two"
  shows "db_amt_sum (db_one - db_two) = db_amt_sum db_one - db_amt_sum db_two"
proof-
  show ?thesis
    by (metis Diff_disjoint Diff_partition a3 a4 assms(1) db_sum_linear diff_add_inverse finite_Diff)
qed

end
locale basic_UTXO_DB = basic_UTXO_DB_definitions DB utxo_id utxo_amt
  for DB :: "'o set"
    and utxo_id :: "'o \<Rightarrow> 'oid"
    and utxo_amt  :: "'o \<Rightarrow> nat"
  +
  assumes "utxos_unique DB"
      and "db_amt_sum DB > 0"
      and "finite DB"
begin

definition transaction_valid :: "'tx \<Rightarrow> ('tx \<Rightarrow> 'o set) \<Rightarrow> ('tx \<Rightarrow> 'o set) \<Rightarrow>  bool" where
  "transaction_valid tx tx_inp tx_out = 
    (tx_inp tx \<subseteq> DB \<and> 
      (fset_map (tx_out tx) utxo_id) \<inter> (fset_map DB utxo_id) = {})" 

lemma outputs_not_in_db:
  assumes "transaction_valid tx tx_inp tx_out"
  shows "tx_out tx \<inter> DB = {}"
proof-
  have ids_not_in_db: "(fset_map (tx_out tx) utxo_id) \<inter> (fset_map DB utxo_id) = {}"
    by (meson assms transaction_valid_def)
  then have "\<forall>u. u \<in> DB \<longrightarrow> (utxo_id u) \<notin> (fset_map (tx_out tx) utxo_id) \<longrightarrow> (u \<notin> (tx_out tx))"
    by (simp add: fset_map_def)
  thus ?thesis
    using fset_map_def ids_not_in_db by fastforce
qed

end

locale basic_UTXO_ledger_definitions = basic_UTXO_DB DB utxo_id utxo_amt
  for DB :: "'o set"
    and utxo_id :: "'o \<Rightarrow> 'oid"
    and utxo_amt  :: "'o \<Rightarrow> nat"
  +
    fixes apply_tx :: "'o set \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow> 'o set) \<Rightarrow> ('t \<Rightarrow> 'o set) \<Rightarrow> 'o set"
begin

definition apply_tx_utxos_unique :: "bool" where
  "apply_tx_utxos_unique = 
    (\<forall>tx tx_inp tx_out. (basic_transaction tx tx_inp tx_out utxo_id utxo_amt) \<and>
      (transaction_valid tx tx_inp tx_out) \<longrightarrow> 
      (let new_DB = apply_tx DB tx tx_inp tx_out in 
        (basic_UTXO_DB_definitions.utxos_unique utxo_id new_DB)
      )
    )"

definition apply_tx_amt_constant :: "bool" where
  "apply_tx_amt_constant = 
    (\<forall>tx tx_inp tx_out. basic_transaction tx tx_inp tx_out utxo_id utxo_amt \<and>
      (transaction_valid tx tx_inp tx_out) \<longrightarrow> 
      (let new_DB = apply_tx DB tx tx_inp tx_out in 
        (basic_UTXO_DB_definitions.db_amt_sum utxo_amt DB = basic_UTXO_DB_definitions.db_amt_sum utxo_amt new_DB)
      )
    )"

end

locale basic_UTXO_ledger = basic_UTXO_ledger_definitions DB utxo_id utxo_amt apply_tx
  for DB :: "'o set"
    and utxo_id :: "'o \<Rightarrow> 'oid"
    and utxo_amt :: "'o \<Rightarrow> nat"
    and apply_tx :: "'o set \<Rightarrow> 't \<Rightarrow> ('t \<Rightarrow> 'o set) \<Rightarrow> ('t \<Rightarrow> 'o set) \<Rightarrow> 'o set"
  +
  assumes apply_uses_inp_out: "apply_tx some_DB tx tx_inp tx_out = (some_DB - tx_inp tx) \<union> tx_out tx"
begin

lemma supply_constant:
  shows "apply_tx_amt_constant"
proof -
  have "\<And>tx tx_inp tx_out.
             basic_transaction tx tx_inp tx_out utxo_id utxo_amt \<and>
             (transaction_valid tx tx_inp tx_out) \<longrightarrow>
             (let new_DB = apply_tx DB tx tx_inp tx_out
              in basic_UTXO_DB_definitions.db_amt_sum utxo_amt DB =
                 basic_UTXO_DB_definitions.db_amt_sum utxo_amt new_DB)"
  proof
    fix tx tx_inp tx_out
    assume a: "basic_transaction (tx::'t) tx_inp tx_out utxo_id utxo_amt \<and> transaction_valid tx tx_inp tx_out"
    have a1: "basic_transaction tx tx_inp tx_out utxo_id utxo_amt" using a by auto
    have a2: "transaction_valid tx tx_inp tx_out" using a by auto
    obtain ndb where ndb: "ndb = apply_tx DB tx tx_inp tx_out" by simp
    have ndb_sets: "ndb = (DB - tx_inp tx) \<union> tx_out tx"
      by (simp add: apply_uses_inp_out ndb)
    have all_fin: "finite DB \<and> finite (tx_inp tx) \<and> finite (tx_out tx) \<and> finite ndb"
      using basic_UTXO_DB_def basic_UTXO_ledger_definitions_axioms basic_UTXO_ledger_definitions_def
            basic_output_set.fin basic_transaction.output_basic_output_set
            finite_Diff finite_Un finite_subset ndb_sets transaction_valid_def
      by (metis a)
    have "basic_UTXO_DB_definitions.db_amt_sum utxo_amt DB = basic_UTXO_DB_definitions.db_amt_sum utxo_amt ndb"
      using ndb ndb_sets fset_sum_def all_fin
            transaction_valid_def
            basic_output_set.amt_sum_def
            basic_transaction.input_basic_output_set
            basic_transaction.output_basic_output_set
            basic_transaction.total_amount_unchanged
      unfolding basic_UTXO_DB_definitions.db_amt_sum_def
    proof - (* This sub-proof is generated by sledgehammer, looks reasonable. *)
      have "tx_inp tx \<subseteq> DB \<and> tx_out tx \<inter> DB = {}"
        using transaction_valid_def outputs_not_in_db unfolding fset_map_def
        by (meson a transaction_valid_def)
      then have "tx_inp tx \<union> (DB - tx_inp tx) = DB"
        by auto
      then have f1: "fset_sum DB utxo_amt = Finite_Set.fold (\<lambda>a. (+) (utxo_amt a)) 0 (tx_inp tx \<union> {a \<in> DB. a \<notin> tx_inp tx})"
        by (simp add: fset_sum_def set_diff_eq)
      have f2: "tx_inp tx \<inter> {a \<in> DB. a \<notin> tx_inp tx} = {}"
        by blast
      have f3: "basic_output_set (tx_out tx) utxo_id utxo_amt"
        by (metis (no_types) a basic_transaction.output_basic_output_set)
      have f4: "basic_output_set.amt_sum (tx_inp tx) utxo_amt = basic_output_set.amt_sum (tx_out tx) utxo_amt"
        by (metis a1 basic_output_set.amt_sum_def basic_transaction.input_basic_output_set basic_transaction.total_amount_unchanged f3)
      have f5: "basic_output_set.amt_sum (tx_inp tx) utxo_amt = fset_sum (tx_inp tx) utxo_amt"
        by (metis a basic_output_set.amt_sum_def basic_transaction.input_basic_output_set)
      have f6: "tx_out tx \<inter> {a \<in> DB. a \<notin> tx_inp tx} \<union> tx_out tx \<inter> (DB \<inter> tx_inp tx) = {}"
        using \<open>tx_inp tx \<subseteq> DB \<and> tx_out tx \<inter> DB = {}\<close> by blast
      have "apply_tx DB tx tx_inp tx_out = DB - tx_inp tx \<union> tx_out tx"
        using ndb ndb_sets by presburger
      then show "fset_sum DB utxo_amt = fset_sum ndb utxo_amt"
        using f6 f5 f4 f3 f2 f1 by (simp add: all_fin basic_output_set.amt_sum_def fset_commute.fold_set_union_disj fset_sum_def inf_sup_aci(5) ndb set_diff_eq)
    qed
    thus "(let new_DB = apply_tx DB tx tx_inp tx_out
           in basic_UTXO_DB_definitions.db_amt_sum utxo_amt DB =
              basic_UTXO_DB_definitions.db_amt_sum utxo_amt new_DB)"
      using ndb by auto
  qed
  thus ?thesis
    using apply_tx_amt_constant_def by blast
qed

lemma utxos_unique:
  shows "apply_tx_utxos_unique"
proof-
  have target: "\<And>tx tx_inp tx_out.
             basic_transaction tx tx_inp tx_out utxo_id utxo_amt \<and>
             transaction_valid tx tx_inp tx_out \<longrightarrow>
              (let new_DB = apply_tx DB tx tx_inp tx_out in (basic_UTXO_DB_definitions.utxos_unique utxo_id new_DB))"
  proof
    fix tx tx_inp tx_out
    assume a1: "basic_transaction (tx::'t) tx_inp tx_out utxo_id utxo_amt \<and> transaction_valid tx tx_inp tx_out"
    show "(let new_DB = apply_tx DB tx tx_inp tx_out in (basic_UTXO_DB_definitions.utxos_unique utxo_id new_DB))"
    proof-
      have old_db_unique: "basic_UTXO_DB_definitions.utxos_unique utxo_id DB"
        using basic_UTXO_DB_def basic_UTXO_ledger_definitions_axioms basic_UTXO_ledger_definitions_def by blast
      have tx_inp_unique: "basic_UTXO_DB_definitions.utxos_unique utxo_id (tx_inp tx)"
        by (meson a1 basic_UTXO_DB_definitions.utxos_unique_def basic_output_set.outs_unique basic_transaction.input_basic_output_set)
      have tx_out_unique: "basic_UTXO_DB_definitions.utxos_unique utxo_id (tx_out tx)"
        by (meson a1 basic_UTXO_DB_definitions.utxos_unique_def basic_output_set.outs_unique basic_transaction.output_basic_output_set)
      obtain diff_db where diff_db: "diff_db = DB - (tx_inp tx)" by simp
      have diff_unique: "basic_UTXO_DB_definitions.utxos_unique utxo_id diff_db"
        by (metis (mono_tags, lifting) DiffD1 basic_UTXO_DB_definitions.utxos_unique_def fset_unique_def diff_db old_db_unique)
      obtain ndb where ndb: "ndb = apply_tx DB tx tx_inp tx_out" by simp
      have "ndb = diff_db \<union> tx_out tx"
        by (simp add: apply_uses_inp_out diff_db ndb)
      have "diff_db \<subset> DB"
        by (metis Diff_disjoint a1 basic_output_set_def basic_transaction.input_basic_output_set diff_db diff_subset inf.absorb2 inf_sup_aci(1) order_less_le transaction_valid_def)
      have "(fset_map (tx_out tx) utxo_id) \<inter> (fset_map DB utxo_id) = {}"
        by (meson a1 transaction_valid_def)
      have "basic_UTXO_DB_definitions.utxos_unique utxo_id DB"
        by (simp add: old_db_unique)
      have "basic_UTXO_DB_definitions.utxos_unique utxo_id (tx_out tx)"
        by (simp add: tx_out_unique)
      then have "basic_UTXO_DB_definitions.utxos_unique utxo_id (DB \<union> tx_out tx)"
        using fset_map_linear fset_unique_linear
        unfolding fset_map_def
        by (smt (verit) Int_commute \<open>fset_map (tx_out tx) utxo_id \<inter> fset_map DB utxo_id = {}\<close> basic_UTXO_DB_definitions.utxos_unique_def fset_unique_linear old_db_unique)
      have "basic_UTXO_DB_definitions.utxos_unique utxo_id (diff_db \<union> tx_out tx)"
        by (smt (verit, best) Diff_iff Un_iff \<open>utxos_unique (DB \<union> tx_out tx)\<close> diff_db fset_unique_def utxos_unique_def)
      then have ndb_unique: "basic_UTXO_DB_definitions.utxos_unique utxo_id ndb"
        by (simp add: \<open>ndb = diff_db \<union> tx_out tx\<close>)
      thus ?thesis
        by (simp add: ndb)
    qed
  qed
  thus ?thesis
    using apply_tx_utxos_unique_def by blast
qed

subsection \<open>Progress\<close>
text \<open>A UTXO Ledger is never "stuck", i.e. there always exists a new transaction that can be applied.\<close>
theorem progress:
  assumes "basic_transaction tx tx_inp tx_out utxo_id utxo_amt"
      and "transaction_valid tx tx_inp tx_out"
      and "new_DB = apply_tx DB tx tx_inp tx_out"
  shows "basic_UTXO_DB new_DB utxo_id utxo_amt"
proof -
  have result: "basic_UTXO_DB new_DB utxo_id utxo_amt"
  proof - (* Generated by Sledgehammer *)
    have f1: "db_amt_sum new_DB = db_amt_sum DB"
      using apply_tx_amt_constant_def assms(1) assms(2) assms(3) supply_constant by fastforce
    have "finite new_DB"
    proof -
      have "basic_output_set (tx_out tx) utxo_id utxo_amt"
        by (meson assms(1) basic_transaction.output_basic_output_set)
      then have "finite (DB - tx_inp tx \<union> tx_out tx)"
        by (meson basic_UTXO_DB_axioms basic_UTXO_DB_def basic_output_set_def finite_Diff finite_UnI)
      then show ?thesis
        using apply_uses_inp_out assms(3) by presburger
    qed
    then show ?thesis
      by (metis apply_tx_utxos_unique_def assms(1) assms(2) assms(3) basic_UTXO_DB_axioms basic_UTXO_DB_def f1 utxos_unique)
  qed
  thus ?thesis
    by simp
qed

subsection \<open>No Double-Spend\<close>
text \<open>If a UTXO is spent in a transaction, it cannot be spent again.\<close>
theorem no_double_spend:
  assumes "basic_transaction tx tx_inp tx_out utxo_id utxo_amt"
    and "transaction_valid tx tx_inp tx_out"
    and "new_DB = apply_tx DB tx tx_inp tx_out"
    and "u \<in> (tx_inp tx)"
  shows "u \<notin> new_DB"
  by (smt (verit, ccfv_threshold) Diff_Diff_Int Diff_eq_empty_iff Diff_iff Un_iff apply_uses_inp_out assms(2) assms(3) assms(4) outputs_not_in_db transaction_valid_def)


text \<open>None of one transaction inputs refer to any of the other transaction outputs.\<close>
definition tx_independent :: "'tx \<Rightarrow> 'tx \<Rightarrow> ('tx \<Rightarrow> 'o set) \<Rightarrow> ('tx \<Rightarrow> 'o set) \<Rightarrow> ('o \<Rightarrow> 'oid) \<Rightarrow> bool" where 
"tx_independent tx1 tx2 tx_inp tx_out o_oid = 
  ((tx_inp tx1 \<inter> tx_out tx2 = {} \<and> fset_intersect (tx_inp tx1) (tx_out tx2) o_oid = {})
  \<and>(tx_inp tx2 \<inter> tx_out tx1 = {} \<and> fset_intersect (tx_inp tx2) (tx_out tx1) o_oid = {}))"

subsection \<open>Locality\<close>
text \<open>Transactions are commutative, i.e. they can be applied in any order.\<close>
theorem independent_tx_commutative:
  assumes "basic_transaction tx1 tx_inp tx_out utxo_id utxo_amt"
    and "basic_transaction tx2 tx_inp tx_out utxo_id utxo_amt"
    and "tx_independent tx1 tx2 tx_inp tx_out utxo_id"
  shows "apply_tx (apply_tx DB tx2 tx_inp tx_out) tx1 tx_inp tx_out = apply_tx (apply_tx DB tx1 tx_inp tx_out) tx2 tx_inp tx_out"
proof -
  have indep_conditions: 
    "tx_inp tx1 \<inter> tx_out tx2 = {} \<and> tx_inp tx2 \<inter> tx_out tx1 = {}
    \<and> fset_intersect (tx_inp tx1) (tx_out tx2) utxo_id = {} \<and> fset_intersect (tx_inp tx2) (tx_out tx1) utxo_id = {}"
    by (meson assms(3) tx_independent_def)

  obtain DB_tx1 where DB_tx1: "DB_tx1 = apply_tx DB tx1 tx_inp tx_out" by simp
  obtain DB_tx2 where DB_tx2: "DB_tx2 = apply_tx DB tx2 tx_inp tx_out" by simp

  obtain newDB1 where newDB1: "newDB1 = apply_tx (DB_tx2) tx1 tx_inp tx_out" by simp
  obtain newDB2 where newDB2: "newDB2 = apply_tx (DB_tx1) tx2 tx_inp tx_out" by simp


  have "newDB1 = (((DB - tx_inp tx2) \<union> tx_out tx2) - tx_inp tx1) \<union> tx_out tx1"
    by (simp add: DB_tx2 apply_uses_inp_out newDB1)
  moreover have db1_flat: "newDB1 = DB - (tx_inp tx2) \<union> (tx_out tx2) - (tx_inp tx1) \<union> (tx_out tx1)"
    by (simp add: calculation)
  moreover have order_swap: "newDB1 = DB - (tx_inp tx1) \<union> (tx_out tx1) - (tx_inp tx2) \<union> (tx_out tx2)"
    using db1_flat indep_conditions by blast

  have "newDB2 = (((DB - tx_inp tx1) \<union> tx_out tx1) - tx_inp tx2) \<union> tx_out tx2"
    by (simp add: DB_tx1 apply_uses_inp_out newDB2)
  moreover have db2_flat: "newDB2 = DB - (tx_inp tx1) \<union> (tx_out tx1) - (tx_inp tx2) \<union> (tx_out tx2)"
    by (simp add: DB_tx1 apply_uses_inp_out newDB2)

  have "newDB1 = newDB2"
    by (simp add: db2_flat order_swap)
  thus ?thesis
    using DB_tx1 DB_tx2 newDB1 newDB2 by fastforce
qed

end (* locale basic_UTXO_ledger *)

end 