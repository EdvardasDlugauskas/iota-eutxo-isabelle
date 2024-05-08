theory IotaUtxoLedgerAlias
  imports IotaUtxoLedger
begin

context iota_utxo_ledger_implementation
begin

lemma take_alias_union:
  shows "take_alias (A \<union> B) = take_alias A \<union> take_alias B"
  using take_alias_def by auto 

lemma take_alias_filters_by_is_alias:
  shows "take_alias A = take_alias (fset_filter A is_alias)"
  by (smt (verit, best) Collect_cong UTXO.simps(11) fset_filter_def is_alias_def mem_Collect_eq take_alias_def)

lemma AliasDB_valid_implies_unique_aliases:
  assumes "DB_valid db"
      and "u1 = AliasU b1 a1"
      and "u1 \<in> A"
      and "u2 = AliasU b2 a2"
      and "u2 \<in> A"
      and "alias_id a1 \<noteq> alias_id a2"
  shows "u1 \<noteq> u2"
  using assms(2) assms(4) assms(6) by blast

lemma alias_exists_in_db:
  assumes "DB_valid db"
      and "us = AliasU bs a"  
      and "us \<in> db"
  shows "\<exists>u b. u = AliasU b a \<and> u \<in> db"
proof -
  from assms(3) show "\<exists> u.  \<exists>b. u = AliasU b a  \<and> u  \<in> db"
    using assms(2) by auto
qed

lemma take_alias_single_element:
  assumes "DB_valid db"
      and "db = {su1, su2}"
      and "take_alias db = {a1, a2}"
    shows "\<exists>b. (su1 = AliasU b a1 \<or> su2 = AliasU b a1)"
  by (smt (verit, ccfv_threshold) assms(2) assms(3) insert_iff mem_Collect_eq singletonD take_alias_def)

lemma take_alias_is_alias:
  assumes "DB_valid db"
    and "u \<in> db"
    and "take_alias {u} = {a}"
  shows "is_alias u"
  using assms(3) is_alias_def take_alias_def by force

lemma take_alias_is_aliasu:
  assumes "DB_valid db"
    and "u \<in> db"
    and "is_alias u"
  shows "\<exists>b a. u = AliasU b a"
  by (metis UTXO.exhaust UTXO.simps(10) UTXO.simps(12) assms(3) is_alias_def)

lemma take_alias_aliases_map_to_utxo1:
  assumes "DB_valid db"
      and "u1 \<in> db" and "u2 \<in> db"
      and "u1 \<noteq> u2"
      and "u1 = AliasU b1 a1"
      and "u2 = AliasU b2 a2"
    shows "a1 \<noteq> a2"
  using AliasDB_valid_def DB_valid_def alias_ids_unique_def assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) by blast

lemma take_alias_aliases_map_to_utxo:
  assumes "DB_valid db"
      and "u1 \<in> db" and "u2 \<in> db"
      and "u1 \<noteq> u2"
      and "take_alias {u1} = {a1}"
      and "take_alias {u2} = {a2}"
    shows "a1 \<noteq> a2"
  by (smt (verit, ccfv_SIG) CollectD assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) singletonD singletonI take_alias_aliases_map_to_utxo1 take_alias_def)

lemma take_alias_is_subset_image:
  assumes "DB_valid db"
      and "adb = take_alias db"
      and "a \<in> adb"
    shows "\<exists>!u. \<exists>b. u = AliasU b a \<and> u \<in> db"
proof-
  have "\<exists>u. \<exists>b. u = AliasU b a \<and> u \<in> db"
    using assms(2) assms(3) take_alias_def by auto
  have "\<forall>a1 \<in> adb. \<exists>!u. \<exists>b. u = AliasU b a1 \<and> u \<in> db"
    by (smt (verit, ccfv_SIG) assms(1) assms(2) mem_Collect_eq take_alias_aliases_map_to_utxo1 take_alias_def)
  thus ?thesis
    by (meson \<open>\<exists>u b. u = AliasU b a \<and> u \<in> db\<close> assms(1) take_alias_aliases_map_to_utxo1)
qed


lemma alias_id_take_alias:
  assumes "fset_map (take_alias {u1}) alias_id = a1"
    and "fset_map (take_alias {u2}) alias_id = a2"
    and "u1 = u2"
  shows "a1 = a1"
  by simp

lemma alias_unique_in_db:
  assumes "DB_valid db"
      and "u1 = AliasU b1 a"  
      and "u1 \<in> db"
      and "u2 = AliasU b2 a"
      and "u2 \<in> db"
  shows "u1 = u2"
  using assms(1) assms(2) assms(3) assms(4) assms(5) take_alias_aliases_map_to_utxo1 by blast

lemma alias_ids_unique_in_db:
  assumes "DB_valid db"
    and "adb = take_alias db"
  shows "fset_unique adb alias_id"
proof -
  have "fset_unique adb alias_id"
  proof-
    have "\<forall>a \<in> adb. \<exists>!u. \<exists>b. u \<in> db \<and> u = AliasU b a"
      by (metis assms(1) assms(2) take_alias_is_subset_image)
    have "\<And>a1 a2. a1 \<in> adb \<and> a2 \<in> adb \<and> a1 \<noteq> a2 \<Longrightarrow> alias_id a1 \<noteq> alias_id a2"
    proof-
      fix a1 a2
      assume "a1 \<in> adb \<and> a2 \<in> adb \<and> a1 \<noteq> a2"

      obtain u1 where u1: "\<exists>b. u1 = AliasU b a1" and "u1 \<in> db"
        by (meson \<open>\<forall>a\<in>adb. \<exists>!u. \<exists>b. u \<in> db \<and> u = AliasU b a\<close> \<open>a1 \<in> adb \<and> a2 \<in> adb \<and> a1 \<noteq> a2\<close>)

      obtain u2 where u2: "\<exists>b. u2 = AliasU b a2" and "u2 \<in> db"
        by (meson \<open>\<forall>a\<in>adb. \<exists>!u. \<exists>b. u \<in> db \<and> u = AliasU b a\<close> \<open>a1 \<in> adb \<and> a2 \<in> adb \<and> a1 \<noteq> a2\<close>)

      have "u1 \<noteq> u2"
        using \<open>a1 \<in> adb \<and> a2 \<in> adb \<and> a1 \<noteq> a2\<close> u1 u2 by fastforce

      show "alias_id a1 \<noteq> alias_id a2"
        using AliasDB_valid_def DB_valid_def \<open>u1 \<in> db\<close> \<open>u1 \<noteq> u2\<close> \<open>u2 \<in> db\<close> alias_ids_unique_def assms(1) u1 u2 by blast
    qed
    thus ?thesis
      by (simp add: fset_unique_def)
  qed
  
  thus ?thesis by (simp add: fset_unique_def)
qed

lemma alias_backwards:
  assumes "DB_valid A" and "DB_valid B"
    and "u = AliasU b a"
    and "u \<in> A" and "u \<in> B"
    and "newA = A - B"
  shows "a \<notin> take_alias newA"
  using alias_unique_in_db assms(1) assms(3) assms(4) assms(5) assms(6) take_alias_def by fastforce

lemma take_alias_diff:
  assumes "B \<subseteq> A"
    and "DB_valid A" and "DB_valid B"
  shows "take_alias (A - B) = take_alias A - take_alias B"
proof
  have "\<forall>x a. AliasU a x \<in> B \<longrightarrow> AliasU a x \<in> A"
    using assms by blast
  then have "\<forall>x. x \<in> take_alias B \<longrightarrow> x \<in> take_alias A"
    using take_alias_def by auto
  then have "take_alias B \<inter> take_alias A = take_alias B"
    by blast

  show "take_alias (A - B) \<subseteq> take_alias A - take_alias B"
  proof
    fix x
    assume "x \<in> take_alias (A - B)"
    show "x \<in> take_alias A - take_alias B"
    proof
      show "x \<in> take_alias A"
        using \<open>x \<in> take_alias (A - B)\<close> take_alias_def by auto
      show "x \<notin> take_alias B"
      proof
        assume "x \<in> take_alias B"
        have "\<forall>ua ub. AliasU ub ua \<in> B \<longrightarrow> AliasU ub ua \<in> A"
          using \<open>\<forall>x a. AliasU a x \<in> B \<longrightarrow> AliasU a x \<in> A\<close> by blast
        have "take_alias A \<inter> take_alias B = take_alias B"
          using \<open>take_alias B \<inter> take_alias A = take_alias B\<close> by blast

        obtain u where u: "\<exists>b. u = AliasU b x" and "u \<in> B"
          using \<open>x \<in> take_alias B\<close> take_alias_def by moura
        have "u \<in> A"
          using \<open>u \<in> B\<close> assms(1) by auto
        have "u \<notin> (A - B)"
          using \<open>u \<in> B\<close> by auto

        then have "\<exists>buniq. AliasU buniq x \<in> (A - B) = False"
          using u by blast
        then have "\<forall>b a. AliasU b a \<in> (A - B) \<longrightarrow> a \<in> take_alias (A - B)"
          using take_alias_def by auto
        then have "\<forall>b. AliasU b x \<in> (A - B) \<longrightarrow> x \<in> take_alias (A - B) "
          by blast 

        then have "\<exists>b. (let un = AliasU b x in un \<in> (A - B))"
        proof - (* Sledgehammer *)
          obtain bb :: "UTXO set \<Rightarrow> AliasT \<Rightarrow> bool" where
            f1: "\<forall>X0 X1. bb X0 X1 = (\<exists>Y0. AliasU Y0 X1 \<in> X0)"
            by moura
          then have "bb (A - B) x"
            using \<open>x \<in> take_alias (A - B)\<close> take_alias_def by auto
          then show ?thesis
            using f1 by meson
        qed

        then obtain u2 where u2: "\<exists>b. u2 = AliasU b x" and "u2 \<in> (A - B)"
          by metis

        thus False
          using \<open>u \<in> A\<close> \<open>u \<in> B\<close> \<open>x \<in> take_alias (A - B)\<close> assms(2) assms(3) alias_backwards iota_utxo_ledger_implementation_axioms u by blast
      qed
    qed
  qed
  show "take_alias A - take_alias B \<subseteq> take_alias (A - B)"
    using take_alias_def by force
qed

section "AliasDB is an alias_ledger"

lemma unique_alias_ids: 
  assumes "a1 \<in> AliasDB"
      and "a2 \<in> AliasDB"
      and "alias_id a1 = alias_id a2"
    shows "a1 = a2"
  by (metis (no_types) alias_ids_unique_in_db assms(1) assms(2) assms(3) fset_unique_def iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def iota_utxo_ledger_implementation_def)

interpretation concrete_iota_alias_ledger: alias_ledger AliasDB alias_id
  by (metis alias_ids_unique_in_db alias_ledger.intro iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def)

section "Valid Transaction is a valid alias_transaction"

lemma inp_set_alias_output_set:
  shows "alias_output_set (take_alias (tx_inp ValidTransaction)) alias_id"
  using alias_ids_unique_in_db alias_output_set.intro transaction_valid_def tx_valid by auto

lemma out_set_alias_output_set:
  shows "alias_output_set (take_alias (tx_out ValidTransaction)) alias_id"
  using alias_ids_unique_in_db alias_output_set.intro transaction_valid_def tx_valid by auto

interpretation concrete_alias_transaction: 
  alias_transaction "(take_alias (tx_inp ValidTransaction))" "(take_alias (tx_out ValidTransaction))" alias_id
  by (simp add: alias_transaction.intro inp_set_alias_output_set out_set_alias_output_set)

section "Valid Transaction and AliasDB is alias_transaction_in_ledger"

interpretation concrete_alias_transaction_in_ledger: 
  alias_transaction_in_ledger "(take_alias (tx_inp ValidTransaction))" "(take_alias (tx_out ValidTransaction))" alias_id AliasDB 
proof
  show "take_alias (tx_inp ValidTransaction) \<subseteq> AliasDB"
  proof -
    have "transaction_inputs_exist_in_ledger DB ValidTransaction"
      using transaction_valid_def tx_valid by blast
    then show ?thesis
      using iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def iota_utxo_ledger_implementation_def take_alias_def transaction_inputs_exist_in_ledger_def 
      by auto
  qed

  have "fset_intersect (take_alias (tx_out ValidTransaction)) AliasDB alias_id = {}"
    unfolding fset_intersect_def transaction_valid_def
    by (smt (verit, best) Collect_empty_eq IntD1 IntD2 Un_Int_eq(1) Un_Int_eq(4) alias_ids_unique_def disjoint_iff_not_equal iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def take_alias_is_subset_image transaction_valid_def utxo_sets_independent_def)

  thus "fset_intersect (take_alias (tx_out ValidTransaction)) AliasDB alias_id
    \<subseteq> fset_intersect (take_alias (tx_inp ValidTransaction)) (take_alias (tx_out ValidTransaction)) alias_id"
    by blast
    
qed

section "Thus, applying Valid Transaction results in a valid Abstract Alias Ledger"

lemma take_alias_disjoint_transitive:
  shows "take_alias (DB - (tx_inp ValidTransaction)) = take_alias DB - take_alias (tx_inp ValidTransaction)"
  by (meson subsetI take_alias_diff transaction_inputs_exist_in_ledger_def transaction_valid_def tx_valid db_valid)

lemma take_alias_union_transitive:
  shows "take_alias (DB \<union> (tx_out ValidTransaction)) = take_alias DB \<union> take_alias (tx_out ValidTransaction)"
  using take_alias_union transaction_valid_def tx_valid by presburger

lemma apply_tx_transitive_alias_unfolded:
  assumes "newDB = apply_valid_transaction"
    and "alias_inputs = (take_alias (tx_inp ValidTransaction))"
    and "alias_outputs = (take_alias (tx_out ValidTransaction))"
  shows "take_alias newDB = 
        take_alias DB - take_alias (tx_inp ValidTransaction) \<union> take_alias (tx_out ValidTransaction)"
  using apply_valid_transaction_def
  by (simp add: apply_tx_def assms(1) take_alias_disjoint_transitive take_alias_union)

lemma apply_tx_transitive_alias:
  assumes "newDB = apply_valid_transaction"
    and "alias_inputs = (take_alias (tx_inp ValidTransaction))"
    and "alias_outputs = (take_alias (tx_out ValidTransaction))"
  shows "take_alias newDB = (AliasDB - alias_inputs) \<union> alias_outputs"
proof -
  have "iota_utxo_ledger_implementation_axioms DB AliasDB FoundryDB ValidTransaction"
    using iota_utxo_ledger_implementation.axioms(2) iota_utxo_ledger_implementation_axioms by force
  then show ?thesis
    by (simp add: apply_tx_transitive_alias_unfolded assms(1) assms(2) assms(3) iota_utxo_ledger_implementation_axioms_def)
qed

theorem apply_produces_valid_alias_ledger:
  assumes newDB: "newDB = apply_valid_transaction"
      and newAliasDB: "newAliasDB = take_alias newDB"
  shows "alias_ledger newAliasDB alias_id"
  using apply_tx_transitive_alias concrete_alias_transaction_in_ledger.apply_transaction_def concrete_alias_transaction_in_ledger.apply_transaction_preserves_validity newAliasDB newDB by presburger

section "Apply produces valid implementation DB"

lemma unique_basic_ids_in_newDB:
  assumes a1: "newDB = apply_valid_transaction"
  shows "fset_unique newDB utxo_to_id"
  using apply_valid_transaction_def
  by (smt (verit, ccfv_threshold) Diff_subset Un_iff apply_tx_def assms basic_ids_unique_def fset_unique_def subset_iff transaction_valid_def tx_valid utxo_sets_independent_def)

theorem apply_produces_valid_aliasdb:
  assumes "newDB = apply_valid_transaction"
      and "adb = take_alias newDB"
      and "inps = (tx_inp ValidTransaction)"
      and "outs = (tx_out ValidTransaction)"
      and "alias_inputs = (take_alias (tx_inp ValidTransaction))"
      and "alias_outputs = (take_alias (tx_out ValidTransaction))"
  shows "AliasDB_valid newDB"
proof-
  have "adb = (AliasDB - alias_inputs) \<union> alias_outputs"
    by (simp add: apply_tx_transitive_alias assms(1) assms(2) assms(5) assms(6))

  have "AliasDB = take_alias (fset_filter DB is_alias)"
    using take_alias_filters_by_is_alias iota_utxo_ledger_implementation_axioms iota_utxo_ledger_implementation_axioms_def iota_utxo_ledger_implementation_def by auto

  have "alias_inputs = take_alias (fset_filter inps is_alias)"
    using take_alias_filters_by_is_alias assms(3) assms(5) by presburger

  have "alias_outputs = take_alias (fset_filter outs is_alias)"
    using take_alias_filters_by_is_alias assms(4) assms(6) by presburger

  have "AliasDB_valid (DB - tx_inp ValidTransaction)"
    by (smt (verit, ccfv_SIG) AliasDB_valid_def DB_valid_def DiffD1 alias_ids_unique_def db_valid)

  have "utxo_sets_independent DB (tx_out ValidTransaction)"
    using transaction_valid_def tx_valid by blast

  have "utxo_sets_independent (DB - tx_inp ValidTransaction) (tx_out ValidTransaction)"
  proof-
    have "utxo_sets_independent DB (tx_out ValidTransaction)"
      using transaction_valid_def tx_valid by blast
    have "(DB - tx_inp ValidTransaction) \<subseteq> DB"
      by simp
    have "\<forall>u \<in> DB. utxo_sets_independent {u} (tx_out ValidTransaction)"
      unfolding utxo_sets_independent_def
      by (smt (z3) IntE Int_Un_eq(2) Int_insert_left_if1 Un_Int_eq(1) Un_Int_eq(3) Un_insert_left \<open>utxo_sets_independent DB (tx_out ValidTransaction)\<close> alias_ids_unique_def basic_ids_unique_def fset_unique_def insert_disjoint(2) sup_commute utxo_sets_independent_def)
    then have "\<forall>u \<in> (DB - tx_inp ValidTransaction). utxo_sets_independent {u} (tx_out ValidTransaction)"
      by blast
    thus ?thesis
      using apply_valid_transaction_def
      by (smt (verit) Diff_iff Diff_triv Un_Diff alias_ids_unique_def apply_tx_def basic_ids_unique_def disjoint_iff_not_equal transaction_valid_def tx_valid unique_basic_ids_in_newDB utxo_sets_independent_def)
  qed

  thus ?thesis
    using apply_valid_transaction_def AliasDB_valid_def \<open>utxo_sets_independent (DB - tx_inp ValidTransaction) (tx_out ValidTransaction)\<close> apply_tx_def assms(1) utxo_sets_independent_def by auto
qed

end

end