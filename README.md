# About

This is a repository for Isabelle/HOL code to accompany the Master's Final Thesis: "Formal Verification of IOTA UTXO Output Type Extensions".

To view the base UTXO model specification, start by visiting `BasicUtxoLedger.thy` for the model and `BasicUtxoLedgerProperties.thy` for a succinct summary of its properties. To see the IOTA EUTXO model specification, see `IotaUtxoLedger.thy` as well as `IotaUtxoLedgerProperties.thy`.

# Structure

The code in this repository is organized into three main directories: `abstract`, `implementation`, and `shared`.

## Abstract

This directory contains the abstract definitions of the UTXO ledgers.

- `AbstractBasicUtxoLedger.thy`: This file contains the abstract definition of a basic UTXO ledger.
- `AbstractIotaAliasUtxoLedger.thy`: This file contains the abstract definition of an IOTA Alias UTXO ledger.
- `AbstractIotaFoundryUtxoLedger.thy`: This file contains the abstract definition of an IOTA Foundry UTXO ledger.

## Implementation

This directory contains the concrete implementations of the UTXO ledgers and their properties.

- `BasicUtxoLedger.thy`: This file contains the concrete implementation of a basic UTXO ledger.
- `BasicUtxoLedgerProperties.thy`: This file contains the essential properties of the basic UTXO ledger.
- `IotaUtxoLedger.thy`: This file contains the concrete implementation of an IOTA UTXO ledger.
- `IotaUtxoLedgerAlias.thy`: This file extends `IotaUtxoLedger.thy` and contains the concrete implementation of an IOTA Alias UTXO ledger.
- `IotaUtxoLedgerFoundry.thy`: This file extends `IotaUtxoLedger.thy` and contains the concrete implementation of an IOTA Foundry UTXO ledger.
- `IotaUtxoLedgerProperties.thy`: This file contains the essential properties of the IOTA UTXO ledgers.

## Shared

This directory contains shared definitions and utilities that are used across the project.

- `FiniteNatSet.thy`: This file contains helper lemmas that are used throughout the other files.
- `Hash.thy`: This file contains the definition of a unique hash identifier.
