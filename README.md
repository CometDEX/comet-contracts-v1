# Comet Contracts

Smart Contracts explicitly written for Soroban.

## How to Test

### Without logs

```cargo test```

### With logs

```cargo test -- --nocapture```

## Create a WASM Release Build

```cargo build --target wasm32-unknown-unknown --release```

## Security Assumptions

Comet pools require trusted SEP-41 token contracts whose transfers debit the sender and credit the recipient by exactly the requested amount. Pool operations verify both observed balance changes and reject transfer fees, in-call rebases, and other mismatches atomically. These checks cannot establish that an actively malicious token contract is trustworthy because the token contract controls its reported balances.

Factory registration identifies a pool created through the factory; it does not endorse the pool's tokens. Integrations must independently allowlist the token contracts and pools they trust.

## Best Practices Used

1. All Rust code is linted with Clippy with the command `cargo clippy`.

2. Function and local variable names follow snake_case. Structs or Enums follow CamelCase and Constants have all capital letters.

# Frontend

An example frontend has also been built that integrates the logic flow from the current v1 smart contracts. It can be found in the Frontend repository in the CometDEX github organization.
- Further documentation will be provided for understanding the Frontend starter implementation as well as general smart contract logic.
