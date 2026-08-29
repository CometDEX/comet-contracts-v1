# Comet Contracts

Smart Contracts explicitly written for Soroban.

## How to Test

### Without logs

```sh
make test
```

### With logs

```sh
make build
cargo test --workspace --all-targets -- --nocapture
```

## Create a WASM Release Build

The repository pins Rust 1.91.1 and the `wasm32v1-none` target in
`rust-toolchain.toml`. Build and optimize both contracts with Stellar CLI:

```sh
make build
```

The deployable artifacts are written to:

- `target/wasm32v1-none/optimized/comet.wasm`
- `target/wasm32v1-none/optimized/comet_factory.wasm`

## Best Practices Used

1. All Rust code is linted with Clippy with the command `cargo clippy`.

2. Function and local variable names follow snake_case. Structs or Enums follow CamelCase and Constants have all capital letters.

# Frontend

An example frontend has also been built that integrates the logic flow from the current v1 smart contracts. It can be found in the Frontend repository in the CometDEX github organization.
- Further documentation will be provided for understanding the Frontend starter implementation as well as general smart contract logic.
