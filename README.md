# Comet Contracts

Smart Contracts explicitly written for Soroban.

## Supported Pool Assets

Pools accept only deployed Stellar Asset Contracts, including native XLM and
classic issued assets. Pool initialization rejects Wasm token contracts. SAC
acceptance does not imply endorsement of an asset or its issuer controls.

## How to Test

### Without logs

```sh
make test
```

### With logs

```sh
make test COMET_TEST_ARGS='-- --nocapture'
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

## Secure Factory Deployment

Factory initialization requires authorization from the address used to deploy
the factory and verifies that address and the deployment salt reproduce the
factory's contract ID. This prevents another account from selecting the pool
WASM hash between factory deployment and initialization.

After building the optimized contracts, the deployment script creates and
initializes a factory using the same source identity and salt:

```bash
./deploy_factory.sh <network> <source-identity> [32-byte-hex-salt]
```

## Best Practices Used

1. All Rust code is linted with Clippy with the command `cargo clippy`.

2. Function and local variable names follow snake_case. Structs or Enums follow CamelCase and Constants have all capital letters.

# Frontend

An example frontend has also been built that integrates the logic flow from the current v1 smart contracts. It can be found in the Frontend repository in the CometDEX github organization.
- Further documentation will be provided for understanding the Frontend starter implementation as well as general smart contract logic.
