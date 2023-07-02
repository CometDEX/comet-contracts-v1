# Comet Contracts

Smart Contracts explicitly written for Soroban.

## How to Test

### Without logs

```cargo test```

### With logs

```cargo test -- --nocapture```

## Create a WASM Release Build

```cargo build --target wasm32-unknown-unknown --release```

## Best Practices Used

1. All Rust code is linted with Clippy with the command `cargo clippy`.

2. Function and local variable names follow snake_case. Structs or Enums follow CamelCase and Constants have all capital letters.
