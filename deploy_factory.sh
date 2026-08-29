#!/usr/bin/env bash

set -euo pipefail

if [[ $# -lt 2 || $# -gt 3 ]]; then
    echo "Usage: $0 <network> <source-identity> [32-byte-hex-salt]" >&2
    exit 1
fi

network=$1
source_identity=$2
salt=${3:-$(openssl rand -hex 32)}

pool_wasm=target/wasm32v1-none/optimized/comet.wasm
factory_wasm=target/wasm32v1-none/optimized/comet_factory.wasm

for artifact in "$pool_wasm" "$factory_wasm"; do
    if [[ ! -f "$artifact" ]]; then
        echo "Missing $artifact; run 'make build' first." >&2
        exit 1
    fi
done

if [[ ! "$salt" =~ ^[[:xdigit:]]{64}$ ]]; then
    echo "Salt must be exactly 32 bytes encoded as 64 hexadecimal characters." >&2
    exit 1
fi

deployer_address=$(stellar keys public-key "$source_identity")
pool_wasm_hash=$(stellar contract upload \
    --wasm "$pool_wasm" \
    --source-account "$source_identity" \
    --network "$network")
factory_wasm_hash=$(stellar contract upload \
    --wasm "$factory_wasm" \
    --source-account "$source_identity" \
    --network "$network")
factory_id=$(stellar contract deploy \
    --wasm-hash "$factory_wasm_hash" \
    --source-account "$source_identity" \
    --network "$network" \
    --salt "$salt")
stellar contract invoke \
    --id "$factory_id" \
    --source-account "$source_identity" \
    --network "$network" \
    -- \
    init \
    --deployer "$deployer_address" \
    --salt "$salt" \
    --pool_wasm_hash "$pool_wasm_hash"

echo "Factory: $factory_id"
echo "Pool WASM hash: $pool_wasm_hash"
