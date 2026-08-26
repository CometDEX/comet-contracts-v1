#!/usr/bin/env bash

set -euo pipefail

exec >script_output.log 2>&1

if (( $# < 3 || $# > 4 )); then
    echo "Usage: $0 <identity> <token_contract_1> <token_contract_2> [network]"
    echo "The identity must hold the configured initial balance of each token."
    exit 1
fi

IDENTITY_STRING=$1
TOKEN_ID_1=$2
TOKEN_ID_2=$3
NETWORK=${4:-futurenet}

BALANCE_1=${COMET_BALANCE_1:-500000000}
BALANCE_2=${COMET_BALANCE_2:-500000000}
WEIGHT_1=${COMET_WEIGHT_1:-8000000}
WEIGHT_2=${COMET_WEIGHT_2:-2000000}
SWAP_FEE=${COMET_SWAP_FEE:-30000}

for VALUE in "$BALANCE_1" "$BALANCE_2" "$WEIGHT_1" "$WEIGHT_2" "$SWAP_FEE"; do
    if [[ ! "$VALUE" =~ ^[0-9]+$ ]]; then
        echo "Balances, weights, and swap fee must be non-negative integers."
        exit 1
    fi
done

if [[ "$TOKEN_ID_1" == "$TOKEN_ID_2" ]]; then
    echo "Token contract IDs must be different."
    exit 1
fi

if (( WEIGHT_1 + WEIGHT_2 != 10000000 )); then
    echo "COMET_WEIGHT_1 and COMET_WEIGHT_2 must sum to 10000000."
    exit 1
fi

make build >/dev/null

ADMIN_ADDRESS=$(stellar keys public-key "$IDENTITY_STRING")

POOL_WASM_HASH=$(stellar contract upload \
    --wasm target/wasm32v1-none/optimized/comet.wasm \
    --source-account "$IDENTITY_STRING" \
    --network "$NETWORK")

FACTORY_CONTRACT=$(stellar contract deploy \
    --wasm target/wasm32v1-none/optimized/comet_factory.wasm \
    --source-account "$IDENTITY_STRING" \
    --network "$NETWORK")

stellar contract invoke \
    --id "$FACTORY_CONTRACT" \
    --source-account "$IDENTITY_STRING" \
    --network "$NETWORK" \
    -- \
    init \
    --pool_wasm_hash "$POOL_WASM_HASH"

SALT=$(openssl rand -hex 32)
TOKENS="[\"${TOKEN_ID_1}\",\"${TOKEN_ID_2}\"]"
WEIGHTS="[${WEIGHT_1},${WEIGHT_2}]"
BALANCES="[${BALANCE_1},${BALANCE_2}]"

POOL_CONTRACT=$(stellar contract invoke \
    --id "$FACTORY_CONTRACT" \
    --source-account "$IDENTITY_STRING" \
    --network "$NETWORK" \
    -- \
    new_c_pool \
    --salt "$SALT" \
    --controller "$ADMIN_ADDRESS" \
    --tokens "$TOKENS" \
    --weights "$WEIGHTS" \
    --balances "$BALANCES" \
    --swap_fee "$SWAP_FEE")
POOL_CONTRACT=${POOL_CONTRACT//\"/}

echo "Factory contract: $FACTORY_CONTRACT"
echo "Pool contract: $POOL_CONTRACT"
echo "Pool WASM hash: $POOL_WASM_HASH"
echo "Tokens: $TOKEN_ID_1, $TOKEN_ID_2"
echo "Balances: $BALANCE_1, $BALANCE_2"
echo "Weights: $WEIGHT_1, $WEIGHT_2"
echo "Swap fee: $SWAP_FEE"
