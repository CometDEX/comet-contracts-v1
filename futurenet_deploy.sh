# Redirect stdout ( > ) and stderr ( 2> ) to a file
exec > script_output.log 2>&1

# Ensure the script exits on any errors
set -e

# Check if the argument is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <identity_string>"
    exit 1
fi

IDENTITY_STRING=$1

# Build and optimize the contracts
make build > /dev/null

echo "Contracts optimized..."

# Fetch the admin's address
ADMIN_ADDRESS=$(stellar keys address $IDENTITY_STRING)

# Deploy the soroban_token_contract and capture its contract ID hash
TOKEN_ADDR1=$(stellar contract deploy \
    --wasm ext/soroban_token_contract.wasm \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    --admin $ADMIN_ADDRESS \
    --decimal 7 \
    --name US_DOLLAR \
    --symbol USDC)

TOKEN_ADDR2=$(stellar contract deploy \
    --wasm ext/soroban_token_contract.wasm \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    --admin $ADMIN_ADDRESS \
    --decimal 7 \
    --name COMET \
    --symbol COM)

echo "Tokens deployed..."

# Sort the token addresses alphabetically
if [[ "$TOKEN_ADDR1" < "$TOKEN_ADDR2" ]]; then
    TOKEN_ID1=$TOKEN_ADDR1
    TOKEN_ID2=$TOKEN_ADDR2
else
    TOKEN_ID1=$TOKEN_ADDR2
    TOKEN_ID2=$TOKEN_ADDR1
fi

# Install the soroban_token_contract and capture its hash
CONTRACT_WASM_HASH=$(stellar contract upload \
    --wasm target/wasm32v1-none/optimized/comet.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

echo "Upload wasm code..."

# Mint both tokens to the admin
stellar contract invoke \
    --id $TOKEN_ID1 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    mint --to $ADMIN_ADDRESS --amount 100000000000

stellar contract invoke \
    --id $TOKEN_ID2 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    mint --to $ADMIN_ADDRESS --amount 100000000000

echo "Minted tokens to the admin..."

SALT=$(openssl rand -hex 32)
echo "Generated Salt (Hex): $SALT"
echo "-----------------------------"
echo "-----------------------------"
echo "-----------CREATE POOL------------------"
echo "-----------------------------"
echo "-----------------------------"

# build JSON vectors
TOKENS_JSON="[\"$TOKEN_ID1\",\"$TOKEN_ID2\"]"
WEIGHTS_JSON="[\"8000000\",\"2000000\"]"
BALANCES_JSON="[\"500000000\",\"500000000\"]"
MIN_FEE=30000
MAX_FEE=30000
LOW_UTIL_BALANCE=500000000
HIGH_UTIL_BALANCE=600000000

# Create Pool
CONTRACT_ID=$(stellar contract deploy \
    --wasm target/wasm32v1-none/optimized/comet.wasm \
    --source $IDENTITY_STRING \
    --network futurenet --fee 10000000 \
    -- \
    --controller $ADMIN_ADDRESS \
    --tokens "$TOKENS_JSON" \
    --weights "$WEIGHTS_JSON" \
    --balances "$BALANCES_JSON" \
    --min_fee $MIN_FEE \
    --max_fee $MAX_FEE \
    --tracked_token $TOKEN_ID2 \
    --low_util_balance $LOW_UTIL_BALANCE \
    --high_util_balance $HIGH_UTIL_BALANCE)

# the CLI prints the returned value quoted – strip quotes
CONTRACT_ID_VAL=$(echo "$CONTRACT_ID" | tr -d '"')

echo "Created new pool: $CONTRACT_ID_VAL"

echo "-----------------------------"
echo "-----------------------------"
echo "-----------SWAP POOL------------------"
echo "-----------------------------"
echo "-----------------------------"

# Swap Function
stellar contract invoke \
    --id $CONTRACT_ID_VAL \
    --source $IDENTITY_STRING \
    --network futurenet --fee 1000000000 \
    -- \
    swap_exact_amount_in \
    --token_in $TOKEN_ID1 \
    --token_amount_in 10000000 \
    --token_out $TOKEN_ID2 \
    --min_amount_out 0 \
    --max_price 10000000000000 \
    --user $ADMIN_ADDRESS \
    --trade_recipients null

echo "Swapped token 1 for token 2"

TOKEN_ID1_BALANCE=$(stellar contract invoke \
    --id $TOKEN_ID1 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    balance \
    --id $ADMIN_ADDRESS)

echo "Balance $TOKEN_ID1_BALANCE"
