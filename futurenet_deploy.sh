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

echo "Tokens initialized..."

# Upload the soroban_token_contract and capture its hash
CONTRACT_WASM_HASH=$(stellar contract upload \
    --wasm target/wasm32v1-none/optimized/comet.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

echo "Upload wasm code..."

# Deploy the Factory Contract
FACTORY_CONTRACT=$(stellar contract deploy \
    --wasm target/wasm32v1-none/optimized/comet_factory.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

echo "Deployed Factory Contract..."

# Initialize the factory contract
stellar contract invoke \
    --id $FACTORY_CONTRACT \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    init \
    --pool_wasm_hash $CONTRACT_WASM_HASH

echo "Factory Contract initialized..."
echo $FACTORY_CONTRACT

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
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------------------------"
echo "-----------------------------"

# build JSON vectors
TOKENS_JSON="[\"$TOKEN_ID1\",\"$TOKEN_ID2\"]"
WEIGHTS_JSON="[\"8000000\",\"2000000\"]"
BALANCES_JSON="[\"500000000\",\"500000000\"]"

# Create Pool
CONTRACT_ID=$(stellar --very-verbose contract invoke \
    --id $FACTORY_CONTRACT \
    --source $IDENTITY_STRING \
    --network futurenet --fee 10000000 \
    -- \
    new_c_pool \
    --salt $SALT \
    --controller $ADMIN_ADDRESS \
    --tokens "$TOKENS_JSON" \
    --weights "$WEIGHTS_JSON" \
    --balances "$BALANCES_JSON" \
    --swap_fee 30000)

# the CLI prints the returned value quoted – strip quotes
CONTRACT_ID_VAL=$(echo "$CONTRACT_ID" | tr -d '"')

echo "Created new pool: $CONTRACT_ID_VAL"

echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------SWAP POOL------------------"
echo "-----------------------------"
echo "-----------------------------"
echo "-----------------------------"
echo "-----------------------------"
echo "-----------------------------"
echo "-----------------------------"

# Swap Function
stellar --very-verbose contract invoke \
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
    --user $ADMIN_ADDRESS

echo "Swapped token 1 for token 2"

TOKEN_ID1_BALANCE=$(stellar contract invoke \
    --id $TOKEN_ID1 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    balance \
    --id $ADMIN_ADDRESS)

echo "Balance $TOKEN_ID1_BALANCE"