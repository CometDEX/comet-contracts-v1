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

# # Build and optimize the contracts
make build > /dev/null

# echo "Contracts optimized..."

# # Fetch the admin's address
ADMIN_ADDRESS=$(soroban config identity address $IDENTITY_STRING)

# Deploy the soroban_token_contract and capture its contract ID hash
TOKEN_ADDR1=$(soroban contract deploy \
    --wasm target/wasm32-unknown-unknown/release/soroban_token_contract.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

TOKEN_ADDR2=$(soroban contract deploy \
    --wasm target/wasm32-unknown-unknown/release/soroban_token_contract.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

# echo "Tokens deployed..."

# Sort the token addresses alphabetically
if [[ "$TOKEN_ADDR1" < "$TOKEN_ADDR2" ]]; then
    TOKEN_ID1=$TOKEN_ADDR1
    TOKEN_ID2=$TOKEN_ADDR2
else
    TOKEN_ID1=$TOKEN_ADDR2
    TOKEN_ID2=$TOKEN_ADDR1
fi

# Initialize the contracts
soroban contract invoke \
    --id $TOKEN_ID1 \
    --source $IDENTITY_STRING \
    --network futurenet\
    -- \
    initialize \
    --admin $ADMIN_ADDRESS \
    --decimal 7 \
    --name US_DOLLAR \
    --symbol USDC

soroban contract invoke \
    --id $TOKEN_ID2 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    initialize \
    --admin $ADMIN_ADDRESS \
    --decimal 7 \
    --name COMET \
    --symbol COM

# echo "Tokens initialized..."

# Install the soroban_token_contract and capture its hash
CONTRACT_WASM_HASH=$(soroban contract install \
    --wasm target/wasm32-unknown-unknown/optimized/comet.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

# echo "Upload wasm code..."

# Deploy the Factory Contract
FACTORY_CONTRACT=$(soroban contract deploy \
    --wasm target/wasm32-unknown-unknown/optimized/comet_factory.wasm \
    --source $IDENTITY_STRING \
    --network futurenet)

# echo "Deployed Factory Contract..."



# Initialize the factory contract
soroban contract invoke \
    --id $FACTORY_CONTRACT \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    init \
    --user $ADMIN_ADDRESS \
    --pool_wasm_hash $CONTRACT_WASM_HASH

# echo "Factory Contract initialized..."
# echo $FACTORY_CONTRACT
# Mint both tokens to the admin
soroban contract invoke \
    --id $TOKEN_ID1 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    mint --to $ADMIN_ADDRESS --amount 100000000000

soroban contract invoke \
    --id $TOKEN_ID2 \
    --source $IDENTITY_STRING \
    --network futurenet \
    -- \
    mint --to $ADMIN_ADDRESS --amount 100000000000

# echo "Minted tokens to the admin..."

SALT=$(openssl rand -hex 32)
# echo "Generated Salt (Hex): $SALT"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------CREATE POOL------------------"
echo "-----------------------------"
echo "-----------------------------"

# Create Pool
CONTRACT_ID=$(soroban --very-verbose contract invoke \
    --id $FACTORY_CONTRACT \
    --source $IDENTITY_STRING \
    --network futurenet --fee 10000000 \
    -- \
    new_c_pool \
    --salt $SALT \
    --user $ADMIN_ADDRESS)

# echo "Deployed Contract... $CONTRACT_ID"
# string='$CONTRACT_ID"'
# no_quotes=${string//\"/}
CONTRACT_ID_VAL=${CONTRACT_ID//\"/}

soroban contract invoke \
    --id $CONTRACT_ID_VAL \
    --source $IDENTITY_STRING \
    --network futurenet --fee 1000000000 \
    -- \
    bind \
    --token $TOKEN_ID1 \
    --balance 500000000 \
    --denorm 80000000 \
    --admin $ADMIN_ADDRESS

# echo "Attached first token"

soroban contract invoke \
    --id $CONTRACT_ID_VAL \
    --source $IDENTITY_STRING \
    --network futurenet --fee 1000000000 \
    -- \
    bind \
    --token $TOKEN_ID2 \
    --balance 500000000 \
    --denorm 20000000 \
    --admin $ADMIN_ADDRESS

# echo "Attached second token"

soroban contract invoke \
    --id $CONTRACT_ID_VAL \
    --source $IDENTITY_STRING \
    --network futurenet --fee 1000000000 \
    -- \
    finalize


# echo "Finalized the Pool i.e made it available for the public to use "

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
soroban --very-verbose contract invoke \
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

 
# # echo "Swapped token 1 for token 2"

# TOKEN_ID1_BALANCE=$(soroban contract invoke \
#     --id $TOKEN_ID1 \
#     --source $IDENTITY_STRING \
#     --network futurenet \
#     -- \
#     balance \
#     --id $ADMIN_ADDRESS)

# echo "Balance $TOKEN_ID1_BALANCE"