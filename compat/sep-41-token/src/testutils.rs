use soroban_sdk::{
    contract, contracterror, contractevent, contractimpl, contracttype, panic_with_error, Address,
    Env, String,
};

const INSTANCE_BUMP: u32 = 31 * 17_280;
const INSTANCE_THRESHOLD: u32 = INSTANCE_BUMP - 17_280;

#[contracterror]
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TokenError {
    InternalError = 1,
    OperationNotSupportedError = 2,
    AlreadyInitializedError = 3,
    UnauthorizedError = 4,
    NegativeAmountError = 8,
    AllowanceError = 9,
    BalanceError = 10,
    OverflowError = 12,
}

#[derive(Clone)]
#[contracttype]
struct TokenMetadata {
    decimals: u32,
    name: String,
    symbol: String,
}

#[derive(Clone)]
#[contracttype]
struct AllowanceKey {
    from: Address,
    spender: Address,
}

#[derive(Clone)]
#[contracttype]
struct Allowance {
    amount: i128,
    live_until_ledger: u32,
}

#[derive(Clone)]
#[contracttype]
enum DataKey {
    Admin,
    Metadata,
    Allowance(AllowanceKey),
    Authorized(Address),
    Balance(Address),
}

#[contractevent(topics = ["mint"], data_format = "single-value")]
struct MintEvent {
    #[topic]
    admin: Address,
    #[topic]
    to: Address,
    amount: i128,
}

#[contractevent(topics = ["approve"], data_format = "vec")]
struct ApproveEvent {
    #[topic]
    from: Address,
    #[topic]
    spender: Address,
    amount: i128,
    live_until_ledger: u32,
}

#[contractevent(topics = ["transfer"], data_format = "single-value")]
struct TransferEvent {
    #[topic]
    from: Address,
    #[topic]
    to: Address,
    amount: i128,
}

#[contractevent(topics = ["burn"], data_format = "single-value")]
struct BurnEvent {
    #[topic]
    from: Address,
    amount: i128,
}

#[contract]
pub struct MockToken;

#[contractimpl]
impl MockToken {
    pub fn initialize(env: Env, admin: Address, decimals: u32, name: String, symbol: String) {
        if env.storage().instance().has(&DataKey::Admin) {
            panic_with_error!(&env, TokenError::AlreadyInitializedError);
        }
        if decimals > 27 {
            panic_with_error!(&env, TokenError::OperationNotSupportedError);
        }
        env.storage().instance().set(&DataKey::Admin, &admin);
        env.storage().instance().set(
            &DataKey::Metadata,
            &TokenMetadata {
                decimals,
                name,
                symbol,
            },
        );
    }

    pub fn mint(env: Env, to: Address, amount: i128) {
        require_nonnegative(&env, amount);
        let admin: Address = env.storage().instance().get(&DataKey::Admin).unwrap();
        admin.require_auth();
        extend_instance(&env);
        receive_balance(&env, &to, amount);
        MintEvent { admin, to, amount }.publish(&env);
    }

    pub fn set_admin(env: Env, new_admin: Address) {
        let admin: Address = env.storage().instance().get(&DataKey::Admin).unwrap();
        admin.require_auth();
        extend_instance(&env);
        env.storage().instance().set(&DataKey::Admin, &new_admin);
    }

    pub fn allowance(env: Env, from: Address, spender: Address) -> i128 {
        get_allowance(&env, &from, &spender).amount
    }

    pub fn approve(
        env: Env,
        from: Address,
        spender: Address,
        amount: i128,
        live_until_ledger: u32,
    ) {
        from.require_auth();
        require_nonnegative(&env, amount);
        if amount > 0 && live_until_ledger < env.ledger().sequence() {
            panic_with_error!(&env, TokenError::AllowanceError);
        }
        extend_instance(&env);
        set_allowance(&env, &from, &spender, amount, live_until_ledger);
        ApproveEvent {
            from,
            spender,
            amount,
            live_until_ledger,
        }
        .publish(&env);
    }

    pub fn balance(env: Env, id: Address) -> i128 {
        extend_instance(&env);
        get_balance(&env, &id)
    }

    pub fn authorized(env: Env, id: Address) -> bool {
        env.storage()
            .persistent()
            .get(&DataKey::Authorized(id))
            .unwrap_or(true)
    }

    pub fn set_authorized(env: Env, id: Address, authorize: bool) {
        let admin: Address = env.storage().instance().get(&DataKey::Admin).unwrap();
        admin.require_auth();
        extend_instance(&env);
        env.storage()
            .persistent()
            .set(&DataKey::Authorized(id), &authorize);
    }

    pub fn transfer(env: Env, from: Address, to: Address, amount: i128) {
        from.require_auth();
        require_nonnegative(&env, amount);
        extend_instance(&env);
        spend_balance(&env, &from, amount);
        receive_balance(&env, &to, amount);
        TransferEvent { from, to, amount }.publish(&env);
    }

    pub fn transfer_from(env: Env, spender: Address, from: Address, to: Address, amount: i128) {
        spender.require_auth();
        require_nonnegative(&env, amount);
        extend_instance(&env);
        spend_allowance(&env, &from, &spender, amount);
        spend_balance(&env, &from, amount);
        receive_balance(&env, &to, amount);
        TransferEvent { from, to, amount }.publish(&env);
    }

    pub fn burn(env: Env, from: Address, amount: i128) {
        from.require_auth();
        require_nonnegative(&env, amount);
        extend_instance(&env);
        spend_balance(&env, &from, amount);
        BurnEvent { from, amount }.publish(&env);
    }

    pub fn burn_from(env: Env, spender: Address, from: Address, amount: i128) {
        spender.require_auth();
        require_nonnegative(&env, amount);
        extend_instance(&env);
        spend_allowance(&env, &from, &spender, amount);
        spend_balance(&env, &from, amount);
        BurnEvent { from, amount }.publish(&env);
    }

    pub fn decimals(env: Env) -> u32 {
        metadata(&env).decimals
    }

    pub fn name(env: Env) -> String {
        metadata(&env).name
    }

    pub fn symbol(env: Env) -> String {
        metadata(&env).symbol
    }
}

fn extend_instance(env: &Env) {
    env.storage()
        .instance()
        .extend_ttl(INSTANCE_THRESHOLD, INSTANCE_BUMP);
}

fn require_nonnegative(env: &Env, amount: i128) {
    if amount < 0 {
        panic_with_error!(env, TokenError::NegativeAmountError);
    }
}

fn metadata(env: &Env) -> TokenMetadata {
    env.storage().instance().get(&DataKey::Metadata).unwrap()
}

fn get_balance(env: &Env, address: &Address) -> i128 {
    env.storage()
        .persistent()
        .get(&DataKey::Balance(address.clone()))
        .unwrap_or(0)
}

fn set_balance(env: &Env, address: &Address, balance: i128) {
    env.storage()
        .persistent()
        .set(&DataKey::Balance(address.clone()), &balance);
}

fn require_authorized(env: &Env, address: &Address) {
    if !MockToken::authorized(env.clone(), address.clone()) {
        panic_with_error!(env, TokenError::UnauthorizedError);
    }
}

fn receive_balance(env: &Env, address: &Address, amount: i128) {
    require_authorized(env, address);
    let balance = get_balance(env, address)
        .checked_add(amount)
        .unwrap_or_else(|| panic_with_error!(env, TokenError::OverflowError));
    set_balance(env, address, balance);
}

fn spend_balance(env: &Env, address: &Address, amount: i128) {
    require_authorized(env, address);
    let balance = get_balance(env, address);
    if balance < amount {
        panic_with_error!(env, TokenError::BalanceError);
    }
    set_balance(env, address, balance - amount);
}

fn get_allowance(env: &Env, from: &Address, spender: &Address) -> Allowance {
    env.storage()
        .temporary()
        .get(&DataKey::Allowance(AllowanceKey {
            from: from.clone(),
            spender: spender.clone(),
        }))
        .unwrap_or(Allowance {
            amount: 0,
            live_until_ledger: 0,
        })
}

fn set_allowance(
    env: &Env,
    from: &Address,
    spender: &Address,
    amount: i128,
    live_until_ledger: u32,
) {
    let key = DataKey::Allowance(AllowanceKey {
        from: from.clone(),
        spender: spender.clone(),
    });
    env.storage().temporary().set(
        &key,
        &Allowance {
            amount,
            live_until_ledger,
        },
    );
    if amount > 0 {
        let ttl = live_until_ledger
            .checked_sub(env.ledger().sequence())
            .unwrap_or_else(|| panic_with_error!(env, TokenError::AllowanceError));
        env.storage().temporary().extend_ttl(&key, ttl, ttl);
    }
}

fn spend_allowance(env: &Env, from: &Address, spender: &Address, amount: i128) {
    let allowance = get_allowance(env, from, spender);
    if allowance.amount < amount || env.ledger().sequence() > allowance.live_until_ledger {
        panic_with_error!(env, TokenError::AllowanceError);
    }
    if amount > 0 {
        set_allowance(
            env,
            from,
            spender,
            allowance.amount - amount,
            allowance.live_until_ledger,
        );
    }
}
