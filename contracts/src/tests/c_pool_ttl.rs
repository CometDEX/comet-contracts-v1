#![cfg(test)]

use crate::tests::utils::MockTokenClient;
use soroban_sdk::{
    testutils::{Address as _, Ledger},
    vec,
    xdr::{ContractDataDurability, LedgerKey, ScAddress, ScVal},
    Address, Env, IntoVal, TryFromVal, Val, Vec,
};

use crate::{
    c_consts::STROOP,
    c_pool::{
        comet::CometPoolContractClient,
        storage_types::{
            DataKey, DataKeyToken, DAY_IN_LEDGERS, POOL_BUMP_AMOUNT, POOL_LIFETIME_THRESHOLD,
        },
    },
    tests::utils::{create_comet_pool, create_stellar_token},
};

fn contract_key<K>(e: &Env, key: K) -> ScVal
where
    K: IntoVal<Env, Val>,
{
    ScVal::try_from_val(e, &key.into_val(e)).unwrap()
}

fn live_until(e: &Env, contract: &Address, key: ScVal) -> Option<u32> {
    let contract = ScAddress::try_from(contract).unwrap();
    let snapshot = e.to_ledger_snapshot();

    let live_until = snapshot
        .entries()
        .into_iter()
        .find_map(|(ledger_key, (_, live_until))| match ledger_key.as_ref() {
            LedgerKey::ContractData(data)
                if data.contract == contract
                    && data.key == key
                    && data.durability == ContractDataDurability::Persistent =>
            {
                *live_until
            }
            _ => None,
        });
    live_until
}

fn pool_ttls(e: &Env, pool: &Address, holder: &Address) -> [u32; 2] {
    [
        live_until(e, pool, ScVal::LedgerKeyContractInstance).unwrap(),
        live_until(
            e,
            pool,
            contract_key(e, DataKeyToken::Balance(holder.clone())),
        )
        .unwrap(),
    ]
}

#[test]
fn test_lp_balance_activity_extends_all_critical_pool_state() {
    let env = Env::default();
    env.mock_all_auths();
    env.cost_estimate().budget().reset_unlimited();

    let admin = Address::generate(&env);
    let token_1 = create_stellar_token(&env, &admin);
    let token_2 = create_stellar_token(&env, &admin);
    let token_1_client = MockTokenClient::new(&env, &token_1);
    let token_2_client = MockTokenClient::new(&env, &token_2);
    let balances: Vec<i128> = vec![&env, 100 * STROOP, 50 * STROOP];
    let weights: Vec<i128> = vec![&env, 5 * STROOP / 10, 5 * STROOP / 10];
    token_1_client.mint(&admin, &balances.get_unchecked(0));
    token_2_client.mint(&admin, &balances.get_unchecked(1));

    let pool = create_comet_pool(
        &env,
        &admin,
        &vec![&env, token_1, token_2],
        &weights,
        &balances,
        0_0030000,
    );
    let comet = CometPoolContractClient::new(&env, &pool);
    let initial_ttls = pool_ttls(&env, &pool, &admin);

    assert_eq!(
        live_until(&env, &pool, contract_key(&env, DataKey::AllTokenVec)),
        None
    );
    assert_eq!(
        live_until(&env, &pool, contract_key(&env, DataKey::AllRecordData)),
        None
    );
    assert_eq!(
        live_until(&env, &pool, contract_key(&env, DataKey::TotalShares)),
        None
    );
    assert!(initial_ttls.iter().all(|ttl| *ttl == initial_ttls[0]));
    assert_eq!(POOL_BUMP_AMOUNT, 120 * DAY_IN_LEDGERS);
    assert_eq!(POOL_LIFETIME_THRESHOLD, 100 * DAY_IN_LEDGERS);

    env.ledger()
        .with_mut(|ledger| ledger.sequence_number += 20 * DAY_IN_LEDGERS + 1);
    comet.balance(&admin);

    let extended_ttls = pool_ttls(&env, &pool, &admin);
    assert!(extended_ttls.iter().all(|ttl| *ttl == extended_ttls[0]));
    assert!(extended_ttls[0] > initial_ttls[0]);
}
