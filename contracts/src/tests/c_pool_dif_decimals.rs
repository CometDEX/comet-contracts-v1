#![cfg(test)]

use std::println;
extern crate std;
use crate::c_pool::comet::CometPoolContractClient;
use crate::tests::utils::create_comet_pool;
use sep_41_token::testutils::{MockTokenClient, MockTokenWASM};
use soroban_sdk::String;
use soroban_sdk::{testutils::Address as _, Address};
use soroban_sdk::{vec, Env};

fn create_and_init_token_contract<'a>(
    env: &'a Env,
    admin_id: &'a Address,
    decimals: &'a u32,
    name: &'a str,
    symbol: &'a str,
) -> MockTokenClient<'a> {
    let token_id = env.register_contract_wasm(None, MockTokenWASM);
    let client = MockTokenClient::new(&env, &token_id);
    client.initialize(
        &admin_id,
        decimals,
        &String::from_str(&env, name),
        &String::from_str(&env, symbol),
    );
    client
}

fn to_stroop<T: Into<f64>>(a: T) -> i128 {
    (a.into() * 1e7) as i128
}
fn to_six_dec<T: Into<f64>>(a: T) -> i128 {
    (a.into() * 1e6) as i128
}

#[test]
fn test_pool_functions_different_decimals() {
    let env: Env = Env::default();
    env.mock_all_auths();
    let admin = soroban_sdk::Address::generate(&env);

    env.budget().reset_unlimited();

    // Create Admin
    let admin1 = soroban_sdk::Address::generate(&env);

    // Create 4 tokens
    let token1: MockTokenClient<'_> =
        create_and_init_token_contract(&env, &admin1, &5, "NebulaCoin", "NBC");
    let token2: MockTokenClient<'_> =
        create_and_init_token_contract(&env, &admin1, &7, "StroopCoin", "STRP");

    // Create 2 users
    let user1 = soroban_sdk::Address::generate(&env);
    let user2 = soroban_sdk::Address::generate(&env);

    token1.mint(&admin1, &to_six_dec(50));
    token2.mint(&admin1, &to_stroop(20));

    token1.mint(&admin, &to_six_dec(50));
    token2.mint(&admin, &to_stroop(20));

    println!("Token Balance of User1 before = {}", token2.balance(&user1));
    token1.mint(&user1, &to_six_dec(25));
    token2.mint(&user1, &to_stroop(4));
    println!(
        "Token Balance of User1 After minting = {}",
        token2.balance(&user1)
    );

    token1.mint(&user2, &to_six_dec(12));
    token2.mint(&user2, &to_stroop(5));

    let tokens = vec![&env, token1.address.clone(), token2.address.clone()];
    let weights = vec![&env, 5000000, 5000000];
    let balances = vec![&env, to_six_dec(50), to_stroop(20)];
    let contract_id =
        create_comet_pool(&env, &admin, &tokens, &weights, &balances, to_stroop(0.003));
    let client = CometPoolContractClient::new(&env, &contract_id);

    token1.approve(&user1, &contract_id, &i128::MAX, &200);
    token2.approve(&user1, &contract_id, &i128::MAX, &200);

    token1.approve(&user2, &contract_id, &i128::MAX, &200);
    token2.approve(&user2, &contract_id, &i128::MAX, &200);

    println!("Token Balance of User1 before = {}", token1.balance(&user2));

    env.budget().reset_unlimited();

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user2);

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user1);

    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user1);

    env.budget().reset_unlimited();

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user1);
    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user1);

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user1);
    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user1);
    env.budget().reset_unlimited();

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user1);

    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user1);

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user1);
    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user1);

    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user2);

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user2);

    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user2);

    env.budget().reset_unlimited();

    client.join_pool(&to_stroop(10), &vec![&env, i128::MAX, i128::MAX], &user2);

    client.exit_pool(&to_stroop(10), &vec![&env, 0, 0], &user2);

    // The balances prove that there is no problem when a user continuously
    // joins and exits pool to gain surplus amounts due to rounding errors.
    println!("Token Balance of User2 Final = {}", token2.balance(&user2));
    println!("Token Balance of User1 Final = {}", token2.balance(&user1));

    assert_eq!(client.balance(&user2), 0);
    assert_eq!(client.balance(&user1), 0);
}
