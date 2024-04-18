#![cfg(test)]

use std::dbg;
use std::println;
extern crate std;
use crate::c_pool::comet::CometPoolContract;
use crate::c_pool::comet::CometPoolContractClient;
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
    let contract_id = env.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&env, &contract_id);
    let factory = admin.clone();
    let controller_arg = factory.clone();
    client.init(&factory, &controller_arg);
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

    let controller = client.get_controller();
    assert_eq!(controller, admin);
    let num_tokens = client.get_tokens();
    assert_eq!(num_tokens.len(), 0);

    let contract_address = contract_id;
    // token1.approve(&admin, &contract_address, &i128::MAX, &200);
    // token2.approve(&admin, &contract_address, &i128::MAX, &200);

    // client.bind(&token1.address, &to_six_dec(50), &to_stroop(5), &admin);
    // client.bind(&token2.address, &to_stroop(20), &to_stroop(5), &admin);

    client.bundle_bind(
        &vec![&env, token1.address.clone(), token2.address.clone()],
        &vec![&env, to_six_dec(50), to_stroop(20)],
        &vec![&env, to_stroop(5), to_stroop(5)],
    );

    dbg!("Checking the Authorization for Bundle Bindc");
    dbg!(env.auths());

    client.set_swap_fee(&to_stroop(0.003), &controller);
    let swap_fee = client.get_swap_fee();
    assert_eq!(swap_fee, to_stroop(0.003));
    client.finalize();

    token1.approve(&user1, &contract_address, &i128::MAX, &200);
    token2.approve(&user1, &contract_address, &i128::MAX, &200);

    token1.approve(&user2, &contract_address, &i128::MAX, &200);
    token2.approve(&user2, &contract_address, &i128::MAX, &200);

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
