#![cfg(test)]

use std::println;
extern crate std;
use crate::c_consts::BONE;
use crate::c_pool::comet::CometPoolContract;
use crate::c_pool::comet::CometPoolContractClient;
use crate::c_pool::error::Error;
use soroban_sdk::token;
use soroban_sdk::xdr::AccountId;
use soroban_sdk::Bytes;
use soroban_sdk::String;
use soroban_sdk::{testutils::Address as _, Address, IntoVal};
use soroban_sdk::{vec, BytesN, Env, Symbol};
use token::Client as TokenClient;

mod test_token {
    soroban_sdk::contractimport!(
        file = "../target/wasm32-unknown-unknown/release/soroban_token_contract.wasm"
    );
}

fn create_token_contract<'a>(e: &Env, admin: &Address) -> TokenClient<'a> {
    TokenClient::new(e, &e.register_stellar_asset_contract(admin.clone()))
}

fn create_and_init_token_contract<'a>(
    env: &'a Env,
    admin_id: &'a Address,
    decimals: &'a u32,
    name: &'a str,
    symbol: &'a str,
) -> test_token::Client<'a> {
    let token_id = env.register_contract_wasm(None, test_token::WASM);
    let client = test_token::Client::new(&env, &token_id);
    client.initialize(
        &admin_id,
        decimals,
        &String::from_slice(&env, name),
        &String::from_slice(&env, symbol),
    );
    client
}

// fn install_token_wasm(e: &Env) -> BytesN<32> {
//     soroban_sdk::contractimport!(
//         file = "../target/wasm32-unknown-unknown/release/soroban_token_contract.wasm"
//     );
//     e.install_contract_wasm(WASM)
// }

fn to_stroop<T: Into<f64>>(a: T) -> i128 {
    (a.into() * 1e7) as i128
}

#[test]
fn test_pool_functions() {
    let env: Env = Env::default();
    env.mock_all_auths();
    let admin = soroban_sdk::Address::random(&env);
    let user1 = soroban_sdk::Address::random(&env);
    let user2 = soroban_sdk::Address::random(&env);
    let contract_id = env.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&env, &contract_id);
    let factory = admin.clone();
    let controller_arg = factory.clone();
    client.init(&factory, &controller_arg);
    env.budget().reset_unlimited();
    // Create Admin
    let mut admin1: Address = soroban_sdk::Address::random(&env);

    // // Create 4 tokens
    let mut token1 = create_and_init_token_contract(&env, &admin1, &7, "NebulaCoin", "NBC");
    let mut token2 = create_and_init_token_contract(&env, &admin1, &7, "QuantumToken", "QTK");
    let mut token3 = create_and_init_token_contract(&env, &admin1, &7, "SolariumCoin", "SLC");
    let mut token4 = create_and_init_token_contract(&env, &admin1, &7, "StellarBit", "XBT");

    // // Create 2 users
    let mut user1 = soroban_sdk::Address::random(&env);
    let mut user2 = soroban_sdk::Address::random(&env);

    token1.mint(&admin1, &to_stroop(50));
    token2.mint(&admin1, &to_stroop(20));
    token3.mint(&admin1, &to_stroop(10000));
    token4.mint(&admin1, &to_stroop(10));

    token1.mint(&admin, &to_stroop(50));
    token2.mint(&admin, &to_stroop(20));
    token3.mint(&admin, &to_stroop(10000));
    token4.mint(&admin, &to_stroop(10));

    token1.mint(&user1, &to_stroop(25));
    token2.mint(&user1, &to_stroop(4));
    token3.mint(&user1, &to_stroop(40000));
    token4.mint(&user1, &to_stroop(10));

    token1.mint(&user2, &to_stroop(12));
    token2.mint(&user2, &to_stroop(1));
    token3.mint(&user2, &to_stroop(40000));
    token4.mint(&user2, &to_stroop(51));

    let controller = client.get_controller();
    assert_eq!(controller, admin);
    let num_tokens = client.get_num_tokens();
    assert_eq!(num_tokens, 0);

    // // let contract_address: Address = Address::from_contract_id(&contract_id);
    // // token1.approve(&admin, &contract_id, &i128::MAX, &200);
    // // token2.approve(&admin, &contract_id, &i128::MAX, &200);
    // // token3.approve(&admin, &contract_id, &i128::MAX, &200);
    // // token4.approve(&admin, &contract_id, &i128::MAX, &200);

    client.bind(&token1.address, &to_stroop(50), &to_stroop(5), &admin);
    client.bind(&token2.address, &to_stroop(20), &to_stroop(5), &admin);
    client.bind(&token3.address, &to_stroop(10000), &to_stroop(5), &admin);
    client.bind(&token4.address, &to_stroop(10), &to_stroop(5), &admin);
    // client.bundle_bind(
    //     &vec![&env, token1.address.clone() ,token2.address.clone(), token3.address.clone(), token4.address.clone()],
    //     &vec![&env, to_stroop(50), to_stroop(20), to_stroop(10000), to_stroop(10)],
    //     &vec![&env, to_stroop(5), to_stroop(5), to_stroop(5), to_stroop(5)]
    // );
    client.unbind(&token4.address, &admin);

    let num_tokens = client.get_num_tokens();
    assert_eq!(3, num_tokens);
    let total_denormalized_weight = client.get_total_denormalized_weight();

    assert_eq!(to_stroop(15), total_denormalized_weight);
    let current_tokens = client.get_current_tokens();
    assert!(current_tokens.contains(&token1.address));
    assert!(current_tokens.contains(&token2.address));
    assert!(current_tokens.contains(&token3.address));
    assert_eq!(current_tokens.len(), 3);

    client.set_swap_fee(&to_stroop(0.003), &controller);
    let swap_fee = client.get_swap_fee();
    assert_eq!(swap_fee, to_stroop(0.003));
    client.finalize();
    let contract_share: Address = client.share_id();
    let token_share = token::Client::new(&env, &contract_share);
    assert_eq!(token_share.balance(&controller), 100 * BONE);

    token1.approve(&user1, &contract_id, &i128::MAX, &200);
    token2.approve(&user1, &contract_id, &i128::MAX, &200);
    token3.approve(&user1, &contract_id, &i128::MAX, &200);
    token4.approve(&user1, &contract_id, &i128::MAX, &200);

    token1.approve(&user2, &contract_id, &i128::MAX, &200);
    token2.approve(&user2, &contract_id, &i128::MAX, &200);
    token3.approve(&user2, &contract_id, &i128::MAX, &200);
    token4.approve(&user2, &contract_id, &i128::MAX, &200);

    client.join_pool(
        &to_stroop(5),
        &vec![&env, i128::MAX, i128::MAX, i128::MAX],
        &user1,
    );
    assert_eq!(105000010001, client.get_balance(&token3.address));
    assert_eq!(224999949, token1.balance(&user1));

    let token_1_price = client.get_spot_price_sans_fee(&token3.address, &token1.address);
    assert_eq!(token_1_price, to_stroop(200));
    let token_1_price_fee = client.get_spot_price(&token3.address, &token1.address);
    let token_1_price_fee_check_float = ((10500.0 / 5.0) / (52.5 / 5.0)) * (1.0 / (1.0 - 0.003));
    // 200.6018054162487462
    // 200.6018000
    // Actual value due to Soroban having only 7 decimal places for token amounts
    assert_eq!(token_1_price_fee, 2006018000);

    let tx = client.swap_exact_amount_in(
        &token1.address,
        &to_stroop(2.5),
        &token3.address,
        &to_stroop(475),
        &to_stroop(200),
        &user2,
    );

    let val = client.get_spot_price(&token3.address, &token1.address);
    // Using Floats 182.804672101083406128
    assert_eq!(val, 1828046606);

    let txr = client.swap_exact_amount_out(
        &token1.address,
        &to_stroop(3),
        &token2.address,
        &to_stroop(1.0),
        &to_stroop(500),
        &user2,
    );

    // // Using Floats
    // // 2.758274824473420261
    assert_eq!(txr.0, 27582695);

    client.set_freeze_status(&controller, &true);

    // fails as expected
    // client.join_pool(
    //     &to_stroop(5),
    //     &vec![&env, i128::MAX, i128::MAX, i128::MAX],
    //     &user2,
    // );

    client.exit_pool(&to_stroop(5), &vec![&env, 0, 0, 0], &user1);

    // Increases due to swap earlier
    println!("Token Balance of User1 = {}", token1.balance(&user1));

    client.set_freeze_status(&controller, &false);

    // It is unfreezed, so everything is working
    client.join_pool(
        &to_stroop(5),
        &vec![&env, i128::MAX, i128::MAX, i128::MAX],
        &user2,
    );

    // assert_eq!(
    //     client.try_set_swap_fee(&to_stroop(0.004), &controller),
    //     Err(Ok(Status::from_type_and_code(
    //         ScStatusType::ContractError,
    //         1,
    //     )))
    // );
    env.budget().reset_unlimited();

    println!(
        "Token Balance 1 of Contract = {}",
        token1.balance(&contract_id)
    );
    token1.mint(&contract_id, &to_stroop(100));
    client.gulp(&token1.address);

    // let logs = env.logger().all();
    // std::println!("{}", logs.join("\n"));
}
