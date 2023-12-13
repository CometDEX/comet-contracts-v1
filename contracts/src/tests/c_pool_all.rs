#![cfg(test)]

use std::dbg;
use std::println;
extern crate std;
use crate::c_consts::BONE;
use crate::c_consts::EXIT_FEE;
use crate::c_pool::comet::CometPoolContract;
use crate::c_pool::comet::CometPoolContractClient;
use sep_41_token::testutils::{MockTokenClient, MockTokenWASM};
use soroban_sdk::token;
use soroban_sdk::xdr::AccountId;
use soroban_sdk::Bytes;
use soroban_sdk::String;
use soroban_sdk::{testutils::Address as _, Address, IntoVal};
use soroban_sdk::{vec, BytesN, Env, Symbol};
use token::Client as TokenClient;

struct Clients {
    core: CometPoolContractClient<'static>,
    native_asset: token::Client<'static>,
    native_asset_admin: token::StellarAssetClient<'static>,
}

// fn create_token_contract<'a>(e: &'a Env, admin: &'a soroban_sdk::Address) -> AdminClient<'a> {
//     token::Client::new(&e, &e.register_stellar_asset_contract(admin.clone()));
//     token::AdminClient::new(&e, &admin)
// }

fn create_and_init_token_contract<'a>(
    env: &'a Env,
    admin_id: &'a Address,
    name: &'a str,
    symbol: &'a str,
) -> MockTokenClient<'a> {
    let token_id = env.register_contract_wasm(None, MockTokenWASM);
    let client = MockTokenClient::new(&env, &token_id);
    client.initialize(
        &admin_id,
        &7,
        &String::from_str(&env, name),
        &String::from_str(&env, symbol),
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
fn test_pool_functions_dep_wdr() {
    let env = Env::default();
    env.mock_all_auths();
    let admin = soroban_sdk::Address::generate(&env);
    let user1 = soroban_sdk::Address::generate(&env);
    let user2 = soroban_sdk::Address::generate(&env);
    let contract_id = env.register_contract(None, CometPoolContract);
    let client = CometPoolContractClient::new(&env, &contract_id);
    let factory = admin.clone();
    let controller_arg = factory.clone();
    client.init(&factory, &controller_arg);

    // // // Create Admin
    let mut admin1 = soroban_sdk::Address::generate(&env);

    // // // Create 4 tokens
    // let mut token1 = create_token_contract(&env, &admin1); // BAT token cannt be embedded inside Liquidity Pool
    // let mut token2 = create_token_contract(&env, &admin1);
    let mut token1 = create_and_init_token_contract(&env, &admin1, "SD", "SD");
    let mut token2 = create_and_init_token_contract(&env, &admin1, "Sample", "RD");

    let mut user1 = soroban_sdk::Address::generate(&env);
    let mut user2 = soroban_sdk::Address::generate(&env);
    token1.mint(&admin, &i128::MAX);
    token2.mint(&admin, &i128::MAX);

    token1.mint(&user1, &to_stroop(40000000));
    token1.mint(&user2, &to_stroop(40000000));
    token2.mint(&user1, &to_stroop(40000000));

    let controller = client.get_controller();
    assert_eq!(controller, admin);
    let num_tokens = client.get_tokens();
    assert_eq!(num_tokens.len(), 0);

    let contract_address = contract_id;
    env.budget().reset_unlimited();
    // token1.approve(&admin, &contract_address, &i128::MAX, &200);
    // token2.approve(&admin, &contract_address, &i128::MAX, &200);

    client.bind(&token1.address, &to_stroop(4), &to_stroop(12), &admin);
    client.bind(&token2.address, &to_stroop(10), &to_stroop(10), &admin);

    // client.bundle_bind(&vec![&env, token1.address.clone() ,token2.address.clone() ],
    //     &vec![&env, to_stroop(4), to_stroop(12)],
    //     &vec![&env, to_stroop(10), to_stroop(10)]
    // );

    client.set_swap_fee(&to_stroop(0.003), &controller);
    client.finalize();
    client.set_public_swap(&admin, &true);

    token1.approve(&user1, &contract_address, &i128::MAX, &200);
    token2.approve(&user1, &contract_address, &i128::MAX, &200);

    token1.approve(&user2, &contract_address, &i128::MAX, &200);
    token2.approve(&user2, &contract_address, &i128::MAX, &200);

    let pool_supply = client.get_total_supply();
    client.join_pool(&to_stroop(120), &vec![&env, i128::MAX, i128::MAX], &user1);
    assert_eq!(client.get_total_supply(), pool_supply + &to_stroop(120));

    client.exit_pool(&to_stroop(120), &vec![&env, 0, 0], &user1);
    assert_eq!(client.get_total_supply(), pool_supply);

    let total_shares_before_depositing = client.get_total_supply();
    println!("Total Shares before {}", total_shares_before_depositing);
    println!(
        "Total Token Balance before {}",
        client.get_balance(&token2.address)
    );
    println!(
        "Total Token 2 Balance before deposit {}",
        token2.balance(&user1)
    );
    let token_amount_in = client.dep_lp_tokn_amt_out_get_tokn_in(
        &token2.address,
        &to_stroop(0.003),
        &to_stroop(0.005),
        &user1,
    );
    assert_eq!(
        to_stroop(0.003),
        client.get_total_supply() - total_shares_before_depositing
    );

    let total_shares_before_withdrawing = client.get_total_supply();
    println!("Total Shares After {}", total_shares_before_withdrawing);
    println!("Total Amount In {}", token_amount_in);
    println!(
        "Total Token Balance {}",
        client.get_balance(&token2.address)
    );
    println!("Total LP Balance {}", client.balance(&user1));
    println!(
        "Total Token 2 Balance before withdraw {}",
        token2.balance(&user1)
    );

    let token_amount_out = client.wdr_tokn_amt_in_get_lp_tokns_out(
        &token2.address,
        &to_stroop(0.003),
        &to_stroop(0.0001),
        &user1,
    );

    let total_shares = client.get_total_supply();
    println!("Total Shares After {}", total_shares);
    println!("Total Amount In {}", token_amount_out);
    println!(
        "Total Token Balance {}",
        client.get_balance(&token2.address)
    );
    println!(
        "Total Token 2 Balance after withdraw {}",
        token2.balance(&user1)
    );
    assert_eq!(
        total_shares,
        total_shares_before_withdrawing - to_stroop(0.003)
    );

    let prev_token_balance = token1.balance(&user2);

    let pool_amount_out = client.dep_tokn_amt_in_get_lp_tokns_out(
        &token1.address,
        &to_stroop(0.001),
        &to_stroop(0.0001),
        &user2,
    );

    assert_eq!(
        to_stroop(0.001),
        prev_token_balance - token1.balance(&user2)
    );
    let prev_token_balance_before_withdrawing = token1.balance(&user2);

    println!(
        "Prev Token Balance {}",
        prev_token_balance_before_withdrawing
    );
    let pool_amount_in: i128 = client.wdr_tokn_amt_out_get_lp_tokns_in(
        &token1.address,
        &to_stroop(0.0009968),
        &to_stroop(0.1),
        &user2,
    );

    println!("Dust Amount {}", client.balance(&user2));
    println!("Token Balance {}", token1.balance(&user2));
    assert_eq!(
        token1.balance(&user2) - prev_token_balance_before_withdrawing,
        to_stroop(0.0009968)
    );
}
