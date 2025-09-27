let comet_address = env.as_contract(&deploy_helper_address.clone(), || {
let salt = BytesN::random(&env);

let mut controller_bytes = [0u8; 32];
controller.clone().to_xdr(&env).slice(8..).copy_into_slice(&mut controller_bytes);

let contract_id_preimage = ContractIdPreimage::Address(ContractIdPreimageFromAddress {
    address: ScAddress::Contract(ContractId(Hash(controller_bytes))),
    salt: Uint256(salt.to_array()),
});
let hash_id_preimage = HashIdPreimage::ContractId(HashIdPreimageContractId {
    network_id: env.ledger().network_id().to_array().try_into().unwrap(),
    contract_id_preimage,
});
let hash: [u8; 32] = Sha256::digest(&hash_id_preimage.to_xdr(Limits::none()).unwrap()).into();
let preimage = ScAddress::Contract(ContractId(hash.try_into().unwrap()));

let mut contract_bytes: Bytes = Bytes::new(&env);
contract_bytes.append(&controller.clone().to_xdr(&env).slice(..8));        
contract_bytes.extend_from_slice(preimage.to_xdr(Limits::none()).unwrap()[4..].try_into().unwrap());
let contract_id = Address::from_xdr(&env, &contract_bytes).unwrap();

let deployer = env
    .deployer()
    .with_current_contract(salt);
    // .with_address(controller.clone(), salt);
let contract_id = deployer.deployed_address();

env.set_auths(&[]);

contract_id.require_auth();
controller.require_auth();

println!("hmm1: {:?}", deploy_helper_address);
println!("hmm2: {:?}", Address::from_str(&env, "CAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAITA4").to_xdr(&env));

println!("controller: {:?}", controller);
println!("contract_id: {:?}", contract_id);

env
    .mock_auths(&[MockAuth {
        address: &controller,
        invoke: &MockAuthInvoke {
            contract: &contract_id,
            fn_name: &"__constructor",
            args: vec![
                &env,
                controller.into_val(&env),
                tokens.clone().into_val(&env),
                weights.clone().into_val(&env),
                balances.clone().into_val(&env),
                min_fee.into_val(&env),
                max_fee.into_val(&env),
                token_2_address.clone().into_val(&env),
                low_util_balance.into_val(&env),
                high_util_balance.into_val(&env),
            ],
            sub_invokes: &[
                MockAuthInvoke {
                    contract: &token_1_address,
                    fn_name: &"transfer",
                    args: vec![
                        &env,
                        controller.into_val(&env),
                        contract_id.into_val(&env),
                        STROOP.into_val(&env),
                    ],
                    sub_invokes: &[],
                },
                MockAuthInvoke {
                    contract: &token_2_address,
                    fn_name: &"transfer",
                    args: vec![
                        &env,
                        controller.into_val(&env),
                        contract_id.into_val(&env),
                        STROOP.into_val(&env),
                    ],
                    sub_invokes: &[],
                },
            ],
        },
    }]);

deployer
    .deploy_v2(
        wasm_hash,
        CometPoolContractArgs::__constructor(
            &controller,
            &tokens,
            &weights,
            &balances,
            &min_fee,
            &max_fee,
            &token_2_address,
            &low_util_balance,
            &high_util_balance,
        ),
    );
});

println!("auths: {:?}", env.auths());