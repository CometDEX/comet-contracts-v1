//! Fee distribution logic for swap micro-fees.

use soroban_fixed_point_math::FixedPoint;
use soroban_sdk::{
    assert_with_error, panic_with_error, unwrap::UnwrapOptimized, Address, Env, Map, Vec,
};

use crate::c_consts::{MAX_FEE_RECIPIENTS, STROOP};
use crate::c_pool::error::Error;
use crate::c_pool::metadata::{
    clear_fee_rule as metadata_clear_fee_rule, read_fee_rule, read_swap_fee_config, read_tokens,
    write_fee_rule,
};
use crate::c_pool::storage_types::{FeeRecipient, FeeRule, Record};
use soroban_sdk::token::Client as TokenClient;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SwapLeg {
    In,
    Out,
}

pub fn validate_fee_rule(e: &Env, rule: &FeeRule, tokens: &Vec<Address>) {
    assert_with_error!(
        &e,
        !rule.recipients.is_empty(),
        Error::ErrInvalidFeeRecipient
    );
    assert_with_error!(
        &e,
        rule.recipients.len() as u32 <= MAX_FEE_RECIPIENTS,
        Error::ErrFeeRecipientCapExceeded
    );

    let mut sum: i128 = 0;
    let mut seen = Map::<Address, bool>::new(&e);
    let self_address = e.current_contract_address();

    let mut found_fee_asset = false;
    for i in 0..tokens.len() {
        let token = tokens.get(i).unwrap_optimized();
        if token == rule.fee_asset {
            found_fee_asset = true;
            break;
        }
    }
    assert_with_error!(&e, found_fee_asset, Error::ErrFeeAssetNotBound);

    for idx in 0..rule.recipients.len() {
        let recipient = rule.recipients.get(idx).unwrap_optimized();
        assert_with_error!(&e, recipient.percent > 0, Error::ErrFeeRecipientPercent);
        sum = sum.checked_add(recipient.percent).unwrap_optimized();
        assert_with_error!(
            &e,
            recipient.recipient != self_address,
            Error::ErrInvalidFeeRecipient
        );
        assert_with_error!(
            &e,
            !seen.contains_key(recipient.recipient.clone()),
            Error::ErrFeeRecipientDuplicate
        );
        seen.set(recipient.recipient.clone(), true);
    }

    assert_with_error!(&e, sum > 0, Error::ErrFeeRecipientSum);
    assert_with_error!(&e, sum <= STROOP, Error::ErrFeeRecipientSum);
}

pub fn validate_fee_recipients(e: &Env, recipients: &Vec<FeeRecipient>) {
    assert_with_error!(
        &e,
        recipients.len() as u32 <= MAX_FEE_RECIPIENTS,
        Error::ErrFeeRecipientCapExceeded
    );

    let mut sum: i128 = 0;
    let mut seen = Map::<Address, bool>::new(&e);
    let self_address = e.current_contract_address();

    for idx in 0..recipients.len() {
        let recipient = recipients.get(idx).unwrap_optimized();
        assert_with_error!(&e, recipient.percent > 0, Error::ErrFeeRecipientPercent);
        sum = sum.checked_add(recipient.percent).unwrap_optimized();
        assert_with_error!(
            &e,
            recipient.recipient != self_address,
            Error::ErrInvalidFeeRecipient
        );
        assert_with_error!(
            &e,
            !seen.contains_key(recipient.recipient.clone()),
            Error::ErrFeeRecipientDuplicate
        );
        seen.set(recipient.recipient.clone(), true);
    }

    assert_with_error!(&e, sum <= STROOP, Error::ErrFeeRecipientSum);
}

fn compute_min_fee_amount(min_fee_percent: i128, leg_amount: i128) -> i128 {
    min_fee_percent
        .fixed_mul_floor(leg_amount, STROOP)
        .unwrap_optimized()
}

fn read_min_fee_percent(e: &Env) -> i128 {
    read_swap_fee_config(e).min_fee
}

fn iter_recipients<'a>(
    e: &'a Env,
    pool: &'a Vec<FeeRecipient>,
    trade: Option<&'a Vec<FeeRecipient>>,
) -> Vec<FeeRecipient> {
    let mut ordered = Vec::new(e);
    for idx in 0..pool.len() {
        ordered.push_back(pool.get(idx).unwrap_optimized());
    }
    if let Some(extra) = trade {
        for idx in 0..extra.len() {
            ordered.push_back(extra.get(idx).unwrap_optimized());
        }
    }
    ordered
}

fn compute_payouts(
    e: &Env,
    fee_total: i128,
    ordered_recipients: &Vec<FeeRecipient>,
) -> Vec<(Address, i128)> {
    let mut remaining = fee_total;
    let mut payouts = Vec::new(e);

    for idx in 0..ordered_recipients.len() {
        if remaining <= 0 {
            break;
        }
        let recipient = ordered_recipients.get(idx).unwrap_optimized();
        let desired = recipient
            .percent
            .fixed_mul_floor(fee_total, STROOP)
            .unwrap_optimized();
        let payout = desired.min(remaining);
        if payout > 0 {
            payouts.push_back((recipient.recipient.clone(), payout));
            remaining -= payout;
        }
    }

    payouts
}

fn adjust_pool_balance(
    e: &Env,
    record_map: &mut Map<Address, Record>,
    fee_asset: &Address,
    amount: i128,
) {
    if amount <= 0 {
        return;
    }

    let mut record = record_map
        .get(fee_asset.clone())
        .unwrap_or_else(|| panic_with_error!(e, Error::ErrFeeRuleUnsupportedToken));
    assert_with_error!(e, record.balance >= amount, Error::ErrFeeDistribution);
    record.balance -= amount;
    record_map.set(fee_asset.clone(), record);
}

fn refund_pool_balance(record_map: &mut Map<Address, Record>, fee_asset: &Address, amount: i128) {
    if amount <= 0 {
        return;
    }

    let mut record = record_map.get(fee_asset.clone()).unwrap_optimized();
    record.balance = record.balance.checked_add(amount).unwrap_optimized();
    record_map.set(fee_asset.clone(), record);
}

fn sum_payouts(e: &Env, payouts: &Vec<(Address, i128)>) -> i128 {
    let mut total: i128 = 0;
    for idx in 0..payouts.len() {
        let (_, amount) = payouts.get(idx).unwrap_optimized();
        total = total.checked_add(amount).unwrap_optimized();
    }
    assert_with_error!(e, total >= 0, Error::ErrFeeDistribution);
    total
}

pub fn apply_fee_distribution(
    e: &Env,
    record_map: &mut Map<Address, Record>,
    _leg: SwapLeg,
    leg_amount: i128,
    rule: &FeeRule,
    trade_recipients: Option<&Vec<FeeRecipient>>,
) -> Option<Vec<(Address, i128)>> {
    if leg_amount <= 0 {
        return None;
    }

    let min_fee_percent = read_min_fee_percent(e);
    if min_fee_percent <= 0 {
        return None;
    }

    let fee_total = compute_min_fee_amount(min_fee_percent, leg_amount);
    if fee_total <= 0 {
        return None;
    }

    let recipients = iter_recipients(e, &rule.recipients, trade_recipients);
    if recipients.is_empty() {
        return None;
    }

    let payouts = compute_payouts(e, fee_total, &recipients);
    if payouts.is_empty() {
        return None;
    }

    let allocated = sum_payouts(e, &payouts);
    if allocated <= 0 {
        return None;
    }

    adjust_pool_balance(e, record_map, &rule.fee_asset, allocated);

    let token_client = TokenClient::new(e, &rule.fee_asset);
    let mut executed = Vec::new(e);
    let mut sent_total: i128 = 0;
    for idx in 0..payouts.len() {
        let (recipient, amount) = payouts.get(idx).unwrap_optimized();
        if amount <= 0 {
            continue;
        }
        if token_client
            .try_transfer(&e.current_contract_address(), &recipient, &amount)
            .is_ok()
        {
            sent_total = sent_total.checked_add(amount).unwrap_optimized();
            executed.push_back((recipient, amount));
        }
    }

    if sent_total < allocated {
        refund_pool_balance(record_map, &rule.fee_asset, allocated - sent_total);
    }

    if executed.is_empty() {
        return None;
    }

    Some(executed)
}

pub fn execute_replace_fee_rule(e: &Env, rule: FeeRule) {
    let tokens = read_tokens(e);
    validate_fee_rule(e, &rule, &tokens);
    write_fee_rule(e, &rule);
}

pub fn execute_clear_fee_rule(e: &Env) {
    metadata_clear_fee_rule(e);
}

pub fn execute_get_fee_rule(e: &Env) -> Option<FeeRule> {
    read_fee_rule(e)
}
