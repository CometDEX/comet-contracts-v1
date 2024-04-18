// Helpers to calculate outputs from a balancer pool
#![cfg(test)]
extern crate std;

use std::f64;
use std::vec::Vec;

/// Basic impl of a f64 Balancer Pool.
/// Does not account for protections like max in, max out, etc.
#[derive(Clone, PartialEq, Debug)]
pub struct BalancerPool {
    pub count: usize,
    pub balances: Vec<f64>,
    pub weights: Vec<f64>,
    pub supply: f64,
    pub swap_fee: f64,
}

impl BalancerPool {
    pub fn new(init_balances: Vec<f64>, weights: Vec<f64>, swap_fee: f64) -> Self {
        let count = init_balances.len();
        if init_balances.iter().any(|bal| bal <= &0.0) {
            panic!("init_balances must be positive");
        }
        if count != weights.len() {
            panic!("init_tokens and weights must have the same length");
        }
        BalancerPool {
            count,
            balances: init_balances,
            weights,
            supply: 100.0,
            swap_fee,
        }
    }

    #[allow(dead_code)]
    pub fn print(&self) {
        std::println!("BalancerPool: ");
        std::println!("  balances: {:?}", self.balances);
        std::println!("  supply: {}", self.supply);
    }

    pub fn spot_price(&self, token_in: usize, token_out: usize) -> f64 {
        let numer = self.balances[token_in] / self.weights[token_in];
        let denom = self.balances[token_out] / self.weights[token_out];
        numer / denom
    }

    /// Swap token in for token out given a fixed input amount `amount`
    ///
    /// Returns the number of tokens out
    pub fn swap_out_given_in(&mut self, token_in: usize, token_out: usize, amount: f64) -> f64 {
        let amount_net_fees = amount * (1.0 - self.swap_fee);
        let ratio = self.balances[token_in] / (self.balances[token_in] + amount_net_fees);
        let weighted_ratio = ratio.powf(self.weights[token_in] / self.weights[token_out]);

        let out = self.balances[token_out] * (1.0 - weighted_ratio);

        self.balances[token_in] += amount;
        self.balances[token_out] -= out;
        out
    }

    /// Swap token in for token out given a fixed output amount `amount`
    ///
    /// Returns the number of tokens in
    pub fn swap_in_given_out(&mut self, token_in: usize, token_out: usize, amount: f64) -> f64 {
        let ratio = self.balances[token_out] / (self.balances[token_out] - amount);
        let weighted_ratio = ratio.powf(self.weights[token_out] / self.weights[token_in]);
        let amount_in_net_fees = self.balances[token_in] * (weighted_ratio - 1.0);

        let amount_in = amount_in_net_fees / (1.0 - self.swap_fee);

        self.balances[token_in] += amount_in;
        self.balances[token_out] -= amount;
        amount_in
    }

    /// Join pool with `to_mint` tokens
    ///
    /// Returns the amount of each token that was added to the pool
    pub fn join_pool(&mut self, to_mint: f64) -> Vec<f64> {
        let ratio = (self.supply + to_mint) / self.supply - 1.0;
        let mut vec_in: Vec<f64> = Vec::new();
        for i in 0..self.balances.len() {
            let amount_in = self.balances[i] * ratio;
            vec_in.push(amount_in);
            self.balances[i] += amount_in;
        }
        self.supply += to_mint;
        vec_in
    }

    /// Exit pool with `to_burn` tokens
    ///
    /// Returns the amount of each token that was removed from the pool
    pub fn exit_pool(&mut self, to_burn: f64) -> Vec<f64> {
        let ratio = 1.0 - (self.supply - to_burn) / self.supply;
        let mut vec_out: Vec<f64> = Vec::new();
        for i in 0..self.balances.len() {
            let amount_out = self.balances[i] * ratio;
            vec_out.push(amount_out);
            self.balances[i] -= amount_out;
        }
        self.supply -= to_burn;
        vec_out
    }

    /// Add liquidity to the pool with `amount` of `token`
    ///
    /// Returns the amount of LP tokens minted
    pub fn single_sided_dep_given_in(&mut self, token: usize, amount: f64) -> f64 {
        let weighted_fee = (1.0 - self.weights[token]) * self.swap_fee;
        let amount_net_fees = amount * (1.0 - weighted_fee);

        let ratio = 1.0 + amount_net_fees / self.balances[token];
        let weighted_ratio = ratio.powf(self.weights[token]) - 1.0;
        let issued = self.supply * weighted_ratio;

        self.balances[token] += amount;
        self.supply += issued;
        issued
    }

    /// Add liquidity to the pool with `amount` of pool shares minted
    ///
    /// Returns the amount of tokens deposited
    pub fn single_sided_dep_given_out(&mut self, token: usize, amount: f64) -> f64 {
        let ratio = 1.0 + amount / self.supply;
        let weighted_ratio = ratio.powf(1.0 / self.weights[token]) - 1.0;
        let amount_in_net_fees = self.balances[token] * weighted_ratio;

        let weighted_fee = (1.0 - self.weights[token]) * self.swap_fee;
        let amount_in = amount_in_net_fees / (1.0 - weighted_fee);

        self.balances[token] += amount_in;
        self.supply += amount;
        amount_in
    }

    /// Withdrawn liquditiy from the pool with `amount` of pool shares
    ///
    /// Returns the amount of `token` withdrawn
    pub fn single_sided_wd_given_in(&mut self, token: usize, amount: f64) -> f64 {
        let ratio = 1.0 - amount / self.supply;
        let weighted_ratio = 1.0 - ratio.powf(1.0 / self.weights[token]);

        let withdrawn_with_fee = self.balances[token] * weighted_ratio;
        let weighted_fee = 1.0 - (1.0 - self.weights[token]) * self.swap_fee;
        let withdrawn_net_fee = withdrawn_with_fee * weighted_fee;

        self.balances[token] -= withdrawn_net_fee;
        self.supply -= amount;
        withdrawn_net_fee
    }

    /// Withdrawn liquditiy from the pool with `amount` of `tokens` withdrawn
    ///
    /// Returns the amount of pool shares burnt
    pub fn single_sided_wd_given_out(&mut self, token: usize, amount: f64) -> f64 {
        let weighted_fee = 1.0 - (1.0 - self.weights[token]) * self.swap_fee;
        let withdrawn_with_fee = amount / weighted_fee;

        let ratio = 1.0 - withdrawn_with_fee / self.balances[token];
        let weighted_ratio = 1.0 - ratio.powf(self.weights[token]);
        let amount_burnt = self.supply * weighted_ratio;

        self.balances[token] -= amount;
        self.supply -= amount_burnt;
        amount_burnt
    }
}

pub trait F64Utils {
    fn to_i128(&self, decimals: &u32) -> i128;
}

impl F64Utils for f64 {
    fn to_i128(&self, decimals: &u32) -> i128 {
        let scalar_f64 = 10_f64.powi(*decimals as i32);
        (*self * scalar_f64) as i128
    }
}
