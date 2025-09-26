"""
Rust-accurate simulation of Comet pool trades
Calculates PnL for 1st and 50th trader after 100 trades of 1250 KALE each
"""
from dataclasses import dataclass
from typing import Tuple

# Constants matching Rust c_consts.rs
BONE = 10**18
STROOP = 10**7
STROOP_SCALAR = 10**11
MAX_IN_RATIO = (STROOP // 3) + 1  # 33.33%
MAX_OUT_RATIO = (STROOP // 3) + 1  # 33.33%

# Pool configuration matching your Rust setup
MIN_FEE = 10
MAX_FEE = 98_00000
LOW_UTIL = 100 * STROOP
HIGH_UTIL = 100_000 * STROOP

@dataclass
class Record:
    balance: int  # 7-decimal stroops
    weight: int   # 1e7 scale
    scalar: int   # 1e11 for 7-decimal tokens

def fixed_mul_floor(a: int, b: int, scale: int) -> int:
    """Fixed point multiplication with floor rounding"""
    return (a * b) // scale

def fixed_div_floor(numer: int, denom: int, scale: int) -> int:
    """Fixed point division with floor rounding"""
    return (numer * scale) // denom

def upscale(amount: int, scalar: int) -> int:
    """Upscale from 7 decimals to 18 decimals"""
    return amount * scalar

def downscale_floor(amount: int, scalar: int) -> int:
    """Downscale from 18 decimals to 7 decimals with floor rounding"""
    return amount // scalar

def sub_no_negative(a: int, b: int) -> int:
    """Subtract with no negative result"""
    return max(0, a - b)

def read_swap_fee(kale_balance: int) -> int:
    """
    Calculate dynamic swap fee based on KALE balance.
    Matches Rust read_swap_fee implementation exactly.
    """
    if MAX_FEE <= MIN_FEE or HIGH_UTIL <= LOW_UTIL:
        return MAX_FEE
    
    # Upscale to 18 decimals for precision
    scalar = STROOP_SCALAR
    current_balance = kale_balance * scalar
    low_balance = LOW_UTIL * scalar
    high_balance = HIGH_UTIL * scalar
    
    # Clamp between low and high
    clamped = max(low_balance, min(current_balance, high_balance))
    
    span = high_balance - low_balance
    if span <= 0:
        return MAX_FEE
    
    # Calculate utilization
    utilization = fixed_div_floor(clamped - low_balance, span, STROOP)
    
    # Calculate fee
    fee_delta = fixed_mul_floor(MAX_FEE - MIN_FEE, utilization, STROOP)
    return MAX_FEE - fee_delta

def calc_spot_price(in_record: Record, out_record: Record, swap_fee: int) -> int:
    """Calculate spot price with fee (Rust calc_spot_price)"""
    numer = fixed_div_floor(in_record.balance, in_record.weight, STROOP)
    denom = fixed_div_floor(out_record.balance, out_record.weight, STROOP)
    ratio = fixed_div_floor(numer, denom, STROOP)
    return fixed_div_floor(ratio, STROOP - swap_fee, STROOP)

def c_pow_equal_weights(base: int, exp: int) -> int:
    """
    For equal weights (50/50), the weight ratio is 1.0, 
    so power function returns base unchanged
    """
    # When weight_in/weight_out = 1, exp = BONE (1e18)
    # c_pow(base, BONE) = base for integer exponent 1
    return base

def calc_token_out_given_token_in(
    in_record: Record,
    out_record: Record,
    amount_in: int,
    swap_fee: int
) -> int:
    """
    Calculate token out for given token in.
    Exact mirror of Rust calc_token_out_given_token_in.
    """
    # Upscale all values to 18 decimals
    token_balance_in = upscale(in_record.balance, in_record.scalar)
    token_balance_out = upscale(out_record.balance, out_record.scalar)
    token_amount_in = upscale(amount_in, in_record.scalar)
    
    # Apply fee to input (fee on the way in)
    fee_adjust_ratio = upscale(STROOP - swap_fee, STROOP_SCALAR)
    adjusted_in = fixed_mul_floor(token_amount_in, fee_adjust_ratio, BONE)
    
    # Calculate weight ratio (for equal weights, this is 1.0 in 18-decimal)
    weight_ratio = upscale(
        fixed_div_floor(in_record.weight, out_record.weight, STROOP),
        STROOP_SCALAR
    )
    
    # Invariant calculation
    base = fixed_div_floor(
        token_balance_in, 
        token_balance_in + adjusted_in, 
        BONE
    )
    
    # For equal weights (ratio = 1), power = base
    power = c_pow_equal_weights(base, weight_ratio)
    
    balance_ratio = sub_no_negative(BONE, power)
    amount_out_1e18 = fixed_mul_floor(token_balance_out, balance_ratio, BONE)
    
    # Downscale back to 7 decimals
    return downscale_floor(amount_out_1e18, out_record.scalar)

def main():
    """Simulate 100 trades and calculate PnL for traders 1 and 50"""
    
    # Initial pool state (matching your Rust configuration)
    test_balance = 990_000_000 * STROOP  # 990M TEST
    kale_balance = 100 * STROOP          # 100 KALE
    
    # Create records with equal weights
    test_record = Record(
        balance=test_balance,
        weight=50_00000,  # 50%
        scalar=STROOP_SCALAR
    )
    kale_record = Record(
        balance=kale_balance,
        weight=50_00000,  # 50%
        scalar=STROOP_SCALAR
    )
    
    # Storage for trader results
    trader_results = {}
    TARGET_AMOUNT = 1250 * STROOP  # 1250 KALE target per trade
    
    print(f"Initial pool state:")
    print(f"  TEST: {test_record.balance / STROOP:,.2f}")
    print(f"  KALE: {kale_record.balance / STROOP:,.2f}")
    print(f"  Initial fee: {read_swap_fee(kale_record.balance) / 1e5:.5f}%")
    print()
    
    # Execute 100 trades
    for trader_num in range(1, 101):
        # Read current fee
        swap_fee = read_swap_fee(kale_record.balance)
        
        # Apply MAX_IN_RATIO constraint (can't trade more than 33.33% of pool balance)
        max_allowed_in = fixed_mul_floor(kale_record.balance, MAX_IN_RATIO, STROOP)
        amount_in = min(TARGET_AMOUNT, max_allowed_in)
        
        # Calculate output
        test_out = calc_token_out_given_token_in(
            kale_record, test_record, amount_in, swap_fee
        )
        
        # Apply MAX_OUT_RATIO constraint (can't take out more than 33.33% of pool balance)
        max_allowed_out = fixed_mul_floor(test_record.balance, MAX_OUT_RATIO, STROOP)
        if test_out > max_allowed_out:
            print(f"  Trade {trader_num}: Output would exceed MAX_OUT_RATIO, skipping")
            continue
        
        # Update pool state
        kale_record.balance += amount_in
        test_record.balance -= test_out
        
        # Store results for traders 1 and 50
        if trader_num in [1, 50]:
            trader_results[trader_num] = {
                'test_received': test_out,
                'kale_spent': amount_in,
                'fee': swap_fee,
                'spot_price_before': calc_spot_price(kale_record, test_record, swap_fee)
            }
    
    print(f"After 100 trades:")
    print(f"  TEST: {test_record.balance / STROOP:,.2f}")
    print(f"  KALE: {kale_record.balance / STROOP:,.2f}")
    print(f"  Final fee: {read_swap_fee(kale_record.balance) / 1e5:.5f}%")
    print()
    
    # Now calculate what each trader gets if they sell all their TEST back
    sell_fee = read_swap_fee(kale_record.balance)
    
    for trader_num in [1, 50]:
        data = trader_results[trader_num]
        
        # Apply MAX_IN_RATIO constraint when selling TEST
        max_allowed_test_in = fixed_mul_floor(test_record.balance, MAX_IN_RATIO, STROOP)
        test_to_sell = min(data['test_received'], max_allowed_test_in)
        
        # Simulate selling TEST back for KALE
        # Note: We're not updating pool state between these sells,
        # just calculating what each would get at current state
        kale_out = calc_token_out_given_token_in(
            test_record, kale_record,
            test_to_sell,
            sell_fee
        )
        
        # Apply MAX_OUT_RATIO constraint to KALE output
        max_allowed_kale_out = fixed_mul_floor(kale_record.balance, MAX_OUT_RATIO, STROOP)
        kale_out = min(kale_out, max_allowed_kale_out)
        
        # Calculate PnL
        kale_spent = data['kale_spent'] / STROOP
        kale_received = kale_out / STROOP
        net_kale = kale_received - kale_spent
        
        # Assuming KALE = $0.0004 for PnL calculation
        kale_price = 0.0004
        total_spent = kale_spent * kale_price
        total_received = kale_received * kale_price
        pnl_dollars = total_received - total_spent
        
        print(f"Trader {trader_num}:")
        print(f"  Buy fee: {data['fee'] / 1e5:.5f}%")
        print(f"  KALE spent: {kale_spent:.2f}")
        print(f"  TEST received: {data['test_received'] / STROOP:,.2f}")
        if test_to_sell < data['test_received']:
            print(f"  TEST to sell: {test_to_sell / STROOP:,.2f} (limited by MAX_IN_RATIO)")
        print(f"  KALE received on sell: {kale_received:.2f}")
        print(f"  Net KALE: {net_kale:.2f}")
        print(f"  PnL: ${total_spent:.2f} spent, ${total_received:.2f} received, ${pnl_dollars:.2f} net")
        print()

if __name__ == "__main__":
    main()