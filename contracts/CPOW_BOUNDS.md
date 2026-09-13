# Proof argument for `c_pow`

This document gives the mathematical argument supporting the implementation.
It is written so its lemmas can be transferred to a proof assistant, but it is
not itself a machine-checked proof.

`c_pow(base, exp, false)` returns a lower bound and
`c_pow(base, exp, true)` returns an upper bound for

```text
(base / BONE) ^ (exp / BONE) * BONE.
```

The admitted domain is

```text
1 <= base < 2 * BONE
0 <= exp <= MAX_CPOW_EXP <= 10 * BONE
BONE = 10^18.
```

The exponent limit is derived at compile time as
`ceil(BONE * STROOP / MIN_WEIGHT)`, matching the directed reciprocal used by
the pool math. With the current 10% minimum normalized weight, this is
`10 * BONE`. A compile-time assertion rejects any weight configuration whose
derived limit exceeds the formally supported maximum, so the limit cannot
silently outgrow the integer-power and overflow arguments below.

Let

```text
F(B, E) = S * (B / S) ^ (E / S), where S = BONE.
```

The function's postcondition is

```text
c_pow(B, E, false) <= F(B, E) <= c_pow(B, E, true).
```

All inequalities in this document compare integer return values with real
scaled values.

## Arithmetic model

`Cargo.lock` pins `soroban-fixed-point-math` 1.5.0. For the positive
denominators used here, its `I256` operations implement

```text
fixed_mul_floor(p, q, S) = floor(pq / S)
fixed_mul_ceil(p, q, S)  = ceil(pq / S)
fixed_div_floor(p, q, S) = floor(pS / q)
fixed_div_ceil(p, q, S)  = ceil(pS / q).
```

Consequently, each floor is at most its real argument and less than one integer
unit below it; each ceiling is at least its real argument and less than one
integer unit above it. The overflow bounds below ensure the underlying `I256`
addition, subtraction, and multiplication are exact throughout this function.

## Exponent decomposition

Write `exp / BONE = n + a`, where `n` is an integer and `0 <= a < 1`.
`c_powi` computes a directed bound for `base^n`. This follows by induction over
exponentiation by squaring: all operands are non-negative, multiplication is
monotone on non-negative values, and every multiplication is rounded in the
requested direction.

For `a > 0`, let `x = base / BONE - 1`. The fractional factor is the convergent
generalized binomial series

```text
(1 + x)^a = sum(T_k, k = 0..infinity)
T_0 = 1
T_k = T_(k-1) * (a - k + 1) * x / k.
```

The base checks give `-1 < x < 1`, so the series converges.

## Fixed-point recurrence error

Let `S = BONE`, `A` be the scaled fractional exponent, and `X` be the scaled
value of `x`. For iteration `k`, define

```text
C_k = A - (k - 1)S
U_k = C_k X / S
T_k = T_(k-1) U_k / (kS).
```

The implementation computes

```text
u_k = floor(U_k)
v_k = floor(t_(k-1) u_k / S)
t_k = floor(v_k / k).
```

Every floor differs from its real argument by less than one integer unit. The
exact term magnitudes decrease, so `|T_k| <= S`. Also, `|C_k| < kS` and
`|X| < S`, giving `|u_k| < kS + 1`.

The first iteration simplifies exactly to

```text
t_1 = floor(a * x * BONE),
```

and therefore `|T_1 - t_1| < 1`.

For `k >= 2`, let `D_k = |T_k - t_k|`. Separating the previous-term error from
the three new rounding errors gives

```text
D_k < (1 + 1/(kS)) D_(k-1) + 1/k + 1/k + 1.
```

For `k <= 50`, the induction bound is much smaller than `S`, so the extra
`D_(k-1)/(kS)` is below one unit. For `k >= 2`, `2/k <= 1`. Consequently

```text
D_k < E_(k-1) + 3
```

whenever `D_(k-1) < E_(k-1)`. Starting from `E_1 = 1`, induction gives

```text
|T_k - t_k| < 3k - 2.
```

Addition is exact, so the computed partial sum `s_N` satisfies

```text
|S_N - s_N| < sum(3k - 2, k = 1..N)
              = (3N^2 - N) / 2.
```

For `N = 1`, the implementation uses the tighter asymmetric fact
`s_1 <= S_1 < s_1 + 1`.

## Series remainder

When `x > 0`, terms after the constant alternate with decreasing magnitude.
The alternating-series theorem says the remainder has the next term's sign and
is no larger than its magnitude.

When `x < 0`, every non-constant term is negative. If `q = |x|`, successive
term magnitudes have ratio strictly below `q`, hence

```text
abs(S_infinity - S_N) <= abs(T_N) * q / (1 - q).
```

`term_magnitude_bound` combines `abs(t_N) + (3N - 2)`. For alternating series,
the current term bounds the next term and therefore the remainder. The
implementation calculates the tighter next-term bound for the important
first-iteration case so small operations do not lose their entire first-order
correction.

For `x < 0`, more than one iteration, and `q <= 1/2`, the current term bounds
the geometric tail because `q / (1 - q) <= 1`. The first-iteration case uses
the tighter next-term calculation to preserve small first-order corrections.
For larger `q`, directed ceil operations calculate the full geometric bound.
The returned tail bound is therefore never smaller than the exact omitted
tail. This remains true if the loop reaches its 50-iteration cap.

The known identities `base > 1 => base^exp >= 1` and
`base < 1 => base^exp <= 1` tighten, but never weaken, the resulting bounds.

## Validity domain and pool operating band

The broad admitted domain is required for total correctness, including requests
that are evaluated and subsequently rejected by a pool ratio check. Bound
validity does not imply uniform tightness: the geometric majorant becomes loose
as `base` approaches its minimum value and `q = 1 - base` approaches one.

Successful pool state transitions operate in the conservative band

```text
0.5 <= base <= 1.6
0.1 <= exp <= 10.
```

To see why, let `r = MAX_IN_RATIO / STROOP` (equivalently the maximum output
ratio to the precision used here), so `r` is only slightly above `1/3`:

- An exact-input swap uses `base = balance / (balance + adjusted_input)`, which
  is greater than `1 / (1 + r) > 0.749`.
- An exact-output swap uses `base = balance / (balance - output)`, which is less
  than `1 / (1 - r) < 1.501`.
- A direct single-asset deposit has `base <= 1 + r < 1.334`.
- For a direct single-asset withdrawal, the fee adjustment is at most 9%, so
  `base >= 1 - r / 0.91 > 0.633`.
- In the LP-specified variants, an accepted deposit with `base > 1 + r` would
  require more than the permitted input ratio. An accepted withdrawal with
  `base < 0.5` would return more than the permitted output ratio: its exponent
  is at least one, its upper power bound is no greater than `base`, and the fee
  multiplier is at least 0.91.

Normalized weights, ratios of normalized weights, and reciprocal normalized
weights place every pool exponent between 0.1 and 10. The wider `[0.5, 1.6]`
base band leaves margin for the pool's fixed-point rounding. Compile-time
assertions tie this envelope to `MAX_IN_RATIO`, `MAX_OUT_RATIO`, `MAX_FEE`,
`MIN_WEIGHT`, and `MAX_WEIGHT`. The Lean configuration module imports those
values from Rust and checks the corresponding input, output, fee-adjusted
withdrawal, and reciprocal-weight margins, so an unsafe configuration change
cannot leave the convergence argument silently stale.

### Iteration guarantee in the operating band

The 50-iteration loop is a hard resource cap, not a convergence guarantee over
the complete admitted base domain. It does, however, have a stronger stopping
guarantee throughout the pool operating band. Let `q = abs(x)`. For fractional
`a`, every exact binomial-term ratio is at most `q`, so

```text
abs(T_N) <= BONE * q^N.
```

Combining this with the recurrence error bound gives

```text
abs(t_N) < BONE * q^N + (3N - 2).
```

The operating band `0.5 <= base <= 1.6` implies `q <= 3/5`. At `N = 46`,

```text
BONE * (3/5)^46 + 136 < 62,367,519 < CPOW_PRECISION = 100,000,000.
```

Therefore the computed term satisfies the loop's stopping condition by
iteration 46, before the iteration-50 cap, for every fractional exponent used
by a successful pool operation. More generally, the iteration-50 inequality

```text
BONE * q^50 + 148 <= CPOW_PRECISION
```

holds for `q <= 0.6309573258...`; the simple rational band
`0.37 <= base <= 1.63` is sufficient because it gives `q <= 0.63`. Inputs
outside that sufficient band can reach the cap, but the remainder construction
still encloses their omitted tail as described above.

`test_c_pow_pool_operating_band_tracks_signal` samples the band boundaries, both
sides of one, integer and fractional exponents, and the exponent endpoints. It
measures interval width against the guaranteed movement away from one: the
lower-bound movement for `base > 1`, or the upper-bound movement for
`base < 1`. The regression keeps the tighter of the original
one-part-per-billion limit on the full power and a
one-part-per-hundred-million limit on that movement plus 16 raw fixed-point
units for changes near the quantization limit. The second condition exercises
the quantity used by pool formulas that subtract one without weakening the
original threshold for larger movements.

The raw fixed-point allowance can be amplified when a pool formula multiplies
the power by a very large LP supply before downscaling. The end-to-end
single-sided round-trip tests in `c_math` separately require results for
non-dust operations to remain within `1e-4` plus one raw output unit. The
low-token-per-share test records the larger conservative deviation possible for
dust operations. These accuracy checks are regression thresholds and are not
part of the proof of enclosure.

## Overflow bounds

Write `S = BONE = 10^18`. The integer exponent is at most 10. Starting from
`base < 2S`, the three possible squarings in `c_powi` produce scaled values no
larger than `4S`, `16S`, and `256S`. The accumulator never represents a power
above ten, is no larger than `1024S`, and the largest raw multiplication is no
larger than

```text
1024S^2 = 2^10 S^2.
```

In the fractional recurrence, `|C_k| < 50S`, `|X| < S`, and the proven term
error gives `|t_k| < S + 148`. Therefore each recurrence multiplication is
strictly below `51S^2`. The computed partial sum has magnitude below
`2S + 3725 < 3S`.

The current-term magnitude bound is below `S + 296`. The largest raw product
used to construct the geometric tail is consequently below `2S^2`. When
`base = 1`, division by the smallest possible `1 - q` can make the resulting
tail value approach `2S^2`, but it is only subtracted and then clamped; it is
not fed into another multiplication.

The returned fractional bound is between zero and `4S`, and the integer bound
is between zero and `1024S`. Thus the final raw multiplication is below

```text
4096S^2 = 2^12 S^2 < 4.1 * 10^39.
```

The signed 256-bit maximum is greater than `5.7 * 10^76`, so every intermediate
above is strictly in range. The scalar expressions `3N - 2` and
`(3N^2 - N) / 2` are at most 148 and 3725 because `N <= 50`, and therefore
also fit in `i128`.

## Final composition

The exact integer and fractional factors are positive, and their computed
bounds are non-negative. Multiplying two lower bounds and flooring produces a
lower bound; multiplying two upper bounds and ceiling produces an upper bound.
This establishes the stated postcondition for `c_pow` under the arithmetic
model above.

## Runtime construction

The series loop is unchanged and computes only one term and one sum. The error
budget is a closed-form scalar calculation after the loop. `I256` error and
tail values are constructed only inside return paths that use them. In
particular, the common `base < 1, round_up` path constructs only its partial-sum
error; it does not construct a term error or `abs(x)`.

For the usual `|x| <= 1/2` multi-iteration case, the current term itself bounds
the tail, avoiding another fixed-point multiplication or division. The full
geometric calculation is used only for a lower bound with `base < 1/2`, or for
the first iteration where using the current term would erase a small
first-order correction.

## Verification status

The standalone Lean project in [`../verification`](../verification/README.md)
machine-checks the reusable recurrence-error budget, geometric-tail
simplification, composition, configured-limit, and `c_pow`-specific signed
256-bit magnitude and denominator bounds above. Its configured values are
generated from the production Rust constants, and CI rejects the generated
Lean module if those values drift. Lean and mathlib are pinned, CI rebuilds the
project, and the proof sources contain no `sorry`, `admit`, or custom axioms.
The compiled namespace is also audited transitively, allowing only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` foundations.

The reusable checked-`I256` model and positive-denominator floor/ceiling
refinement proofs are maintained with the fixed-point implementation on the
companion `proof/formalize-i256-fixed-point` branch of
`soroban-fixed-point-math`, pinned here to proof commit
[`649f02a`](https://github.com/blnt-protocol/soroban-fixed-point-math/commit/649f02aab503e0502f495b64de5575da2c28434b).
That proof commit is based on `script3` upstream commit `c85960e`; its
`src/i256.rs` is byte-for-byte identical to the implementation in the exact
1.5.0 dependency pinned by this contract.

This is not yet a machine-checked proof of the deployed `c_pow` postcondition.
The generalized binomial series must still be connected to real
exponentiation, the lemmas must be instantiated for every branch of an
executable `c_pow` model, this project's bounds must be mechanically composed
with the upstream refinement theorems, and that model must be connected to the
Rust control flow. The upstream Rust-to-Lean correspondence remains
human-reviewed, and primitive Soroban host operations are trusted to satisfy
their protocol-specified checked-integer semantics. Until those links are
completed, the full enclosure claim remains the mathematical argument in this
document, corroborated by the existing boundary and slow-convergence
regression tests.
