import CometPool.Source.ProportionalLiquiditySource

set_option maxRecDepth 65536

namespace CometPool

/-!
Executable, source-shaped model of the successful arithmetic and configuration
path through `init` and `execute_init`. External token metadata reads and
transfers, authorization, storage writes, and event behavior remain outside the
model; the returned records capture the values written after those operations
succeed and retain queried decimals as a ghost witness for the scalar proof.
-/

universe u

/-- The three parallel public vectors after the source retrieves token decimals. -/
structure InitializationTokenInput (Token : Type u) where
  token : Token
  weight : ℤ
  balance : ℤ
  decimals : ℕ

/-- Written token-record fields plus queried decimals as a proof-only witness. -/
structure InitializedTokenRecord (Token : Type u) where
  token : Token
  weight : ℤ
  balance : ℤ
  decimals : ℕ
  scalar : ℕ
  index : ℕ

/-- Intermediate result after the source-shaped initialization loop. -/
structure InitializationRecordsExecutionResult (Token : Type u) where
  records : List (InitializedTokenRecord Token)
  totalWeight : ℤ

/-- Successful modeled initialization result. -/
structure InitializationExecutionResult (Token : Type u) where
  records : List (InitializedTokenRecord Token)
  totalWeight : ℤ
  swapFee : ℤ
  initialPoolMintAmount : ℕ
  lpDecimals : ℕ

/-- The decimal scalar stored by `execute_init`. -/
def initializationScalar (decimals : ℕ) : ℕ := 10 ^ (18 - decimals)

theorem initializationScalar_positive (decimals : ℕ) :
    0 < initializationScalar decimals := by
  exact pow_pos (by norm_num) _

theorem initializationScalar_le_bone
    {decimals : ℕ} (hdecimals : decimals ≤ 18) :
    initializationScalar decimals ≤ BONE := by
  interval_cases decimals <;> norm_num [initializationScalar, BONE]

/-- Build the source loop's aligned token inputs from its three public vectors. -/
def initializationInputs (decimals : Token → ℕ) :
    List Token → List ℤ → List ℤ →
      Option (List (InitializationTokenInput Token))
  | [], [], [] => some []
  | token :: tokens, weight :: weights, balance :: balances => do
      let inputs ← initializationInputs decimals tokens weights balances
      some ({ token, weight, balance, decimals := decimals token } :: inputs)
  | _, _, _ => none

/--
Execute the record-building loop with the source's duplicate and configured
range guards. Checked i128 addition models release-profile overflow checking on
`total_weight += weight`.
-/
def initializationRecordsExecution [DecidableEq Token]
    (seen : List Token) (index : ℕ) (totalWeight : ℤ) :
    List (InitializationTokenInput Token) →
      Option (InitializationRecordsExecutionResult Token)
  | [] => some { records := [], totalWeight }
  | input :: inputs => do
      if input.token ∈ seen then
        none
      else if input.weight < (MIN_WEIGHT : ℤ) then
        none
      else if (MAX_WEIGHT : ℤ) < input.weight then
        none
      else if input.balance < (MIN_BALANCE : ℤ) then
        none
      else if 18 < input.decimals then
        none
      else
        let nextTotalWeight ←
          SorobanFixedPointMath.I128.add totalWeight input.weight
        let tail ← initializationRecordsExecution
          (input.token :: seen) (index + 1) nextTotalWeight inputs
        some {
          records := {
            token := input.token
            weight := input.weight
            balance := input.balance
            decimals := input.decimals
            scalar := initializationScalar input.decimals
            index
          } :: tail.records
          totalWeight := tail.totalWeight
        }

/--
Source-shaped successful initialization. `alreadyInitialized` models the
controller storage-key check; vector-length, fee, token-record, and total-weight
guards follow `execute_init` in source order.
-/
def initializationExecution [DecidableEq Token]
    (alreadyInitialized : Bool)
    (tokens : List Token) (weights balances : List ℤ)
    (decimals : Token → ℕ) (swapFee : ℤ) :
    Option (InitializationExecutionResult Token) := do
  if alreadyInitialized = true then
    none
  else if tokens.length < 2 then
    none
  else if 8 < tokens.length then
    none
  else if weights.length ≠ tokens.length then
    none
  else if balances.length ≠ tokens.length then
    none
  else if swapFee < (MIN_FEE : ℤ) then
    none
  else if (MAX_FEE : ℤ) < swapFee then
    none
  else
    let inputs ← initializationInputs decimals tokens weights balances
    let recordsResult ←
      initializationRecordsExecution [] 0 0 inputs
    if recordsResult.totalWeight = (STROOP : ℤ) then
      some {
        records := recordsResult.records
        totalWeight := recordsResult.totalWeight
        swapFee
        initialPoolMintAmount := INIT_POOL_SUPPLY
        lpDecimals := 7
      }
    else
      none

/-- Per-record invariants established by successful initialization. -/
structure InitializedTokenRecord.Valid
    (record : InitializedTokenRecord Token) : Prop where
  weightLower : (MIN_WEIGHT : ℤ) ≤ record.weight
  weightUpper : record.weight ≤ (MAX_WEIGHT : ℤ)
  balanceLower : (MIN_BALANCE : ℤ) ≤ record.balance
  balancePositive : 0 < record.balance
  decimalsUpper : record.decimals ≤ 18
  scalarEquation : record.scalar = initializationScalar record.decimals
  scalarPositive : 0 < record.scalar
  scalarUpper : record.scalar ≤ BONE

private theorem initialization_i128_add_success_eq
    {x y result : ℤ}
    (hexec : SorobanFixedPointMath.I128.add x y = some result) :
    result = x + y := by
  have h := SorobanFixedPointMath.I128.checked_eq_some_iff.mp
    (show SorobanFixedPointMath.I128.checked (x + y) = some result from hexec)
  exact h.2.symm

/-- Successful vector alignment preserves every public vector exactly. -/
theorem initializationInputs_success
    {decimals : Token → ℕ} {tokens : List Token} {weights balances : List ℤ}
    {inputs : List (InitializationTokenInput Token)}
    (hexec : initializationInputs decimals tokens weights balances = some inputs) :
    inputs.map (·.token) = tokens ∧
      inputs.map (·.weight) = weights ∧
      inputs.map (·.balance) = balances ∧
      inputs.map (fun input => (input.token, input.decimals)) =
        tokens.map (fun token => (token, decimals token)) := by
  induction tokens generalizing weights balances inputs with
  | nil =>
      cases weights <;> cases balances <;>
        simp [initializationInputs] at hexec ⊢
      subst inputs
      simp
  | cons token tokens ih =>
      cases weights with
      | nil => simp [initializationInputs] at hexec
      | cons weight weights =>
          cases balances with
          | nil => simp [initializationInputs] at hexec
          | cons balance balances =>
              rw [initializationInputs] at hexec
              rcases Option.bind_eq_some.mp hexec with
                ⟨tail, htail, hresult⟩
              have hfields := Option.some.inj hresult
              subst inputs
              rcases ih htail with
                ⟨htokens, hweights, hbalances, htokenDecimals⟩
              exact ⟨by simp [htokens], by simp [hweights],
                by simp [hbalances], by simp [htokenDecimals]⟩

/-- All facts recovered from one successful source-shaped record loop. -/
theorem initializationRecordsExecution_success [DecidableEq Token]
    {seen : List Token} {index : ℕ} {totalWeight : ℤ}
    {inputs : List (InitializationTokenInput Token)}
    {result : InitializationRecordsExecutionResult Token}
    (hexec : initializationRecordsExecution seen index totalWeight inputs =
      some result) :
    result.records.map (·.token) = inputs.map (·.token) ∧
      result.records.map (·.weight) = inputs.map (·.weight) ∧
      result.records.map (·.balance) = inputs.map (·.balance) ∧
      result.records.map (fun record => (record.token, record.decimals)) =
        inputs.map (fun input => (input.token, input.decimals)) ∧
      result.records.map (·.index) = List.range' index inputs.length ∧
      result.totalWeight = totalWeight + (inputs.map (·.weight)).sum ∧
      (inputs.map (·.token)).Nodup ∧
      (∀ token ∈ inputs.map (·.token), token ∉ seen) ∧
      ∀ record ∈ result.records, record.Valid := by
  induction inputs generalizing seen index totalWeight result with
  | nil =>
      simp [initializationRecordsExecution] at hexec
      subst result
      simp
  | cons input inputs ih =>
      rw [initializationRecordsExecution] at hexec
      by_cases hseen : input.token ∈ seen
      · simp [hseen] at hexec
      · rw [if_neg hseen] at hexec
        by_cases hweightLower : input.weight < (MIN_WEIGHT : ℤ)
        · simp [hweightLower] at hexec
        · rw [if_neg hweightLower] at hexec
          by_cases hweightUpper : (MAX_WEIGHT : ℤ) < input.weight
          · simp [hweightUpper] at hexec
          · rw [if_neg hweightUpper] at hexec
            by_cases hbalance : input.balance < (MIN_BALANCE : ℤ)
            · simp [hbalance] at hexec
            · rw [if_neg hbalance] at hexec
              by_cases hdecimals : 18 < input.decimals
              · simp [hdecimals] at hexec
              · rw [if_neg hdecimals] at hexec
                rcases Option.bind_eq_some.mp hexec with
                  ⟨nextTotalWeight, hnextTotalWeight, hexec⟩
                rcases Option.bind_eq_some.mp hexec with
                  ⟨tail, htail, hresult⟩
                have hfields := Option.some.inj hresult
                cases hfields
                rcases ih htail with
                  ⟨htokens, hweights, hbalances, htokenDecimals, hindices,
                    htotalWeight, hnodup, hnotSeen, hvalid⟩
                have hnextTotalWeightEq :=
                  initialization_i128_add_success_eq hnextTotalWeight
                have hheadNotTail :
                    input.token ∉ inputs.map (·.token) := by
                  intro hmember
                  have hnot := hnotSeen input.token hmember
                  exact hnot (by simp)
                have hheadValid :
                    (InitializedTokenRecord.mk input.token input.weight
                      input.balance input.decimals
                      (initializationScalar input.decimals) index).Valid := by
                  refine {
                    weightLower := le_of_not_gt hweightLower
                    weightUpper := le_of_not_gt hweightUpper
                    balanceLower := le_of_not_gt hbalance
                    balancePositive := ?_
                    decimalsUpper := le_of_not_gt hdecimals
                    scalarEquation := rfl
                    scalarPositive := initializationScalar_positive _
                    scalarUpper := initializationScalar_le_bone
                      (le_of_not_gt hdecimals)
                  }
                  have hminBalance : (0 : ℤ) < MIN_BALANCE := by
                    norm_num [MIN_BALANCE]
                  exact lt_of_lt_of_le hminBalance (le_of_not_gt hbalance)
                refine ⟨by simp [htokens], by simp [hweights],
                  by simp [hbalances], by simp [htokenDecimals], ?_, ?_, ?_,
                  ?_, ?_⟩
                · simp only [List.map_cons, List.length_cons]
                  rw [List.range'_succ]
                  exact congrArg (fun indices => index :: indices) hindices
                · rw [htotalWeight, hnextTotalWeightEq]
                  simp
                  ring
                · simp [hheadNotTail, hnodup]
                · intro token hmember
                  rcases List.mem_cons.mp hmember with hhead | htailMember
                  · simpa [hhead] using hseen
                  · have hnot := hnotSeen token htailMember
                    exact fun htokenSeen => hnot (by simp [htokenSeen])
                · intro record hmember
                  rcases List.mem_cons.mp hmember with hhead | htailMember
                  · simpa [hhead] using hheadValid
                  · exact hvalid record htailMember

/-- Complete configuration facts established by a successful public init model. -/
structure InitializationInvariants
    (alreadyInitialized : Bool)
    (tokens : List Token) (weights balances : List ℤ)
    (decimals : Token → ℕ) (swapFee : ℤ)
    (result : InitializationExecutionResult Token) : Prop where
  notAlreadyInitialized : alreadyInitialized = false
  tokenCountLower : 2 ≤ tokens.length
  tokenCountUpper : tokens.length ≤ 8
  weightsLength : weights.length = tokens.length
  balancesLength : balances.length = tokens.length
  feeLower : (MIN_FEE : ℤ) ≤ swapFee
  feeUpper : swapFee ≤ (MAX_FEE : ℤ)
  recordTokens : result.records.map (·.token) = tokens
  recordWeights : result.records.map (·.weight) = weights
  recordBalances : result.records.map (·.balance) = balances
  recordTokenDecimals :
    result.records.map (fun record => (record.token, record.decimals)) =
      tokens.map (fun token => (token, decimals token))
  recordIndices : result.records.map (·.index) = List.range' 0 tokens.length
  tokensNodup : tokens.Nodup
  recordWeightTotal : (result.records.map (·.weight)).sum = (STROOP : ℤ)
  everyRecordValid : ∀ record ∈ result.records, record.Valid
  totalWeight : result.totalWeight = (STROOP : ℤ)
  storedSwapFee : result.swapFee = swapFee
  initialPoolMintAmount : result.initialPoolMintAmount = INIT_POOL_SUPPLY
  initialPoolMintAmountPositive : 0 < result.initialPoolMintAmount
  lpDecimals : result.lpDecimals = 7

/-- Successful initialization establishes every modeled configuration invariant. -/
theorem initializationExecution_establishes_invariants [DecidableEq Token]
    {alreadyInitialized : Bool}
    {tokens : List Token} {weights balances : List ℤ}
    {decimals : Token → ℕ} {swapFee : ℤ}
    {result : InitializationExecutionResult Token}
    (hexec : initializationExecution alreadyInitialized tokens weights balances
      decimals swapFee = some result) :
    InitializationInvariants alreadyInitialized tokens weights balances
      decimals swapFee result := by
  rw [initializationExecution] at hexec
  by_cases hinitialized : alreadyInitialized = true
  · simp [hinitialized] at hexec
  · rw [if_neg hinitialized] at hexec
    by_cases htokenLower : tokens.length < 2
    · simp [htokenLower] at hexec
    · rw [if_neg htokenLower] at hexec
      by_cases htokenUpper : 8 < tokens.length
      · simp [htokenUpper] at hexec
      · rw [if_neg htokenUpper] at hexec
        by_cases hweightsLength : weights.length ≠ tokens.length
        · simp [hweightsLength] at hexec
        · rw [if_neg hweightsLength] at hexec
          by_cases hbalancesLength : balances.length ≠ tokens.length
          · simp [hbalancesLength] at hexec
          · rw [if_neg hbalancesLength] at hexec
            by_cases hfeeLower : swapFee < (MIN_FEE : ℤ)
            · simp [hfeeLower] at hexec
            · rw [if_neg hfeeLower] at hexec
              by_cases hfeeUpper : (MAX_FEE : ℤ) < swapFee
              · simp [hfeeUpper] at hexec
              · rw [if_neg hfeeUpper] at hexec
                rcases Option.bind_eq_some.mp hexec with
                  ⟨inputs, hinputs, hexec⟩
                rcases Option.bind_eq_some.mp hexec with
                  ⟨recordsResult, hrecords, hexec⟩
                by_cases htotalWeight :
                    recordsResult.totalWeight = (STROOP : ℤ)
                · rw [if_pos htotalWeight] at hexec
                  have hfields := Option.some.inj hexec
                  cases hfields
                  rcases initializationInputs_success hinputs with
                    ⟨hinputTokens, hinputWeights, hinputBalances,
                      hinputTokenDecimals⟩
                  rcases initializationRecordsExecution_success hrecords with
                    ⟨hrecordTokens, hrecordWeights, hrecordBalances,
                      hrecordTokenDecimals, hrecordIndices, hrecordTotal,
                      hnodup, hnotSeen, hvalid⟩
                  refine {
                    notAlreadyInitialized := by
                      cases alreadyInitialized <;> simp_all
                    tokenCountLower := le_of_not_gt htokenLower
                    tokenCountUpper := le_of_not_gt htokenUpper
                    weightsLength := not_ne_iff.mp hweightsLength
                    balancesLength := not_ne_iff.mp hbalancesLength
                    feeLower := le_of_not_gt hfeeLower
                    feeUpper := le_of_not_gt hfeeUpper
                    recordTokens := hrecordTokens.trans hinputTokens
                    recordWeights := hrecordWeights.trans hinputWeights
                    recordBalances := hrecordBalances.trans hinputBalances
                    recordTokenDecimals :=
                      hrecordTokenDecimals.trans hinputTokenDecimals
                    recordIndices := ?_
                    tokensNodup := by simpa [hinputTokens] using hnodup
                    recordWeightTotal := ?_
                    everyRecordValid := hvalid
                    totalWeight := htotalWeight
                    storedSwapFee := rfl
                    initialPoolMintAmount := rfl
                    initialPoolMintAmountPositive := by
                      norm_num [INIT_POOL_SUPPLY]
                    lpDecimals := rfl
                  }
                  · have hinputLength : inputs.length = tokens.length := by
                      simpa using congrArg List.length hinputTokens
                    simpa [hinputLength] using hrecordIndices
                  calc
                    (recordsResult.records.map (·.weight)).sum =
                        (inputs.map (·.weight)).sum :=
                      congrArg List.sum hrecordWeights
                    _ = recordsResult.totalWeight := by
                      simpa using hrecordTotal.symm
                    _ = (STROOP : ℤ) := htotalWeight
                · simp [htotalWeight] at hexec

end CometPool
