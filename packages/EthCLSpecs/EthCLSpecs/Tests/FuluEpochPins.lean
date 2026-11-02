import EthCLSpecs.Fulu.EpochProcessing

/-!
# `EthCLSpecs.Tests.FuluEpochPins`: the epoch substeps' index and `uint64` faults

The pins cover two rejects: `.outOfBounds` for a per-validator list shorter than the
registry (the pyspec's `IndexError`), and `.arithmetic` for a `uint64` over- or underflow
(its `ValueError`). Two pins check the other side: the hysteresis `or` skips a sum that would
overflow, and a non-participant never reads the finality delay, so those steps succeed. No
conformance vector reaches these paths. Gloas and Heze inherit every substep pinned here but
`process_pending_deposits`, which Gloas overrides and Heze inherits from Gloas. Its Gloas
pins are in `Tests/GloasEpochPins.lean`.
`State` is FFI-backed, so `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.FuluEpochPins

open EthCLSpecs.Fulu

/-- The pins' state-machine monad over the minimal preset and the FFI hasher. -/
private abbrev PinM := EStateM StateTransitionError (@State minimal fastHasherTag)

/-- A minimal Fulu state at epoch 1, so the inactivity substeps run. Its first validator is
active from genesis, has effective balance `eb`, and carries participation `flags` in both
epochs (none by default); `extra` validators follow it. `participation` overrides both
participation lists. `balances`, `inactivityScores`, and `participation` may be shorter than
the registry. `slashings[0] = slashed0`, `slashings[1] = slashed1`,
`deposit_balance_to_consume = toConsume`, `finalized_checkpoint.epoch = finalized`, and
`pending_deposits = deposits`. -/
private def fixture (eb : Gwei) (balances scores : Array UInt64) (slashed0 : Gwei := 0)
    (flags : UInt8 := 0) (toConsume : Gwei := 0) (slashed1 : Gwei := 0) (finalized : Epoch := 0)
    (extra : Array (@Validator minimal) := #[]) (participation : Array UInt8 := #[flags])
    (deposits : Array (@PendingDeposit minimal) := #[]) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := eb,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  -- The empty fallback never fires: every array here has at most two entries.
  let list {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
    if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩
  SSZ.FastBox
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      slot := UInt64.ofNat Const.slotsPerEpoch
      validators := list (#[v] ++ extra)
      balances := list balances
      inactivityScores := list scores
      previousEpochParticipation := list participation
      currentEpochParticipation := list participation
      slashings := Vector.ofFn fun i =>
        if i.val = 0 then slashed0 else if i.val = 1 then slashed1 else 0
      depositBalanceToConsume := toConsume
      finalizedCheckpoint := { epoch := finalized, root := default }
      pendingDeposits := list deposits }

/-- Run one epoch substep over a fixture, and report whether it rejected with the
constructor `ok` accepts. -/
private def rejectsWith (step : PinM Unit) (s : @State minimal fastHasherTag)
    (ok : StateTransitionError → Bool) : Bool :=
  match step.run s with
  | .error e _ => ok e
  | .ok _ _ => false

private def isOob : StateTransitionError → Bool | .outOfBounds _ _ => true | _ => false
private def isArith : StateTransitionError → Bool | .arithmetic _ => true | _ => false

/-- `.arithmetic` raised at the operation `descr` names, for a step that computes more than
one checked operation. -/
private def isArithAt (descr : String) : StateTransitionError → Bool
  | .arithmetic d => d == descr
  | _ => false

private def maxU64 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- `process_effective_balance_updates`: an empty `balances` list rejects with
`.outOfBounds`, and a balance at `2**64 - 1` overflows `balance + DOWNWARD_THRESHOLD`. -/
private def pinEffectiveBalanceUpdates : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processEffectiveBalanceUpdates (fixture 32000000000 #[] #[0]) isOob &&
  rejectsWith processEffectiveBalanceUpdates (fixture 32000000000 #[maxU64] #[0]) isArith
example : pinEffectiveBalanceUpdates = true := by native_decide

/-- `process_effective_balance_updates`: with effective balance `2**64 - 1` and a 32 ETH
balance, `balance + DOWNWARD_THRESHOLD < effective_balance` holds. The spec's `or` then
never forms `effective_balance + UPWARD_THRESHOLD`, which would overflow, so the step
succeeds. -/
private def pinEffectiveBalanceShortCircuit : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (processEffectiveBalanceUpdates : PinM Unit).run (fixture maxU64 #[32000000000] #[0]) with
  | .ok _ _ => true
  | .error _ _ => false
example : pinEffectiveBalanceShortCircuit = true := by native_decide

/-- `process_inactivity_updates`: an empty `inactivity_scores` list or an empty previous
participation list rejects with `.outOfBounds`, and a non-participating validator's score at
`2**64 - 1` overflows `+= INACTIVITY_SCORE_BIAS`. -/
private def pinInactivityUpdates : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processInactivityUpdates (fixture 32000000000 #[32000000000] #[]) isOob &&
  rejectsWith processInactivityUpdates
    (fixture 32000000000 #[32000000000] #[0] (participation := #[])) isOob &&
  rejectsWith processInactivityUpdates (fixture 32000000000 #[32000000000] #[maxU64]) isArith
example : pinInactivityUpdates = true := by native_decide

/-- The spec's description of `get_finality_delay`'s subtraction. -/
private def finalityDelayDescr : String :=
  "get_finality_delay: get_previous_epoch(state) - state.finalized_checkpoint.epoch"

/-- `get_finality_delay`'s `uint64` subtraction underflows when the finalized epoch (1) is past
the previous epoch (0). `process_inactivity_updates` reads the delay after the eligible
validator's score update, so it rejects with `.arithmetic`. -/
private def pinInactivityUpdatesFinalityDelay : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processInactivityUpdates
    (fixture 32000000000 #[32000000000] #[0] (finalized := 1)) (isArithAt finalityDelayDescr)
example : pinInactivityUpdatesFinalityDelay = true := by native_decide

/-- `get_flag_index_deltas` reads the finality delay only for a participant
(`altair/beacon-chain.md:480`). With the finalized epoch past the previous epoch, a
target-participating validator rejects with `.arithmetic`. A non-participant takes the
penalty branch, never reads the delay, and succeeds. -/
private def pinFlagDeltaFinalityDelay : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let participant := fixture 32000000000 #[32000000000] #[0] (flags := 0b010) (finalized := 1)
  let absent := fixture 32000000000 #[32000000000] #[0] (finalized := 1)
  (match getFlagIndexDeltas participant Const.timelyTargetFlagIndex with
    | .error e => isArithAt finalityDelayDescr e
    | .ok _ => false) &&
  (match getFlagIndexDeltas absent Const.timelyTargetFlagIndex with
    | .ok _ => true
    | .error _ => false)
example : pinFlagDeltaFinalityDelay = true := by native_decide

/-- `get_flag_index_deltas` and `get_inactivity_penalty_deltas`: an empty previous
participation list rejects with `.outOfBounds` at `get_unslashed_participating_indices`
(`altair/beacon-chain.md:412`), and an empty `inactivity_scores` list rejects the penalty
read (`bellatrix/beacon-chain.md:305`). -/
private def pinDeltasOutOfBounds : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  (match getFlagIndexDeltas (fixture 32000000000 #[32000000000] #[0] (participation := #[]))
      Const.timelyTargetFlagIndex with
    | .error e => isOob e
    | .ok _ => false) &&
  (match getInactivityPenaltyDeltas (fixture 32000000000 #[32000000000] #[]) with
    | .error e => isOob e
    | .ok _ => false)
example : pinDeltasOutOfBounds = true := by native_decide

/-- `get_inactivity_penalty_deltas`: `effective_balance * inactivity_scores[index]`
overflows for a 32 ETH validator whose score is `2**40`. -/
private def pinInactivityPenaltyOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match getInactivityPenaltyDeltas (fixture 32000000000 #[32000000000] #[0x10000000000]) with
  | .error (.arithmetic _) => true
  | _ => false
example : pinInactivityPenaltyOverflow = true := by native_decide

/-- `process_slashings`: `sum(state.slashings) * PROPORTIONAL_SLASHING_MULTIPLIER_BELLATRIX`
overflows when one slot already holds `2**64 - 1`. -/
private def pinSlashingsOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processSlashings (fixture 32000000000 #[32000000000] #[0] maxU64) isArith
example : pinSlashingsOverflow = true := by native_decide

/-- `process_slashings`: `sum(state.slashings)` overflows when two slots hold `2**63` each
(`electra/beacon-chain.md:1086`). -/
private def pinSlashingsSumOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processSlashings
    (fixture 32000000000 #[32000000000] #[0] 0x8000000000000000 (slashed1 := 0x8000000000000000))
    (isArithAt "process_slashings: sum(state.slashings)")
example : pinSlashingsSumOverflow = true := by native_decide

/-- `process_slashings`: `penalty_per_effective_balance_increment * effective_balance_increments`
overflows (`electra/beacon-chain.md:1101`). The active validator holds `1.9 * 10**9` Gwei, so
the total is one increment and the per-increment penalty is `1.9 * 10**9`. The second
validator is slashed and already exited, so its effective balance of `2**64 - 1` stays out of
the total. Its withdrawable epoch is `epoch + EPOCHS_PER_SLASHINGS_VECTOR // 2`, so the
penalty applies, and `1.9 * 10**9 * 18446744073` overflows. -/
private def pinSlashingsPenaltyOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let slashed : Validator :=
    { (default : Validator) with
      effectiveBalance := maxU64, slashed := true, exitEpoch := 0,
      withdrawableEpoch := 1 + UInt64.ofNat Const.epochsPerSlashingsVector / 2 }
  rejectsWith processSlashings
    (fixture 1900000000 #[1900000000, 0] #[0] 1900000000 (extra := #[slashed]))
    (isArithAt
      "process_slashings: penalty_per_effective_balance_increment * effective_balance_increments")
example : pinSlashingsPenaltyOverflow = true := by native_decide

/-- `get_flag_index_deltas`: `base_reward * weight * unslashed_participating_increments`
overflows for a target-participating validator with effective balance `10**17` Gwei. Its
`base_reward` is `10**8 * 202`, so the product is about `5.25 * 10**19`. Epoch 1 has no
inactivity leak, so the reward branch runs. -/
private def pinFlagDeltaOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let s := fixture 100000000000000000 #[100000000000000000] #[0] (flags := 0b010)
  match getFlagIndexDeltas s Const.timelyTargetFlagIndex with
  | .error (.arithmetic _) => true
  | _ => false
example : pinFlagDeltaOverflow = true := by native_decide

/-- `weigh_justification_and_finalization`: `previous_epoch_target_balance * 3`,
`total_active_balance * 2`, and `current_epoch_target_balance * 3` overflow `uint64`
(`phase0/beacon-chain.md:1978`, `:1983`). The first two run before any block-root read. The
third runs after the previous epoch's root read, which a zero previous target skips, so the
epoch-1 fixture reaches all three through a direct call. -/
private def pinJustificationOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let s := fixture 32000000000 #[32000000000] #[0]
  rejectsWith (weighJustificationAndFinalization 32000000000 maxU64 0) s isArith &&
  rejectsWith (weighJustificationAndFinalization maxU64 0 0) s isArith &&
  rejectsWith (weighJustificationAndFinalization 32000000000 0 maxU64) s
    (isArithAt "weigh_justification_and_finalization: current_epoch_target_balance * 3")
example : pinJustificationOverflow = true := by native_decide

/-- `process_pending_deposits`: `deposit_balance_to_consume + get_activation_exit_churn_limit`
overflows when the carried churn is `2**64 - 1`. The sum runs before the deposit scan, so
no signature check runs. -/
private def pinPendingDepositsOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  rejectsWith processPendingDeposits
    (fixture 32000000000 #[32000000000] #[0] (toConsume := maxU64)) isArith
example : pinPendingDepositsOverflow = true := by native_decide

/-- `process_pending_deposits`: two top-ups to the fixture's own pubkey, `1` then `2**64 - 1`.
The first fits the churn and applies as a balance top-up, with no signature check. The second
overflows `processed_amount + deposit.amount` (`fulu/beacon-chain.md:452`). -/
private def pinPendingDepositsChurnSumOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  let topUp (amount : Gwei) : PendingDeposit := { (default : PendingDeposit) with amount }
  rejectsWith processPendingDeposits
    (fixture 32000000000 #[32000000000] #[0] (deposits := #[topUp 1, topUp maxU64]))
    (isArithAt "process_pending_deposits: processed_amount + deposit.amount")
example : pinPendingDepositsChurnSumOverflow = true := by native_decide

/-- `process_pending_deposits`: `compute_start_slot_at_epoch` overflows on a finalized epoch
of `2**61`, since minimal `SLOTS_PER_EPOCH` is 8 (`fulu/beacon-chain.md:424`). -/
private def pinPendingDepositsFinalizedSlotOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  rejectsWith processPendingDeposits
    (fixture 32000000000 #[32000000000] #[0] (finalized := 0x2000000000000000))
    (isArithAt
      "process_pending_deposits: compute_start_slot_at_epoch(state.finalized_checkpoint.epoch)")
example : pinPendingDepositsFinalizedSlotOverflow = true := by native_decide

end EthCLSpecs.Tests.FuluEpochPins
