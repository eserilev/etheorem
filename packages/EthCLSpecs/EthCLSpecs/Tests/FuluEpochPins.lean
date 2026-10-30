import EthCLSpecs.Fulu.EpochProcessing

/-!
# `EthCLSpecs.Tests.FuluEpochPins`: the epoch substeps' index and `uint64` faults

The pins cover two rejects: `.outOfBounds` for a per-validator list shorter than the
registry (the pyspec's `IndexError`), and `.arithmetic` for a `uint64` overflow (its
`ValueError`). One pin checks the other side: the hysteresis `or` skips a sum that would
overflow, so that step succeeds. No conformance vector reaches these paths. Gloas and Heze
inherit the substeps.
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

/-- A minimal Fulu state at epoch 1, so the inactivity substeps run. Its one validator is
active from genesis, has effective balance `eb`, and carries participation `flags` in both
epochs (none by default). `balances` and `inactivityScores` may be shorter than the
registry, `slashings[0] = slashed0`, and `deposit_balance_to_consume = toConsume`. -/
private def fixture (eb : Gwei) (balances scores : Array UInt64) (slashed0 : Gwei := 0)
    (flags : UInt8 := 0) (toConsume : Gwei := 0) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := eb,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  -- The empty fallback never fires: every array here has at most one entry.
  let list {α : Type} {cap : Nat} (a : Array α) : SSZList α cap :=
    if h : a.size ≤ cap then ⟨a, h⟩ else ⟨#[], by simp⟩
  SSZ.FastBox
    { (default : @EthCLSpecs.Fulu.BeaconState minimal) with
      slot := UInt64.ofNat Const.slotsPerEpoch
      validators := list #[v]
      balances := list balances
      inactivityScores := list scores
      previousEpochParticipation := list #[flags]
      currentEpochParticipation := list #[flags]
      slashings := Vector.ofFn fun i => if i.val = 0 then slashed0 else 0
      depositBalanceToConsume := toConsume }

/-- Run one epoch substep over a fixture, and report whether it rejected with the
constructor `ok` accepts. -/
private def rejectsWith (step : PinM Unit) (s : @State minimal fastHasherTag)
    (ok : StateTransitionError → Bool) : Bool :=
  match step.run s with
  | .error e _ => ok e
  | .ok _ _ => false

private def isOob : StateTransitionError → Bool | .outOfBounds _ _ => true | _ => false
private def isArith : StateTransitionError → Bool | .arithmetic _ => true | _ => false

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

/-- `process_inactivity_updates`: an empty `inactivity_scores` list rejects with
`.outOfBounds`, and a non-participating validator's score at `2**64 - 1` overflows
`+= INACTIVITY_SCORE_BIAS`. -/
private def pinInactivityUpdates : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  rejectsWith processInactivityUpdates (fixture 32000000000 #[32000000000] #[]) isOob &&
  rejectsWith processInactivityUpdates (fixture 32000000000 #[32000000000] #[maxU64]) isArith
example : pinInactivityUpdates = true := by native_decide

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

/-- `weigh_justification_and_finalization`: `previous_target_balance * 3` and
`total_active_balance * 2` overflow `uint64`. The products run before any block-root read,
so the epoch-1 fixture reaches them through a direct call. -/
private def pinJustificationOverflow : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let s := fixture 32000000000 #[32000000000] #[0]
  rejectsWith (weighJustificationAndFinalization 32000000000 maxU64 0) s isArith &&
  rejectsWith (weighJustificationAndFinalization maxU64 0 0) s isArith
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

end EthCLSpecs.Tests.FuluEpochPins
