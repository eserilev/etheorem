import EthCLSpecs.Fulu.EpochProcessing

/-!
# `EthCLSpecs.Tests.FuluEpochPins`: the epoch substeps' index and `uint64` faults

The pins cover two rejects: `.outOfBounds` for a per-validator list shorter than the
registry (the pyspec's `IndexError`), and `.arithmetic` for a `uint64` overflow (its
`ValueError`). No conformance vector reaches either. Gloas and Heze inherit the substeps.
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
active from genesis, never participates, and has effective balance `eb`. `balances` and
`inactivityScores` may be shorter than the registry, and `slashings[0] = slashed0`. -/
private def fixture (eb : Gwei) (balances scores : Array UInt64) (slashed0 : Gwei := 0) :
    @State minimal fastHasherTag :=
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
      previousEpochParticipation := list #[0]
      currentEpochParticipation := list #[0]
      slashings := Vector.ofFn fun i => if i.val = 0 then slashed0 else 0 }

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

end EthCLSpecs.Tests.FuluEpochPins
