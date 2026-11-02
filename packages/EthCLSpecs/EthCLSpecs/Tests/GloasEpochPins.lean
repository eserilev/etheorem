import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Tests.GloasEpochPins`: the Gloas `process_pending_deposits` faults

Gloas overrides `process_pending_deposits` (`gloas/beacon-chain.md:1659-1713`) to draw on
`get_activation_churn_limit`, so its `uint64` sums are a separate copy from Fulu's, and
`Tests/FuluEpochPins.lean` does not reach them. Heze inherits this copy. The pins cover the
three `.arithmetic` rejects, the pyspec's `ValueError`, which no conformance vector reaches.
`State` is FFI-backed, so `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasEpochPins

open EthCLSpecs.Gloas

/-- The pins' state-machine monad over the minimal preset and the FFI hasher. -/
private abbrev PinM := EStateM StateTransitionError (@State minimal fastHasherTag)

/-- A minimal Gloas state at slot 0 with one active 32 ETH validator and a 32 ETH balance.
`deposit_balance_to_consume = toConsume`, `finalized_checkpoint.epoch = finalized`, and
`pending_deposits = deposits`. -/
private def fixture (toConsume : Gwei := 0) (finalized : Epoch := 0)
    (deposits : Array (@PendingDeposit minimal) := #[]) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  SSZ.FastBox
    { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
      validators := ⟨#[v]⟩, balances := ⟨#[32000000000]⟩
      depositBalanceToConsume := toConsume
      finalizedCheckpoint := { epoch := finalized, root := default }
      pendingDeposits := ⟨deposits⟩ }

/-- Run `process_pending_deposits` over a fixture, and report whether it rejected with
`.arithmetic` at the operation `descr` names. -/
private def rejectsAt (s : @State minimal fastHasherTag) (descr : String) : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  letI : CryptoBackend := CryptoBackend.realBackend
  match (processPendingDeposits : PinM Unit).run s with
  | .error (.arithmetic d) _ => d == descr
  | _ => false

private def maxU64 : UInt64 := 0xFFFFFFFFFFFFFFFF

/-- `deposit_balance_to_consume + get_activation_churn_limit(state)` overflows when the
carried churn is `2**64 - 1` (`gloas/beacon-chain.md:1663`). -/
private def pinChurnBudgetOverflow : Bool :=
  rejectsAt (fixture (toConsume := maxU64))
    "process_pending_deposits: deposit_balance_to_consume + get_activation_churn_limit(state)"
example : pinChurnBudgetOverflow = true := by native_decide

/-- `compute_start_slot_at_epoch` overflows on a finalized epoch of `2**61`, since minimal
`SLOTS_PER_EPOCH` is 8 (`gloas/beacon-chain.md:1668`). -/
private def pinFinalizedSlotOverflow : Bool :=
  rejectsAt (fixture (finalized := 0x2000000000000000))
    "process_pending_deposits: compute_start_slot_at_epoch(state.finalized_checkpoint.epoch)"
example : pinFinalizedSlotOverflow = true := by native_decide

/-- Two top-ups to the fixture's own pubkey, `1` then `2**64 - 1`. The first fits the churn
and applies as a balance top-up, with no signature check. The second overflows
`processed_amount + deposit.amount` (`gloas/beacon-chain.md:1696`). -/
private def pinChurnSumOverflow : Bool :=
  letI : Preset := minimal
  let topUp (amount : Gwei) : PendingDeposit := { (default : PendingDeposit) with amount }
  rejectsAt (fixture (deposits := #[topUp 1, topUp maxU64]))
    "process_pending_deposits: processed_amount + deposit.amount"
example : pinChurnSumOverflow = true := by native_decide

end EthCLSpecs.Tests.GloasEpochPins
