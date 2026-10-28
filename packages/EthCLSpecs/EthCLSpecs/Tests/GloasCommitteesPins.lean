import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Tests.GloasCommitteesPins`: the empty-selection pins

The pins for `compute_balance_weighted_selection`'s `assert total > 0`
(`gloas/beacon-chain.md:770`), which no conformance vector reaches. `State` is
FFI-backed, so `native_decide`.

Fires on `lake build EthCLSpecsTests` (`just ethcl-test`).
-/

set_option autoImplicit false

open EthCLLib.Spec
open EthCLLib.PySpecTests
open SizzLean
open SizzLean.Cache
open SizzLean.Hasher

namespace EthCLSpecs.Tests.GloasCommitteesPins

open EthCLSpecs.Gloas

/-- The pins' state-machine monad over the minimal preset and the FFI hasher. -/
private abbrev PinM := EStateM StateTransitionError (@State minimal fastHasherTag)

/-- A minimal Gloas state with one active 32 ETH validator, slashed or not. -/
private def oneValidatorState (slashed : Bool) : @State minimal fastHasherTag :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  let v : Validator :=
    { (default : Validator) with
      effectiveBalance := 32000000000, slashed,
      exitEpoch := Const.farFutureEpoch, withdrawableEpoch := Const.farFutureEpoch }
  SSZ.FastBox
    { (default : @EthCLSpecs.Gloas.BeaconState minimal) with
      validators := ⟨#[v]⟩, balances := ⟨#[32000000000]⟩ }

/-- An empty `indices` rejects with `.assert`. -/
private def pinSelectionEmptyRejects : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match computeBalanceWeightedSelection (oneValidatorState false) #[] ByteArray.empty 1 true with
  | .error (.assert _) => true
  | _ => false
example : pinSelectionEmptyRejects = true := by native_decide

/-- `process_proposer_lookahead` rejects with `.assert` when the only validator is slashed,
and passes when it is not. -/
private def pinProposerLookaheadAllSlashedRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let run (slashed : Bool) := (processProposerLookahead : PinM Unit).run (oneValidatorState slashed)
  (match run true with | .error (.assert _) _ => true | _ => false) &&
  (match run false with | .ok _ _ => true | _ => false)
example : pinProposerLookaheadAllSlashedRejects = true := by native_decide

/-- `process_ptc_window` rejects with `.assert` when a slot has no committee member. One
validator leaves all but one slot empty. -/
private def pinPtcWindowFewActiveRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (processPtcWindow : PinM Unit).run (oneValidatorState false) with
  | .error (.assert _) _ => true
  | _ => false
example : pinPtcWindowFewActiveRejects = true := by native_decide

end EthCLSpecs.Tests.GloasCommitteesPins
