import EthCLSpecs.Gloas.EpochProcessing

/-!
# `EthCLSpecs.Tests.GloasCommitteesPins`: the empty-candidate selection pins

`compute_balance_weighted_selection` opens with `assert total > 0`
(`gloas/beacon-chain.md:770`). No conformance vector reaches an empty candidate set, so
the `#guard`-style pins here lock the reject and the two epoch substeps that surface it:

- the proposer lookahead, whose Gloas candidates are the *unslashed* active validators
  (EIP-8045), so a registry whose active validators are all slashed has none;
- the PTC window, whose candidates for a slot are that slot's beacon committees, so a
  registry with fewer active validators than `SLOTS_PER_EPOCH` leaves some slot empty.

A last pin locks the sampler's loop bound, the spec's `uint64` counter.

Each fixture is one validator, active from genesis with a 32 ETH effective balance. The
unslashed lookahead runs clean, so the reject in the slashed case is the empty candidate
set and not the fixture. `State` is FFI-backed, so `native_decide`.

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

/-- A minimal Gloas state at slot 0 whose registry is one validator, active from genesis
with a 32 ETH effective balance, slashed or not. -/
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

/-- `compute_balance_weighted_selection` over no candidates rejects with `.assert`. -/
private def pinSelectionEmptyRejects : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  match computeBalanceWeightedSelection (oneValidatorState false) #[] ByteArray.empty 1 true with
  | .error (.assert _) => true
  | _ => false
example : pinSelectionEmptyRejects = true := by native_decide

/-- `process_proposer_lookahead` rejects with `.assert` when every active validator is
slashed, and runs clean on the same registry unslashed. -/
private def pinProposerLookaheadAllSlashedRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  let run (slashed : Bool) := (processProposerLookahead : PinM Unit).run (oneValidatorState slashed)
  (match run true with | .error (.assert _) _ => true | _ => false) &&
  (match run false with | .ok _ _ => true | _ => false)
example : pinProposerLookaheadAllSlashedRejects = true := by native_decide

/-- `process_ptc_window` rejects with `.assert` when fewer validators are active than
`SLOTS_PER_EPOCH`: one validator fills one slot's committee and leaves the others empty. -/
private def pinPtcWindowFewActiveRejects : Bool :=
  letI : Preset := minimal
  letI : Config := minimalConfig
  letI : HasherTag := fastHasherTag
  match (processPtcWindow : PinM Unit).run (oneValidatorState false) with
  | .error (.assert _) _ => true
  | _ => false
example : pinPtcWindowFewActiveRejects = true := by native_decide

/-- The sampler's bound is the spec's `uint64` counter: with no passes left (fuel `0`, the
counter past `2**64 - 1`) the walk raises the `.arithmetic` fault of the spec's `i += 1`,
never a short selection. A selection already full returns before spending a pass. -/
private def pinSamplerCounterOverflow : Bool :=
  letI : Preset := minimal
  letI : HasherTag := fastHasherTag
  (match cbwsAux #[] #[] #[] ByteArray.empty 1 1 false 0 0 ByteArray.empty #[] with
    | .error (.arithmetic _) => true | _ => false) &&
  (match cbwsAux #[] #[] #[] ByteArray.empty 1 1 false 1 0 ByteArray.empty #[7] with
    | .ok sel => sel == #[7] | _ => false)
#guard pinSamplerCounterOverflow

end EthCLSpecs.Tests.GloasCommitteesPins
