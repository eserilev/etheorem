import EthCLSpecs.Fulu.RegistryUpdates

/-!
# `EthCLSpecs.Fulu.Rewards`: base-reward and inactivity-leak math (load order row 29)

The reward arithmetic the epoch rewards/penalties and inactivity substeps call:
`get_base_reward_per_increment`, `get_base_reward`, `get_finality_delay`,
`is_in_inactivity_leak` (`SPECS_ARCHITECTURE.md` §3.1 row 29). These read the
derived `get_total_active_balance` (`Accessors`), so they sit above it. Reward
arithmetic runs in `Nat` (matching the pyspec's `int`).
-/

set_option autoImplicit false

open EthCLLib.Spec

namespace EthCLSpecs.Fulu

state_section

/-- `get_base_reward_per_increment`. -/
forkdef getBaseRewardPerIncrement (state : State) : Nat :=
  Const.effectiveBalanceIncrement * Const.baseRewardFactor / isqrt (getTotalActiveBalance state).toNat

/-- `get_base_reward`. Reads `validators[i]`, so it returns `Except IndexError`: an
out-of-range `i` rejects (the pyspec's `IndexError`), where `[i]!` would mask it with a
default. A monadic caller binds it through `liftErr`; a same-error caller binds directly. -/
forkdef getBaseReward (state : State) (i : ValidatorIndex) : Except IndexError Nat := do
  let v ← sszGetIdx (sszGet state validators) i.toNat
  pure ((v.effectiveBalance.toNat / Const.effectiveBalanceIncrement) * getBaseRewardPerIncrement state)

/-- `get_finality_delay` (`phase0/beacon-chain.md:2028`). The spec's `Epoch` subtraction
raises `ValueError` when the finalized epoch is past the previous epoch, so `checkedSub`
rejects that state with `.arithmetic`. -/
forkdef getFinalityDelay (state : State) : Except StateTransitionError Epoch :=
  checkedSub (previousEpochOf state) (sszGet state finalizedCheckpoint).epoch
    "get_finality_delay: get_previous_epoch(state) - state.finalized_checkpoint.epoch"

/-- `is_in_inactivity_leak`. It inherits `getFinalityDelay`'s `.arithmetic` reject, so a
caller binds it where the spec calls it. -/
forkdef isInInactivityLeak (state : State) : Except StateTransitionError Bool := do
  let delay ← getFinalityDelay state
  return decide (delay > Const.minEpochsToInactivityPenalty)

end

end EthCLSpecs.Fulu
