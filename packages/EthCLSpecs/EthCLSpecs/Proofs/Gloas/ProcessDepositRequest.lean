import EthCLSpecs.Gloas.Operations
import EthCLSpecs.Proofs.Gloas.Run
import EthCLLib.Proofs.Run

/-!
# `EthCLSpecs.Proofs.Gloas.ProcessDepositRequest`: the whole-transition equation

`EthCLSpecs.Gloas.processDepositRequest` (inherited from Fulu) appends one
`PendingDeposit` to the queue, stamped with the current slot, and writes nothing else.
Fulu removed the Electra write of `deposit_requests_start_index`. The record update in
`processDepositRequest_run` leaves that field out, so the theorem states that the run
keeps it.

Statements bind plain `BeaconState` values. The run reads `pureState preState`.
-/

set_option autoImplicit false

namespace EthCLSpecs.Proofs.Gloas

open EthCLLib.Spec
open EthCLLib.Proofs (pureState runPure runPure_of_run_ok)
open EthCLSpecs.Gloas (Slot Preset BeaconState DepositRequest PendingDeposit processDepositRequest)

/-- The pending deposit that `processDepositRequest` appends for `dr` at `slot`. -/
def depositRequestPending [Preset] (dr : DepositRequest) (slot : Slot) : PendingDeposit :=
  { pubkey := dr.pubkey, withdrawalCredentials := dr.withdrawalCredentials,
    amount := dr.amount, signature := dr.signature, slot }

/-- Exact whole-transition contract for `processDepositRequest`: the run on
`pureState preState` appends `depositRequestPending dr preState.slot` to
`pendingDeposits`, and every other field, `depositRequestsStartIndex` included, keeps its
value. -/
@[characterizes EthCLSpecs.Gloas.processDepositRequest]
theorem processDepositRequest_run [Preset] [HasherTag] (preState : BeaconState)
    (dr : DepositRequest) :
    (processDepositRequest (StateTransition := GloasRun) dr).run (pureState preState)
      = .ok ((), pureState { preState with
          pendingDeposits := preState.pendingDeposits.push
            (depositRequestPending dr preState.slot) }) := rfl

/-- The run keeps `deposit_requests_start_index`. -/
theorem processDepositRequest_keeps_startIndex [Preset] [HasherTag] (preState : BeaconState)
    (dr : DepositRequest) :
    (runPure (processDepositRequest (StateTransition := GloasRun) dr) preState).map
        (fun r => r.2.depositRequestsStartIndex)
      = .ok preState.depositRequestsStartIndex := by
  rw [runPure_of_run_ok (processDepositRequest_run preState dr)]
  rfl

end EthCLSpecs.Proofs.Gloas
