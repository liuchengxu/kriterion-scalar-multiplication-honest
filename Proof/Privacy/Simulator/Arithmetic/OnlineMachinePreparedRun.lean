import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrepare
import Proof.Privacy.Simulator.Arithmetic.OnlineMachineLink

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The common selected-path allowance bounds private preparation and every oracle phase. -/
def onlineSelectedReserve (attempts limit : Nat) (state : SparseOracleFamily) : Nat :=
  1678841 + (6 * state.hash.length + 9056 + encLinkLoopBudget attempts limit 508 + onlineGateReserve attempts limit)

/-- The selected source charges private preparation before the public oracle source. -/
noncomputable def onlinePreparedSamples [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool) :
    PMF (Configuration 290305300 × Nat) :=
  (onlineLinkSamples attempts (onlinePreparedMemory memory output sample) state key suffix).map
    fun result => (result.1, result.2 + onlinePrepareCost sample)

/-- The selected-path reserve bounds every actual preparation and link allowance. -/
theorem onlineSelectedReserve_enough [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) (state : SparseOracleFamily) :
    onlinePrepareCost sample + (encLinkReserve attempts limit 0 (onlinePreparedMemory memory output sample) state +
      onlineGateReserve attempts limit) ≤ onlineSelectedReserve attempts limit state := by
  have preparation := onlinePrepareCost_bound sample
  have link := encLinkReserve_bound attempts limit 0 (onlinePreparedMemory memory output sample) state
  change 7468 + encLinkReserve attempts limit 0 (onlinePreparedMemory memory output sample) state ≤
    6 * state.hash.length + 16524 + encLinkLoopBudget attempts limit 508 + 0 at link
  unfold onlineSelectedReserve
  omega

/-- The actual selected preparation and oracle phases share one uniform reserve. -/
theorem onlineMachine_preparedRun [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts limit : Nat) (memory : Memory) (output : BN254.Point)
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (state : SparseOracleFamily) (key : BN254.BaseField) (suffix : List Bool)
    (attemptFits : attempts < 2 ^ 256)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 onlineSampleBase) 0 (onlineWords sample))
    (selected : selectedOutputPoint memory.ram (BitVec.ofNat 256 onlineInputBase) = some output)
    (ready : OnlineLinkReady attempts limit (onlinePreparedMemory memory output sample) state key suffix) :
    ClosedRun (onlineMachine attempts) 22393 memory (onlineSelectedReserve attempts limit state)
      (onlinePreparedSamples attempts memory output sample state key suffix) := by
  have preparation := onlineMachine_prepare attempts memory output sample stored selected
  have link := onlineMachine_linkRun attempts limit (onlinePreparedMemory memory output sample) state key suffix attemptFits ready
  have combined := preparation.close _ _ _ _ _ _ _ _ link
  exact combined.mono _ _ _ _ _ _ (onlineSelectedReserve_enough attempts limit memory output sample state)

end Kriterion.ArgoMAC.ArithmeticSimulator
