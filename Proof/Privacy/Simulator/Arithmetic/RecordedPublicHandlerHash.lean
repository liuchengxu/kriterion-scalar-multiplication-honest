import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerHash
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The complete hash branch reserve includes the two-block wire output. -/
def recordedPublicHashReserve (count : Nat) (memory : Memory) : Nat := (hashScan count memory).2 + 2616

/-- The complete hash branch implements the sparse source and emits its packed answer. -/
theorem recordedPublicHandler_hashRun [BN254.FieldCertificate] (attempts count : Nat) (memory : Memory)
    (tableFits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run (recordedPublicHandler attempts) (recordedPublicHashReserve count memory) ⟨542, memory⟩ =
      (hashHandlerSamples count memory).map fun result =>
        some (⟨recordedPublicTailLabel result.1, (recordedPublicHashTail result.1).1⟩,
          (recordedPublicHashTail result.1).2 + (result.2 - 1)) := by
  have executed := hashHandlerBlock_continue (recordedPublicHandler attempts) (recordedPublicRedirect ∘ publicHashLabels)
    (recordedPublicHandler_hash attempts) count 772 memory tableFits counter
  dsimp only at executed
  change run (recordedPublicHandler attempts) ((hashScan count memory).2 + 1844 + 772) ⟨542, memory⟩ = _ at executed
  rw [show recordedPublicHashReserve count memory = (hashScan count memory).2 + 1844 + 772 by
    simp [recordedPublicHashReserve, Nat.add_assoc], executed]
  change (hashHandlerSamples count memory).bind _ = (hashHandlerSamples count memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := hashHandlerSamples_cost count memory final cost supported
  let remaining := (hashScan count memory).2 + 1844 + 772 - (cost - 1)
  have enough : 772 ≤ remaining := by dsimp [remaining]; omega
  change (run (recordedPublicHandler attempts) remaining ⟨615, final⟩).map _ = _
  rw [show remaining = 772 + (remaining - 772) by omega, recordedPublicHandler_hashTail, PMF.pure_map]
  rfl

/-- The complete hash branch has a linear concrete instruction budget. -/
theorem recordedPublicHashReserve_bound (count : Nat) (memory : Memory) :
    recordedPublicHashReserve count memory ≤ 6 * count + 2619 := by
  have bound := tableScan_cost count (tableInitial (hashReady (oracleLoaded memory)))
  dsimp [recordedPublicHashReserve, hashScan]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
