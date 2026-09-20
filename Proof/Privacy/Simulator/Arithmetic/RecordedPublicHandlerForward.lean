import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerForward
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward branch reserve includes its stored query, overlay, flag check, and wire output. -/
def recordedPublicForwardReserve (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  22 + (permutationForwardCost attempts count count (oracleLoaded memory) + (3 + (11 * overlayCount + 421)))

/-- The complete public forward branch implements the stored source and the programmed overlay. -/
theorem recordedPublicHandler_forwardRun [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    run (recordedPublicHandler attempts) (recordedPublicForwardReserve attempts count overlayCount memory) ⟨102, memory⟩ =
      (storedForwardSamples attempts count memory).map fun result =>
        some (⟨recordedPublicTailLabel result.1, (recordedPublicForwardTail overlayCount result.1).1⟩,
          (recordedPublicForwardTail overlayCount result.1).2 + (result.2 - 1)) := by
  have executed := storedForwardBlock_continue (recordedPublicHandler attempts) attempts count (11 * overlayCount + 421)
    (recordedPublicRedirect ∘ publicForwardLabels) (recordedPublicHandler_forward attempts) memory attemptFits tableFits counter
  dsimp only at executed
  change run (recordedPublicHandler attempts) (recordedPublicForwardReserve attempts count overlayCount memory)
    ⟨102, memory⟩ = _ at executed
  rw [executed]
  change (storedForwardSamples attempts count memory).bind _ =
    (storedForwardSamples attempts count memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := storedForwardSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  let remaining := recordedPublicForwardReserve attempts count overlayCount memory - (cost - 1)
  have enough : 11 * overlayCount + 421 ≤ remaining := by
    dsimp [remaining, recordedPublicForwardReserve]
    omega
  change (run (recordedPublicHandler attempts) remaining ⟨280, final⟩).map _ = _
  rw [show remaining = 11 * overlayCount + 421 + (remaining - (11 * overlayCount + 421)) by omega,
    recordedPublicHandler_forwardTail attempts overlayCount _ final overlayFits (overlayCounter (final, cost) supported),
    PMF.pure_map]
  rfl

/-- The complete public forward branch has a linear concrete instruction budget. -/
theorem recordedPublicForwardReserve_bound (attempts count overlayCount : Nat) (memory : Memory) :
    recordedPublicForwardReserve attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 539 := by
  have bound := storedForward_budget attempts count memory
  change 178 + 1 + 22 + _ ≤ _ at bound
  dsimp [recordedPublicForwardReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
