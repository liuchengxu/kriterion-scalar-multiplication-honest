import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward branch reserve includes its stored query, overlay, flag check, and wire output. -/
def publicForwardReserve (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  22 + (permutationForwardCost attempts count count (oracleLoaded memory) + (3 + (11 * overlayCount + 393)))

/-- The complete public forward branch implements the stored source and the programmed overlay. -/
theorem publicHandler_forwardRun [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (counter : (oracleLoaded memory).registers 0 = BitVec.ofNat 256 count)
    (overlayCounter : ∀ result ∈ (storedForwardSamples attempts count memory).support,
      result.1.ram (overlayHeader result.1) = BitVec.ofNat 256 overlayCount) :
    run (publicHandler attempts) (publicForwardReserve attempts count overlayCount memory) ⟨102, memory⟩ =
      (storedForwardSamples attempts count memory).map fun result =>
        some (⟨publicTailLabel result.1, (publicForwardTail overlayCount result.1).1⟩,
          (publicForwardTail overlayCount result.1).2 + (result.2 - 1)) := by
  have executed := storedForwardBlock_continue (publicHandler attempts) attempts count (11 * overlayCount + 393)
    publicForwardLabels (publicHandler_forward attempts) memory attemptFits tableFits counter
  dsimp only at executed
  change run (publicHandler attempts) (publicForwardReserve attempts count overlayCount memory)
    ⟨102, memory⟩ = _ at executed
  rw [executed]
  change (storedForwardSamples attempts count memory).bind _ =
    (storedForwardSamples attempts count memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := storedForwardSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  let remaining := publicForwardReserve attempts count overlayCount memory - (cost - 1)
  have enough : 11 * overlayCount + 393 ≤ remaining := by
    dsimp [remaining, publicForwardReserve]
    omega
  change (run (publicHandler attempts) remaining ⟨280, final⟩).map _ = _
  rw [show remaining = 11 * overlayCount + 393 + (remaining - (11 * overlayCount + 393)) by omega,
    publicHandler_forwardTail attempts overlayCount _ final overlayFits (overlayCounter (final, cost) supported),
    PMF.pure_map]
  rfl

/-- The complete public forward branch has a linear concrete instruction budget. -/
theorem publicForwardReserve_bound (attempts count overlayCount : Nat) (memory : Memory) :
    publicForwardReserve attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 511 := by
  have bound := storedForward_budget attempts count memory
  change 178 + 1 + 22 + _ ≤ _ at bound
  dsimp [publicForwardReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
