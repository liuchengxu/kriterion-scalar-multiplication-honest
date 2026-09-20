import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerInverse
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The inverse stored branch reserves its body and checked one-block output. -/
def recordedPublicInverseStoredReserve (attempts count : Nat) (memory : Memory) : Nat :=
  29 + (permutationForwardCost attempts count count (inverseLoaded memory) + (10 + 414))

/-- The stored inverse branch implements its source and checks the cutoff flag before output. -/
theorem recordedPublicHandler_inverseStoredRun [BN254.FieldCertificate] (attempts count : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (inverseLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run (recordedPublicHandler attempts) (recordedPublicInverseStoredReserve attempts count memory) ⟨349, memory⟩ =
      (storedInverseSamples attempts count memory).map fun result =>
        some (⟨recordedPublicTailLabel result.1, (recordedPublicInverseTail result.1).1⟩,
          (recordedPublicInverseTail result.1).2 + (result.2 - 1)) := by
  have executed := storedInverseBlock_continue (recordedPublicHandler attempts) attempts count 414
    (recordedPublicRedirect ∘ publicInverseLabels) (recordedPublicHandler_inverse attempts) memory attemptFits tableFits counter
  dsimp only at executed
  change run (recordedPublicHandler attempts) (recordedPublicInverseStoredReserve attempts count memory) ⟨349, memory⟩ = _ at executed
  rw [executed]
  change (storedInverseSamples attempts count memory).bind _ = (storedInverseSamples attempts count memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := storedInverseSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  let remaining := recordedPublicInverseStoredReserve attempts count memory - (cost - 1)
  have enough : 414 ≤ remaining := by dsimp [remaining, recordedPublicInverseStoredReserve]; omega
  change (run (recordedPublicHandler attempts) remaining ⟨541, final⟩).map _ = _
  rw [show remaining = 414 + (remaining - 414) by omega, recordedPublicHandler_inverseTail, PMF.pure_map]
  rfl

/-- The inverse preparation removes the overlay before it enters the stored inverse handler. -/
theorem recordedPublicHandler_inversePrepare [BN254.FieldCertificate] (attempts count fuel : Nat)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).ram (overlayHeader (oracleLoaded memory)) = BitVec.ofNat 256 count) :
    run (recordedPublicHandler attempts) (publicInversePrepareCost count memory + fuel) ⟨299, memory⟩ =
      (run (recordedPublicHandler attempts) fuel ⟨349, publicInversePrepared count memory⟩).map
        (Option.map fun result => (result.1, result.2 + publicInversePrepareCost count memory)) := by
  have loaded := oracleLoad_continue (recordedPublicHandler attempts) (recordedPublicRedirect ∘ publicInverseHeaderLabels)
    (recordedPublicHandler_inverseHeader attempts) memory
    ((overlayInverseScan count (oracleLoaded memory)).2 + (4 + fuel))
  change run (recordedPublicHandler attempts) _ ⟨299, memory⟩ = _ at loaded
  rw [show publicInversePrepareCost count memory + fuel =
      22 + ((overlayInverseScan count (oracleLoaded memory)).2 + (4 + fuel)) by
        dsimp [publicInversePrepareCost]; omega, loaded]
  have scanned := overlayInverse_continue (recordedPublicHandler attempts) (recordedPublicRedirect ∘ publicInverseOverlayLoadLabels)
    (recordedPublicRedirect ∘ publicInverseOverlayScanLabels) (recordedPublicHandler_inverseLoad attempts) (recordedPublicHandler_inverseScan attempts)
    rfl count (oracleLoaded memory) fits counter (4 + fuel)
  change run (recordedPublicHandler attempts) _ ⟨321, oracleLoaded memory⟩ = _ at scanned
  change (run (recordedPublicHandler attempts) _ ⟨321, oracleLoaded memory⟩).map _ = _
  rw [scanned]
  have restored := queryRestore_continue (recordedPublicHandler attempts) (recordedPublicRedirect ∘ publicQueryRestoreLabels)
    (recordedPublicHandler_restore attempts) (overlayInverseScan count (oracleLoaded memory)).1 fuel
  change run (recordedPublicHandler attempts) (4 + fuel) ⟨345, _⟩ = _ at restored
  change ((run (recordedPublicHandler attempts) (4 + fuel) ⟨345, _⟩).map _).map _ = _
  rw [restored]
  simp [publicInversePrepared, publicInversePrepareCost, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rfl

/-- The complete inverse reserve includes removal of the programmed overlay. -/
def recordedPublicInverseReserve (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  publicInversePrepareCost overlayCount memory +
    recordedPublicInverseStoredReserve attempts count (publicInversePrepared overlayCount memory)

/-- The complete inverse branch removes the overlay and emits the stored inverse answer. -/
theorem recordedPublicHandler_inverseRun [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (overlayCounter : (oracleLoaded memory).ram (overlayHeader (oracleLoaded memory)) =
      BitVec.ofNat 256 overlayCount)
    (counter : (inverseLoaded (publicInversePrepared overlayCount memory)).registers 0 = BitVec.ofNat 256 count) :
    run (recordedPublicHandler attempts) (recordedPublicInverseReserve attempts count overlayCount memory) ⟨299, memory⟩ =
      (storedInverseSamples attempts count (publicInversePrepared overlayCount memory)).map fun result =>
        some (⟨recordedPublicTailLabel result.1, (recordedPublicInverseTail result.1).1⟩,
          (recordedPublicInverseTail result.1).2 + (result.2 - 1) + publicInversePrepareCost overlayCount memory) := by
  unfold recordedPublicInverseReserve
  rw [recordedPublicHandler_inversePrepare attempts overlayCount _ memory overlayFits overlayCounter,
    recordedPublicHandler_inverseStoredRun attempts count _ attemptFits tableFits counter, PMF.map_comp]
  rfl

/-- The complete inverse branch has a linear concrete instruction budget. -/
theorem recordedPublicInverseReserve_bound (attempts count overlayCount : Nat) (memory : Memory) :
    recordedPublicInverseReserve attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 583 := by
  have before := publicInversePrepareCost_bound overlayCount memory
  have after := storedInverse_budget attempts count (publicInversePrepared overlayCount memory)
  change 192 + 1 + 29 + _ ≤ _ at after
  dsimp [recordedPublicInverseReserve, recordedPublicInverseStoredReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
