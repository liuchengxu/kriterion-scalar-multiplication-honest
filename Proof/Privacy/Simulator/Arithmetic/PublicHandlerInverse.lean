import Proof.Privacy.Simulator.Arithmetic.PublicHandlerTail
import Proof.Privacy.Simulator.Arithmetic.StoredHandlerCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The inverse stored branch reserves its body and checked one-block output. -/
def publicInverseStoredReserve (attempts count : Nat) (memory : Memory) : Nat :=
  29 + (permutationForwardCost attempts count count (inverseLoaded memory) + (10 + 386))

/-- The stored inverse branch implements its source and checks the cutoff flag before output. -/
theorem publicHandler_inverseStoredRun [BN254.FieldCertificate] (attempts count : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (counter : (inverseLoaded memory).registers 0 = BitVec.ofNat 256 count) :
    run (publicHandler attempts) (publicInverseStoredReserve attempts count memory) ⟨349, memory⟩ =
      (storedInverseSamples attempts count memory).map fun result =>
        some (⟨publicTailLabel result.1, (publicInverseTail result.1).1⟩,
          (publicInverseTail result.1).2 + (result.2 - 1)) := by
  have executed := storedInverseBlock_continue (publicHandler attempts) attempts count 386
    publicInverseLabels (publicHandler_inverse attempts) memory attemptFits tableFits counter
  dsimp only at executed
  change run (publicHandler attempts) (publicInverseStoredReserve attempts count memory) ⟨349, memory⟩ = _ at executed
  rw [executed]
  change (storedInverseSamples attempts count memory).bind _ = (storedInverseSamples attempts count memory).bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨final, cost⟩
  have bounded := storedInverseSamples_cost attempts count memory final cost attemptFits tableFits counter supported
  let remaining := publicInverseStoredReserve attempts count memory - (cost - 1)
  have enough : 386 ≤ remaining := by dsimp [remaining, publicInverseStoredReserve]; omega
  change (run (publicHandler attempts) remaining ⟨541, final⟩).map _ = _
  rw [show remaining = 386 + (remaining - 386) by omega, publicHandler_inverseTail, PMF.pure_map]
  rfl

/-- The inverse preparation source loads and removes the programmed overlay. -/
def publicInversePrepared (count : Nat) (memory : Memory) : Memory :=
  queryRestored (overlayInverseScan count (oracleLoaded memory)).1

/-- The inverse preparation charges its initial metadata load and query restore. -/
def publicInversePrepareCost (count : Nat) (memory : Memory) : Nat :=
  22 + (overlayInverseScan count (oracleLoaded memory)).2 + 4

/-- The inverse preparation removes the overlay before it enters the stored inverse handler. -/
theorem publicHandler_inversePrepare [BN254.FieldCertificate] (attempts count fuel : Nat)
    (memory : Memory) (fits : count < 2 ^ 256)
    (counter : (oracleLoaded memory).ram (overlayHeader (oracleLoaded memory)) = BitVec.ofNat 256 count) :
    run (publicHandler attempts) (publicInversePrepareCost count memory + fuel) ⟨299, memory⟩ =
      (run (publicHandler attempts) fuel ⟨349, publicInversePrepared count memory⟩).map
        (Option.map fun result => (result.1, result.2 + publicInversePrepareCost count memory)) := by
  have loaded := oracleLoad_continue (publicHandler attempts) publicInverseHeaderLabels
    (publicHandler_inverseHeader attempts) memory
    ((overlayInverseScan count (oracleLoaded memory)).2 + (4 + fuel))
  change run (publicHandler attempts) _ ⟨299, memory⟩ = _ at loaded
  rw [show publicInversePrepareCost count memory + fuel =
      22 + ((overlayInverseScan count (oracleLoaded memory)).2 + (4 + fuel)) by
        dsimp [publicInversePrepareCost]; omega, loaded]
  have scanned := overlayInverse_continue (publicHandler attempts) publicInverseOverlayLoadLabels
    publicInverseOverlayScanLabels (publicHandler_inverseLoad attempts) (publicHandler_inverseScan attempts)
    rfl count (oracleLoaded memory) fits counter (4 + fuel)
  change run (publicHandler attempts) _ ⟨321, oracleLoaded memory⟩ = _ at scanned
  change (run (publicHandler attempts) _ ⟨321, oracleLoaded memory⟩).map _ = _
  rw [scanned]
  have restored := queryRestore_continue (publicHandler attempts) publicQueryRestoreLabels
    (publicHandler_restore attempts) (overlayInverseScan count (oracleLoaded memory)).1 fuel
  change run (publicHandler attempts) (4 + fuel) ⟨345, _⟩ = _ at restored
  change ((run (publicHandler attempts) (4 + fuel) ⟨345, _⟩).map _).map _ = _
  rw [restored]
  simp [publicInversePrepared, publicInversePrepareCost, PMF.map_comp, Option.map_map,
    Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rfl

/-- The complete inverse reserve includes removal of the programmed overlay. -/
def publicInverseReserve (attempts count overlayCount : Nat) (memory : Memory) : Nat :=
  publicInversePrepareCost overlayCount memory +
    publicInverseStoredReserve attempts count (publicInversePrepared overlayCount memory)

/-- The complete inverse branch removes the overlay and emits the stored inverse answer. -/
theorem publicHandler_inverseRun [BN254.FieldCertificate] (attempts count overlayCount : Nat)
    (memory : Memory) (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256)
    (overlayFits : overlayCount < 2 ^ 256)
    (overlayCounter : (oracleLoaded memory).ram (overlayHeader (oracleLoaded memory)) =
      BitVec.ofNat 256 overlayCount)
    (counter : (inverseLoaded (publicInversePrepared overlayCount memory)).registers 0 = BitVec.ofNat 256 count) :
    run (publicHandler attempts) (publicInverseReserve attempts count overlayCount memory) ⟨299, memory⟩ =
      (storedInverseSamples attempts count (publicInversePrepared overlayCount memory)).map fun result =>
        some (⟨publicTailLabel result.1, (publicInverseTail result.1).1⟩,
          (publicInverseTail result.1).2 + (result.2 - 1) + publicInversePrepareCost overlayCount memory) := by
  unfold publicInverseReserve
  rw [publicHandler_inversePrepare attempts overlayCount _ memory overlayFits overlayCounter,
    publicHandler_inverseStoredRun attempts count _ attemptFits tableFits counter, PMF.map_comp]
  rfl

/-- The inverse preparation has linear cost in the stored overlay length. -/
theorem publicInversePrepareCost_bound (count : Nat) (memory : Memory) :
    publicInversePrepareCost count memory ≤ 11 * count + 38 := by
  have bound := overlayInverse_cost count (oracleLoaded memory)
  dsimp [publicInversePrepareCost]
  omega

/-- The complete inverse branch has a linear concrete instruction budget. -/
theorem publicInverseReserve_bound (attempts count overlayCount : Nat) (memory : Memory) :
    publicInverseReserve attempts count overlayCount memory ≤
      2574 * attempts + 33 * count + 11 * overlayCount + 555 := by
  have before := publicInversePrepareCost_bound overlayCount memory
  have after := storedInverse_budget attempts count (publicInversePrepared overlayCount memory)
  change 192 + 1 + 29 + _ ≤ _ at after
  dsimp [publicInverseReserve, publicInverseStoredReserve]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
