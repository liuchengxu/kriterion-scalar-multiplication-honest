import Proof.Privacy.Simulator.Arithmetic.OverlayPairs
import Proof.Privacy.Simulator.Arithmetic.SwapBlock
import Proof.Privacy.Simulator.Arithmetic.ReverseSwapBlock
import Proof.Privacy.Simulator.Arithmetic.KnownQuery

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The forward overlay source applies the ascending swap table. -/
def overlayForwardScan (count : Nat) (memory : Memory) : Memory × Nat :=
  let scanned := swapScan count (swapInitial (overlayLoaded memory))
  (scanned.1, scanned.2 + 5)

/-- The inverse overlay source applies the same table in reverse order. -/
def overlayInverseScan (count : Nat) (memory : Memory) : Memory × Nat :=
  let scanned := reverseSwapScan count (reverseSwapInitial (overlayInverseLoaded memory))
  (scanned.1, scanned.2 + 10)

/-- The host loads and applies the forward overlay before its continuation. -/
theorem overlayForward_continue [BN254.FieldCertificate] (host : Machine)
    (loadLabels : Nat → Fin (host.size + 1)) (scanLabels : Fin 14 → Fin (host.size + 1))
    (loader : ContainsLinear host overlayLoad loadLabels) (scanner : ContainsSwapTable host scanLabels)
    (joined : loadLabels 5 = scanLabels 0) (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 count)
    (fuel : Nat) :
    run host ((overlayForwardScan count memory).2 + fuel) ⟨loadLabels 0, memory⟩ =
      (run host fuel ⟨scanLabels 13, (overlayForwardScan count memory).1⟩).map
        (Option.map fun result => (result.1, result.2 + (overlayForwardScan count memory).2)) := by
  unfold overlayForwardScan
  dsimp only
  rw [show (swapScan count (swapInitial (overlayLoaded memory))).2 + 5 + fuel =
    5 + ((swapScan count (swapInitial (overlayLoaded memory))).2 + fuel) by omega,
    overlayLoad_continue host loadLabels loader, joined,
    swapBlock_continue host scanLabels scanner count (overlayLoaded memory) fits
      (by simp [overlayLoaded, counter]) fuel]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The host loads and removes the overlay before its inverse-query continuation. -/
theorem overlayInverse_continue [BN254.FieldCertificate] (host : Machine)
    (loadLabels : Nat → Fin (host.size + 1)) (scanLabels : Fin 15 → Fin (host.size + 1))
    (loader : ContainsLinear host overlayInverseLoad loadLabels)
    (scanner : ContainsReverseSwapTable host scanLabels)
    (joined : loadLabels 9 = scanLabels 0) (count : Nat) (memory : Memory)
    (fits : count < 2 ^ 256) (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 count)
    (fuel : Nat) :
    run host ((overlayInverseScan count memory).2 + fuel) ⟨loadLabels 0, memory⟩ =
      (run host fuel ⟨scanLabels 13, (overlayInverseScan count memory).1⟩).map
        (Option.map fun result => (result.1, result.2 + (overlayInverseScan count memory).2)) := by
  unfold overlayInverseScan
  dsimp only
  rw [show (reverseSwapScan count (reverseSwapInitial (overlayInverseLoaded memory))).2 + 10 + fuel =
    9 + ((reverseSwapScan count (reverseSwapInitial (overlayInverseLoaded memory))).2 + 1 + fuel) by omega,
    overlayInverseLoad_continue host loadLabels loader, joined,
    reverseSwapBlock_continue host scanLabels scanner count (overlayInverseLoaded memory) fits
      (by simp [overlayInverseLoaded, overlayReverseReady, overlayLoaded, counter]) fuel]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The forward overlay result agrees with the programmed source permutation. -/
theorem overlayForward_source (memory : Memory) (pairs : List (Word × Word))
    (represented : RepresentsPairs memory.ram (overlayHeader memory + 256#256) pairs) :
    (overlayForwardScan pairs.length memory).1.registers 8 =
      Security.OperationalOracle.swaps pairs (memory.registers 8) := by
  simp only [overlayForwardScan, swapScan_source]
  simpa [swapInitial, overlayLoaded] using applyTableSwaps_source pairs memory.ram
    (overlayHeader memory + 256#256) (memory.registers 8) represented

/-- The inverse overlay result agrees with the inverse programmed source permutation. -/
theorem overlayInverse_source (memory : Memory) (pairs : List (Word × Word))
    (counter : memory.ram (overlayHeader memory) = BitVec.ofNat 256 pairs.length)
    (represented : RepresentsPairs memory.ram (overlayHeader memory + 256#256) pairs) :
    (overlayInverseScan pairs.length memory).1.registers 8 =
      (Security.OperationalOracle.swaps pairs).symm (memory.registers 8) := by
  simp only [overlayInverseScan, reverseSwapScan_source]
  simpa [reverseSwapInitial, overlayInverseLoaded, overlayReverseReady, overlayLoaded, counter,
    ← BitVec.ofNat_mul, Nat.mul_comm] using applyReverseTableSwaps_inverse pairs memory.ram
    (overlayHeader memory + 256#256) (memory.registers 8) represented

/-- The forward overlay preserves the RAM, bits, and caller registers below eight. -/
theorem overlayForward_data (count : Nat) (memory : Memory) :
    (overlayForwardScan count memory).1.ram = memory.ram ∧
    (overlayForwardScan count memory).1.bits = memory.bits ∧
    ∀ register : Register, register.val < 8 →
      (overlayForwardScan count memory).1.registers register = memory.registers register := by
  refine ⟨(swapScan_data _ _).2, (swapScan_data _ _).1, ?_⟩
  intro register small
  rw [show (overlayForwardScan count memory).1 = (swapScan count (swapInitial (overlayLoaded memory))).1 from rfl,
    swapScan_caller _ _ register small]
  have a : register ≠ 9 := by intro equal; subst register; simp at small
  have b : register ≠ 10 := by intro equal; subst register; simp at small
  have c : register ≠ 14 := by intro equal; subst register; simp at small
  simp [swapInitial, overlayLoaded, a, b, c]

/-- The inverse overlay preserves the RAM, bits, and caller registers below eight. -/
theorem overlayInverse_data (count : Nat) (memory : Memory) :
    (overlayInverseScan count memory).1.ram = memory.ram ∧
    (overlayInverseScan count memory).1.bits = memory.bits ∧
    ∀ register : Register, register.val < 8 →
      (overlayInverseScan count memory).1.registers register = memory.registers register := by
  refine ⟨(reverseSwapScan_data _ _).2, (reverseSwapScan_data _ _).1, ?_⟩
  intro register small
  rw [show (overlayInverseScan count memory).1 =
    (reverseSwapScan count (reverseSwapInitial (overlayInverseLoaded memory))).1 from rfl,
    reverseSwapScan_caller _ _ register small]
  have a : register ≠ 9 := by intro equal; subst register; simp at small
  have b : register ≠ 10 := by intro equal; subst register; simp at small
  have c : register ≠ 14 := by intro equal; subst register; simp at small
  have d : register ≠ 15 := by intro equal; subst register; simp at small
  simp [reverseSwapInitial, overlayInverseLoaded, overlayReverseReady, overlayLoaded, a, b, c, d]

/-- The forward overlay has linear cost in its stored pair count. -/
theorem overlayForward_cost (count : Nat) (memory : Memory) :
    (overlayForwardScan count memory).2 ≤ 11 * count + 7 := by
  have bound := (swapScan_cost count (swapInitial (overlayLoaded memory))).2
  dsimp [overlayForwardScan]
  omega

/-- The inverse overlay has linear cost in its stored pair count. -/
theorem overlayInverse_cost (count : Nat) (memory : Memory) :
    (overlayInverseScan count memory).2 ≤ 11 * count + 12 := by
  have bound := (reverseSwapScan_cost count (reverseSwapInitial (overlayInverseLoaded memory))).2
  dsimp [overlayInverseScan]
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
