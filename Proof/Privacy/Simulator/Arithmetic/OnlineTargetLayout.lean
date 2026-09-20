import Proof.Privacy.Simulator.Arithmetic.OnlineMachineSetup
import Proof.Privacy.Simulator.Arithmetic.OutputTargetsBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every sample and correction word is outside the selected-target buffer. -/
theorem onlineSample_targetSeparate (offset target : Nat) (sampleBound : offset < 361) (targetBound : target < 273) :
    BitVec.ofNat 256 (onlineSampleBase + offset) ≠ BitVec.ofNat 256 (onlineTargetBase + target) := by
  have sampleFits : onlineSampleBase + offset < 2 ^ 256 := by
    have bound : onlineSampleBase + 361 < 2 ^ 256 := by decide
    omega
  have targetFits : onlineTargetBase + target < 2 ^ 256 := by
    have bound : onlineTargetBase + 273 < 2 ^ 256 := by decide
    omega
  intro same
  have values := congrArg BitVec.toNat same
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt sampleFits, Nat.mod_eq_of_lt targetFits] at values
  have layout : onlineSampleBase + 361 = onlineTargetBase := onlineBuffer_bounds.2.2.2.1
  omega

/-- The target setup meets the complete correction-point and scale disjointness contract. -/
theorem onlineTargetSetup_separate (memory : Memory) :
    let final := executeLinear onlineTargetSetup memory
    ∀ i, i < 270 → ∀ j, j < 273 →
      final.registers 10 + BitVec.ofNat 256 i ≠ final.registers 13 + BitVec.ofNat 256 j ∧
      final.registers 14 + BitVec.ofNat 256 i ≠ final.registers 13 + BitVec.ofNat 256 j := by
  dsimp only
  intro i first j second
  have setup := onlineTargetSetup_state memory
  rw [setup.2.2.1, setup.2.2.2.2.2, setup.2.2.2.2.1]
  simp only [← BitVec.ofNat_add]
  constructor
  · simpa only [Nat.add_assoc] using onlineSample_targetSeparate (91 + i) j (by omega) second
  · exact onlineSample_targetSeparate i j (by omega) second

/-- The target setup points to the first point after the 91 sampled scales. -/
theorem onlineTargetSetup_pointer (memory : Memory) :
    (executeLinear onlineTargetSetup memory).registers 10 =
      (executeLinear onlineTargetSetup memory).registers 14 + 91 := by
  have setup := onlineTargetSetup_state memory
  rw [setup.2.2.1, setup.2.2.2.2.1, BitVec.ofNat_add]
  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
