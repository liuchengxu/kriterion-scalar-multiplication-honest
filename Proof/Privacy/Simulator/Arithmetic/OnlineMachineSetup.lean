import Proof.Privacy.Simulator.Arithmetic.OnlineMachine

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The original-label setup retains RAM and stacks and installs all three fixed pointers. -/
theorem onlineOriginalSetup_state (memory : Memory) :
    let final := executeLinear onlineOriginalSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 11 = BitVec.ofNat 256 privateBase ∧
    final.registers 12 = BitVec.ofNat 256 onlineInputBase ∧
    final.registers 14 = BitVec.ofNat 256 onlineOriginalBase := by
  simp [onlineOriginalSetup, executeLinear, LinearInstruction.execute]

/-- The target setup installs the scale, point, input, and destination pointers.
The first point word follows the 91 scale words `onlineWords` stores. -/
theorem onlineTargetSetup_state (memory : Memory) :
    let final := executeLinear onlineTargetSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 10 = BitVec.ofNat 256 (onlineSampleBase + 91) ∧
    final.registers 11 = BitVec.ofNat 256 onlineInputBase ∧
    final.registers 14 = BitVec.ofNat 256 onlineSampleBase ∧
    final.registers 13 = BitVec.ofNat 256 onlineTargetBase := by
  simp [onlineTargetSetup, executeLinear, LinearInstruction.execute]

/-- The retarget setup installs the source, input, and selected-target pointers. -/
theorem onlineRetargetSetup_state (memory : Memory) :
    let final := executeLinear onlineRetargetSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 11 = BitVec.ofNat 256 privateBase ∧
    final.registers 12 = BitVec.ofNat 256 onlineInputBase ∧
    final.registers 14 = BitVec.ofNat 256 onlineTargetBase := by
  simp [onlineRetargetSetup, executeLinear, LinearInstruction.execute]

/-- The link setup loads the original labels, both coordinate words, and the bridge key. -/
theorem onlineLinkSetup_state (memory : Memory) :
    let final := executeLinear onlineLinkSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 11 = BitVec.ofNat 256 onlineOriginalBase ∧
    final.registers 14 = BitVec.ofNat 256 onlineLinkedBase ∧
    final.registers 12 = memory.ram (BitVec.ofNat 256 onlineInputBase) ∧
    final.registers 13 = memory.ram (BitVec.ofNat 256 (onlineInputBase + 1)) ∧
    final.registers 8 = memory.ram (BitVec.ofNat 256 privateBase) := by
  simp [onlineLinkSetup, executeLinear, LinearInstruction.execute]

/-- The point setup selects the transformed-label buffer for all point gates. -/
theorem onlinePointSetup_state (memory : Memory) :
    let final := executeLinear onlinePointSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 11 = BitVec.ofNat 256 privateBase ∧
    final.registers 12 = BitVec.ofNat 256 onlineInputBase ∧
    final.registers 14 = BitVec.ofNat 256 onlineLinkedBase := by
  simp [onlinePointSetup, executeLinear, LinearInstruction.execute]

/-- The final output setup returns to the original offline labels. -/
theorem onlineLabelSetup_state (memory : Memory) :
    let final := executeLinear onlineLabelSetup memory
    final.ram = memory.ram ∧ final.bits = memory.bits ∧
    final.registers 11 = BitVec.ofNat 256 privateBase ∧
    final.registers 12 = BitVec.ofNat 256 onlineInputBase := by
  simp [onlineLabelSetup, executeLinear, LinearInstruction.execute]

/-- The fixed buffers occupy separate consecutive private intervals.
Five words hold the input record, 361 the sampled words, 273 the target rows
(91 rows of three coordinates), and 508 each label buffer. -/
theorem onlineBuffer_bounds :
    256 ≤ privateBase ∧ privateBase + 838208 = onlineInputBase ∧
    onlineInputBase + 5 = onlineSampleBase ∧ onlineSampleBase + 361 = onlineTargetBase ∧
    onlineTargetBase + 273 = onlineOriginalBase ∧ onlineOriginalBase + 508 = onlineLinkedBase ∧
    onlineLinkedBase + 508 < 2 ^ 96 := by
  decide

end Kriterion.ArgoMAC.ArithmeticSimulator
