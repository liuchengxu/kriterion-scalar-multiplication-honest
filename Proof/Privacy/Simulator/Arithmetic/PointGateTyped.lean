import Proof.Privacy.Simulator.Arithmetic.GateCodeTyped
import Proof.Privacy.Simulator.Arithmetic.GateDirectiveSchedule
import Proof.Privacy.Simulator.Arithmetic.RetargetedGateMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security

/-- The thirteen point descriptors read their exact retargeted source records. -/
theorem pointGateCode_typed (sample : RowPublicSample) (input : AffineInput)
    (target : Fin 3 → BaseField) (mac : InputMac) (memory : Memory) (row : Fin FieldMacToECMac.outputMacCount)
    (coordinates : memory.ram (memory.registers 12) = BitVec.ofNat 256 input.x.val ∧
      memory.ram (memory.registers 12 + 1) = BitVec.ofNat 256 input.y.val)
    (labels : WordsAt memory.ram (memory.registers 14) 0 ((encLinkMacWords mac).map (fun label => label.setWidth 256)))
    (x : RetargetedGateMemory (sample.x.coefficients, sample.x.tables, sample.x.quotients, sample.x.targets)
      3 ((sample.x.request.retarget input (target 0)).x9Targets 0) memory.ram (memory.registers 11)
      (1017 + 9158 * row.val + 6105))
    (y : RetargetedGateMemory (sample.y.coefficients, sample.y.tables, sample.y.quotients, sample.y.targets)
      2 ((sample.y.request.retarget input (target 1)).x9Targets 0) memory.ram (memory.registers 11)
      (1017 + 9158 * row.val + 3815))
    (z : RetargetedGateMemory (sample.z.coefficients, sample.z.tables, sample.z.quotients, sample.z.targets)
      4 ((sample.z.request.retarget input (target 2)).x9Targets 0) memory.ram (memory.registers 11)
      (1017 + 9158 * row.val))
    (gate : Fin 12) (bit : Fin 254) :
    ∃ quotient, GateTypedData memory (pointGateCode row gate bit)
      (pointRowDirectiveAt ⟨sample.x.request.retarget input (target 0),
        sample.y.request.retarget input (target 1), sample.z.request.retarget input (target 2)⟩ row input mac gate bit) quotient := by
  have typedX (gate : Fin 4) := xGateCodeAt_typed sample.x input (target 0) mac memory row gate bit
    coordinates labels (x.target gate bit) (x.quotient gate bit) (x.table gate bit)
  have typedY (gate : Fin 3) := yGateCodeAt_typed sample.y input (target 1) mac memory row gate bit
    coordinates labels (y.target gate bit) (y.quotient gate bit) (y.table gate bit)
  have typedZ (gate : Fin 5) := zGateCodeAt_typed sample.z input (target 2) mac memory row gate bit
    coordinates labels (by simpa only [Nat.add_zero] using z.target gate bit)
    (by simpa only [Nat.add_zero] using z.quotient gate bit)
    (by simpa only [Nat.add_zero] using z.table gate bit)
  rcases gate with ⟨gate, bound⟩
  interval_cases gate
  · exact ⟨_, typedX 0⟩
  · exact ⟨_, typedX 1⟩
  · exact ⟨_, typedX 2⟩
  · exact ⟨_, typedX 3⟩
  · exact ⟨_, typedY 0⟩
  · exact ⟨_, typedY 1⟩
  · exact ⟨_, typedY 2⟩
  · exact ⟨_, typedZ 0⟩
  · exact ⟨_, typedZ 1⟩
  · exact ⟨_, typedZ 2⟩
  · exact ⟨_, typedZ 3⟩
  · exact ⟨_, typedZ 4⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
