import Proof.Privacy.Simulator.Arithmetic.OnlineInputNull

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- The input reader preserves its destination register. -/
theorem onlineReadStored_base (base : Memory) (width value : Nat) (offset : Word) (rest : List Bool) :
    (onlineReadStored base width value offset rest).registers 10 = base.registers 10 := by
  simp only [onlineReadStored, onlineStored, Function.update_of_ne (by decide : (10 : Register) ≠ 8),
    Function.update_of_ne (by decide : (10 : Register) ≠ 15)]
  exact inputFinal_caller base _ rest 10 (by decide)

/-- The input reader writes exactly one decoded word to RAM. -/
theorem onlineReadStored_ram (base : Memory) (width value : Nat) (offset : Word) (rest : List Bool)
    (fits : value < 2 ^ width) :
    (onlineReadStored base width value offset rest).ram =
      Function.update base.ram (base.registers 10 + offset) (BitVec.ofNat 256 value) := by
  simp only [onlineReadStored, onlineStored, decodedInput_value base width value rest fits]
  rw [show (decodedInput base width value rest).registers 10 = base.registers 10 from
    inputFinal_caller base _ rest 10 (by decide)]
  rfl

/-- The input reader preserves the unread suffix. -/
theorem onlineReadStored_bits (base : Memory) (width value : Nat) (offset : Word) (rest : List Bool) :
    (onlineReadStored base width value offset rest).bits 0 = rest := rfl

/-- The common prefix writes the two input coordinates and the output tag. -/
theorem onlineTaggedMemory_ram (base : Memory) (x y tag : Nat) (rest : List Bool)
    (xFits : x < 2 ^ 254) (yFits : y < 2 ^ 254) (tagFits : tag < 2 ^ 2) :
    (onlineTaggedMemory base x y tag rest).ram =
      Function.update (Function.update (Function.update base.ram
        (base.registers 10) (BitVec.ofNat 256 x))
        (base.registers 10 + 1) (BitVec.ofNat 256 y))
        (base.registers 10 + 2) (BitVec.ofNat 256 tag) := by
  simp only [onlineTaggedMemory, onlineReadStored_ram _ _ _ _ _ tagFits,
    onlineReadStored_ram _ _ _ _ _ yFits, onlineReadStored_ram _ _ _ _ _ xFits,
    onlineReadStored_base, add_zero]

/-- The five-word RAM record contains both coordinates, the tag, and the output coordinates. -/
def onlineRecordRam (base : Memory) (x y tag outX outY : Nat) : Word → Word :=
  Function.update (Function.update (Function.update (Function.update (Function.update base.ram
    (base.registers 10) (BitVec.ofNat 256 x))
    (base.registers 10 + 1) (BitVec.ofNat 256 y))
    (base.registers 10 + 2) (BitVec.ofNat 256 tag))
    (base.registers 10 + 3) (BitVec.ofNat 256 outX))
    (base.registers 10 + 4) (BitVec.ofNat 256 outY)

/-- The affine path has the exact five-word RAM record. -/
theorem onlineAffineMemory_values (base : Memory) (x y outX outY : Nat) (rest : List Bool)
    (xFits : x < 2 ^ 254) (yFits : y < 2 ^ 254)
    (outXFits : outX < 2 ^ 254) (outYFits : outY < 2 ^ 254) :
    let result := onlineAffineMemory base x y outX outY rest
    result.ram = onlineRecordRam base x y 1 outX outY ∧
    result.registers 10 = base.registers 10 ∧ result.bits 0 = rest := by
  dsimp only
  refine ⟨?_, ?_, rfl⟩
  · simp only [onlineAffineMemory, onlineReadStored_ram _ _ _ _ _ outYFits,
      onlineReadStored_ram _ _ _ _ _ outXFits, onlineReadStored_base,
      onlineBranchMemory, Function.update_of_ne (by decide : (10 : Register) ≠ 6),
      Function.update_of_ne (by decide : (10 : Register) ≠ 15),
      onlineTaggedMemory_ram base x y 1 _ xFits yFits (by decide)]
    simp only [onlineTaggedMemory, onlineReadStored_base, onlineRecordRam]
  · simp [onlineAffineMemory, onlineReadStored_base, onlineBranchMemory,
      onlineTaggedMemory]

/-- The null path stores zeros for both unused output coordinates. -/
theorem onlineNullMemory_values (base : Memory) (x y tag : Nat) (rest : List Bool)
    (xFits : x < 2 ^ 254) (yFits : y < 2 ^ 254) (tagFits : tag < 2 ^ 2) :
    let result := onlineNullMemory base x y tag rest
    result.ram = onlineRecordRam base x y tag 0 0 ∧
    result.registers 10 = base.registers 10 ∧ result.bits 0 = rest := by
  dsimp only
  simp only [onlineNullMemory, onlineInputZero, executeLinear, LinearInstruction.execute,
    Arithmetic.eval, onlineBranchMemory]
  simp only [onlineTaggedMemory_ram base x y tag rest xFits yFits tagFits]
  simp [onlineRecordRam, onlineTaggedMemory, onlineReadStored_base, onlineReadStored_bits]

end Kriterion.ArgoMAC.ArithmeticSimulator
