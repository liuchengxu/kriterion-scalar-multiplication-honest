import Proof.Privacy.Simulator.Arithmetic.ClampPointBlock
import Proof.Privacy.Simulator.Arithmetic.ClampPointSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The correction load and addition preserve every caller register. -/
theorem clampAdded_caller [BN254.FieldCertificate] (base : Memory) (negative output : BN254.Point)
    (register : Register) (caller : 9 ≤ register.val) :
    (clampAdded base negative output).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  change writePoint (clampLoaded base).registers scalarAccumulator (negative + output) register = _
  rw [writePoint_other _ scalarAccumulator _ register
    (different 2 (by decide)) (different 3 (by decide)) (different 4 (by decide))]
  simp only [clampLoaded, Function.update_of_ne (different 7 (by decide)),
    Function.update_of_ne (different 6 (by decide)), Function.update_of_ne (different 5 (by decide)),
    Function.update_of_ne (different 1 (by decide)), Function.update_of_ne (different 8 (by decide))]

private theorem clampAdded_bits [BN254.FieldCertificate] (base : Memory) (negative output : BN254.Point) :
    (clampAdded base negative output).bits = base.bits := rfl

private theorem clampAdded_ram [BN254.FieldCertificate] (base : Memory) (negative output : BN254.Point) :
    (clampAdded base negative output).ram = base.ram := rfl

private theorem clampCanonical_bits [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) :
    (clampCanonical base point).bits = base.bits := rfl

private theorem clampCanonical_ram [BN254.FieldCertificate] (base : Memory) (point : BN254.Point) :
    (clampCanonical base point).ram = base.ram := rfl

/-- The correction computation preserves RAM, stacks, and all caller registers. -/
theorem clampPointMemory_data [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (current output : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some current) :
    (clampPointMemory base current output).bits = base.bits ∧
    (clampPointMemory base current output).ram = base.ram ∧
    ∀ register : Register, 9 ≤ register.val →
      (clampPointMemory base current output).registers register = base.registers register := by
  have spec := hornerScaled_spec base current input
  have bits (memory : Memory) (point : BN254.Point) : (pointNegationMemory memory point).bits = memory.bits := by
    cases point <;> rfl
  have ram (memory : Memory) (point : BN254.Point) : (pointNegationMemory memory point).ram = memory.ram := by
    cases point <;> rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [clampPointMemory, clampAdded_bits, bits, clampCanonical_bits]
    exact spec.2.1
  · rw [clampPointMemory, clampAdded_ram, ram, clampCanonical_ram]
    exact spec.2.2.1
  · intro register caller
    have different (target : Register) (small : target.val < 9) : register ≠ target := by
      intro same; have value := congrArg Fin.val same; omega
    rw [clampPointMemory, clampAdded_caller _ _ _ register caller,
      pointNegationMemory_register _ _ register (different 0 (by decide)) (different 4 (by decide)),
      clampCanonical_caller _ _ register caller, spec.2.2.2 register caller]

end Kriterion.ArgoMAC.ArithmeticSimulator
