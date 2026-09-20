import Proof.Privacy.Simulator.Arithmetic.OutputTargetsCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The complete Horner block retains its initialized zero register. -/
theorem pointHornerMemory_zero [BN254.FieldCertificate] [BN254.GroupCertificate]
    (points : List BN254.Point) (base : Memory) : (pointHornerMemory points base).registers 9 = 0 := by
  have spec := hornerPrefixMemory_spec points points.length (Nat.le_refl _)
    (hornerInitial base) (hornerInitial_point base)
  rw [pointHornerMemory, spec.2.2.2 9 (by decide)]
  simp [hornerInitial]

/-- Canonical RAM words decode to the same point. -/
theorem StoredPointEncoding.read [BN254.FieldCertificate] (ram : Word → Word) (address : Word)
    (point : BN254.Point) (encoded : StoredPointEncoding ram address point) :
    storedPoint ram address = some point := by
  apply Eq.trans _ (scalarMultiple_write (fun _ => 0) point)
  apply readPoint_congr <;> cases point <;>
    simp_all [storedPoint, StoredPointEncoding, scalarMultiple, scalarAccumulator, writePoint]

/-- The prepared row memory includes the Horner and correction blocks. -/
def outputTargetsPrepared [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) : Memory :=
  targetScalePointer (clampPointMemory (pointHornerMemory (Vector.ofFn sample.1).toList base)
    (pointHorner radix (Vector.ofFn sample.1).toList) output)

/-- The complete target memory records the original target source in RAM. -/
def outputTargetsMemory [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) : Memory :=
  outputTargetRowsMemory (outputTargetsPrepared base output sample) output sample

private theorem targetScalePointer_bits (base : Memory) : (targetScalePointer base).bits = base.bits := rfl

private theorem targetScalePointer_ram (base : Memory) : (targetScalePointer base).ram = base.ram := rfl

/-- The prepared memory preserves RAM and protocol stacks. -/
theorem outputTargetsPrepared_data [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (outputTargetsPrepared base output sample).bits = base.bits ∧
    (outputTargetsPrepared base output sample).ram = base.ram := by
  have horner := pointHornerMemory_spec (Vector.ofFn sample.1).toList base
  have correction := clampPointMemory_data _ _ output horner.1
  constructor
  · rw [outputTargetsPrepared, targetScalePointer_bits, correction.1, horner.2.1]
  · rw [outputTargetsPrepared, targetScalePointer_ram, correction.2.1, horner.2.2.1]

/-- The prepared memory preserves each caller register outside its fixed working registers. -/
theorem outputTargetsPrepared_caller [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (register : Register) (caller : 9 ≤ register.val) (notNine : register ≠ 9)
    (notEleven : register ≠ 11) (notTwelve : register ≠ 12) :
    (outputTargetsPrepared base output sample).registers register = base.registers register := by
  have horner := pointHornerMemory_spec (Vector.ofFn sample.1).toList base
  have correction := clampPointMemory_data _ _ output horner.1
  simp only [outputTargetsPrepared, targetScalePointer, Function.update_of_ne notEleven]
  exact (correction.2.2 register caller).trans (horner.2.2.2 register caller notNine notTwelve)

/-- The prepared memory selects the sampled scale pointer. -/
theorem outputTargetsPrepared_scale [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (outputTargetsPrepared base output sample).registers 11 = base.registers 14 := by
  have horner := pointHornerMemory_spec (Vector.ofFn sample.1).toList base
  have correction := clampPointMemory_data _ _ output horner.1
  simp only [outputTargetsPrepared, targetScalePointer, Function.update_self]
  rw [correction.2.2 14 (by decide), correction.2.2 9 (by decide),
    pointHornerMemory_zero, horner.2.2.2 14 (by decide) (by decide) (by decide)]
  simp

/-- The prepared memory retains the exact correction point. -/
theorem outputTargetsPrepared_encoding [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    PointAccumulatorEncoding (outputTargetsPrepared base output sample)
      (output - radix • pointHorner radix (Vector.ofFn sample.1).toList) := by
  have encoded := clampPointMemory_encoding (pointHornerMemory (Vector.ofFn sample.1).toList base)
    (pointHorner radix (Vector.ofFn sample.1).toList) output
  simpa only [outputTargetsPrepared, targetScalePointer, PointAccumulatorEncoding,
    Function.update_of_ne (by decide : (2 : Register) ≠ 11),
    Function.update_of_ne (by decide : (3 : Register) ≠ 11),
    Function.update_of_ne (by decide : (4 : Register) ≠ 11)] using encoded

/-- The complete target computation writes the original source targets. -/
theorem outputTargetsMemory_ram [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (outputTargetsMemory base output sample).ram = storeDrawWords (base.registers 13) 0 base.ram
      (vectorWords homogeneousWords (Security.outputTargets output (Vector.ofFn sample.1) sample.2)) := by
  rw [outputTargetsMemory, outputTargetRowsMemory_ram, (outputTargetsPrepared_data base output sample).2,
    outputTargetsPrepared_caller base output sample 13 (by decide) (by decide) (by decide) (by decide)]

/-- The complete target computation preserves every protocol stack. -/
theorem outputTargetsMemory_bits [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (outputTargetsMemory base output sample).bits = base.bits := by
  rw [outputTargetsMemory, outputTargetRowsMemory_bits, (outputTargetsPrepared_data base output sample).1]

end Kriterion.ArgoMAC.ArithmeticSimulator
