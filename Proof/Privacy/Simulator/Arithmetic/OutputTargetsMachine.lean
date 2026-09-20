import Proof.Privacy.Simulator.Arithmetic.OutputTargetsBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The standalone target machine contains each instruction before its halt. -/
theorem outputTargetsMachine_self : ContainsOutputTargets outputTargetsMachine id := by
  intro pc inside
  change outputTargetsMachine.code[pc.val] = relocate id (outputTargetsMachine.code[pc.val])
  generalize outputTargetsMachine.code[pc.val] = instruction
  cases instruction <;> rfl

private theorem halt_at [BN254.FieldCertificate] (machine : Machine) (pc : Fin (machine.size + 1))
    (code : machine.code[pc.val] = .halt) (base : Memory) :
    run machine 1 ⟨pc, base⟩ = PMF.pure (some (⟨pc, base⟩, 1)) := by
  simp [run, step, code]

/-- The target machine charges its final halt. -/
theorem outputTargetsMachine_halt [BN254.FieldCertificate] (base : Memory) :
    run outputTargetsMachine 1 ⟨(4288 : Fin 4289), base⟩ = PMF.pure (some (⟨(4288 : Fin 4289), base⟩, 1)) := by
  apply halt_at
  simp only [outputTargetsMachine, Vector.getElem_ofFn]
  simp

/-- The complete machine returns all original target rows with its exact instruction charge. -/
theorem outputTargetsMachine_run [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (pointer : base.registers 10 = base.registers 14 + 91)
    (stored : WordsAt base.ram (base.registers 14) 0 (onlineWords sample))
    (selected : selectedOutputPoint base.ram (base.registers 11) = some output)
    (separate : ∀ i, i < 270 → ∀ j, j < 273 →
      base.registers 10 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j ∧
      base.registers 14 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j) :
    run outputTargetsMachine (outputTargetsCost sample.1 + 1) ⟨(0 : Fin 4289), base⟩ =
      PMF.pure (some (⟨(4288 : Fin 4289), outputTargetsMemory base output sample⟩, outputTargetsCost sample.1 + 1)) := by
  have continued := outputTargetsBlock_run outputTargetsMachine id outputTargetsMachine_self 1 base output sample pointer stored selected separate
  simpa only [id_eq, outputTargetsMachine_halt, PMF.pure_map, Option.map_some, Nat.add_comm] using continued

/-- The standalone target budget includes all executed instructions and table entries. -/
theorem outputTargetsMachine_budget [BN254.FieldCertificate] [BN254.GroupCertificate] (free : Fin 90 → BN254.Point) :
    outputTargetsMachine.size + 1 + (outputTargetsCost free + 1) ≤ 149241 := by
  have bounded := outputTargetsCost_bound free
  change 4288 + 1 + (outputTargetsCost free + 1) ≤ 149241
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
