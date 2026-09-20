import Proof.Privacy.Simulator.Arithmetic.GateRetargetMachine
import Proof.Privacy.Simulator.Arithmetic.PolynomialInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The factor loader reads the input record through register twelve. -/
def retargetInput : List LinearInstruction :=
  [.load 5 12, .constant 2 1, .arithmetic .add 2 12 2, .load 6 2,
    .arithmetic .fieldMul 7 5 5, .arithmetic .fieldMul 8 6 6]

/-- The request loader selects its private data and requested output word. -/
noncomputable def retargetAt (kind : RetargetKind) (sourceOffset : Nat) (targetBase : Register)
    (targetOffset : Nat) : List LinearInstruction :=
  [.constant 10 (BitVec.ofNat 256 sourceOffset), .arithmetic .add 10 11 10,
    .constant 13 (BitVec.ofNat 256 targetOffset), .arithmetic .add 13 targetBase 13] ++ retargetCode kind

/-- The curve request uses the private bridge word as its target. -/
noncomputable def retargetCurveProgram : List LinearInstruction :=
  retargetInput ++ retargetAt .curve 834395 11 0

/-- Each point row updates its X, Y, and Z low targets. -/
noncomputable def retargetPointRow (row : Fin FieldMacToECMac.outputMacCount) : List LinearInstruction :=
  retargetAt .x (1017 + 9158 * row.val + 6105) 14 (3 * row.val) ++
  retargetAt .y (1017 + 9158 * row.val + 3815) 14 (3 * row.val + 1) ++
  retargetAt .z (1017 + 9158 * row.val) 14 (3 * row.val + 2)

/-- The point pass updates all 273 coordinate requests before their gate phase. -/
noncomputable def retargetPointProgram : List LinearInstruction :=
  retargetInput ++ (List.ofFn retargetPointRow).flatten

theorem retargetAt_length (kind : RetargetKind) (sourceOffset : Nat) (targetBase : Register) (targetOffset : Nat) :
    (retargetAt kind sourceOffset targetBase targetOffset).length = 4 + retargetLength kind := by
  simp only [retargetAt, List.length_append, List.length_cons, List.length_nil, retargetCode_length]

theorem retargetCurveProgram_length : retargetCurveProgram.length = 6405 := by
  simp [retargetCurveProgram, retargetAt_length, retargetInput, retargetLength]

theorem retargetPointRow_length (row : Fin FieldMacToECMac.outputMacCount) : (retargetPointRow row).length = 15401 := by
  simp [retargetPointRow, retargetAt_length, retargetLength]

theorem retargetPointProgram_length : retargetPointProgram.length = 1401497 := by
  simp only [retargetPointProgram, List.length_append, List.length_flatten, List.map_ofFn]
  change 6 + (List.ofFn (fun row : Fin FieldMacToECMac.outputMacCount => (retargetPointRow row).length)).sum = 1401497
  simp_rw [retargetPointRow_length]
  rw [List.ofFn_const, List.sum_replicate_nat, FieldMacToECMac.outputMacCount]

attribute [local irreducible] retargetPointProgram retargetCurveProgram

private noncomputable def retargetCurvePackage : {program : List LinearInstruction // program = retargetCurveProgram} :=
  Classical.choice ⟨⟨retargetCurveProgram, rfl⟩⟩

private noncomputable def retargetPointPackage : {program : List LinearInstruction // program = retargetPointProgram} :=
  Classical.choice ⟨⟨retargetPointProgram, rfl⟩⟩

/-- The checked packages keep both large arithmetic passes symbolic. -/
noncomputable def retargetCurveCode : List LinearInstruction := retargetCurvePackage.val

noncomputable def retargetPointCode : List LinearInstruction := retargetPointPackage.val

theorem retargetCurveCode_eq : retargetCurveCode = retargetCurveProgram := retargetCurvePackage.property

theorem retargetPointCode_eq : retargetPointCode = retargetPointProgram := retargetPointPackage.property

theorem retargetCurveCode_length : retargetCurveCode.length = 6405 := by
  rw [retargetCurveCode_eq, retargetCurveProgram_length]

theorem retargetPointCode_length : retargetPointCode.length = 1401497 := by
  rw [retargetPointCode_eq, retargetPointProgram_length]

/-- The curve pass returns after its exact arithmetic charge. -/
theorem retargetCurveHost_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host retargetCurveCode labels)
    (memory : Memory) (fuel : Nat) :
    run host (6405 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 6405, executeLinear retargetCurveCode memory⟩).map
        (Option.map fun result => (result.1, result.2 + 6405)) := by
  simpa only [retargetCurveCode_length] using linear_continue host retargetCurveCode labels present memory fuel

/-- The point pass returns after its exact arithmetic charge. -/
theorem retargetPointHost_continue [BN254.FieldCertificate] (host : Machine)
    (labels : Nat → Fin (host.size + 1)) (present : ContainsLinear host retargetPointCode labels)
    (memory : Memory) (fuel : Nat) :
    run host (1401497 + fuel) ⟨labels 0, memory⟩ =
      (run host fuel ⟨labels 1401497, executeLinear retargetPointCode memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1401497)) := by
  simpa only [retargetPointCode_length] using linear_continue host retargetPointCode labels present memory fuel

end Kriterion.ArgoMAC.ArithmeticSimulator
