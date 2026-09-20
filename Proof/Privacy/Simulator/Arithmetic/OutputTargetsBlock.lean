import Proof.Privacy.Simulator.Arithmetic.OutputTargetsMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The target block charges Horner evaluation, correction, pointer setup, and all rows. -/
def outputTargetsCost [BN254.FieldCertificate] [BN254.GroupCertificate] (free : Fin 90 → BN254.Point) : Nat :=
  pointHornerCost 90 + clampPointCost (pointHorner radix (Vector.ofFn free).toList) + 1 + 1996

/-- The prepared row memory meets the exact online-source contract. -/
theorem outputTargetsPrepared_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (base : Memory) (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (pointer : base.registers 10 = base.registers 14 + 91)
    (stored : WordsAt base.ram (base.registers 14) 0 (onlineWords sample))
    (separate : ∀ i, i < 270 → ∀ j, j < 273 →
      base.registers 10 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j ∧
      base.registers 14 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j) :
    (outputTargetsPrepared base output sample).registers 10 = (outputTargetsPrepared base output sample).registers 11 + 91 ∧
    WordsAt (outputTargetsPrepared base output sample).ram ((outputTargetsPrepared base output sample).registers 11) 0 (onlineWords sample) ∧
    HomogeneousRegionsDisjoint (outputTargetsPrepared base output sample) 91 := by
  have ten := outputTargetsPrepared_caller base output sample 10 (by decide) (by decide) (by decide) (by decide)
  have thirteen := outputTargetsPrepared_caller base output sample 13 (by decide) (by decide) (by decide) (by decide)
  have scale := outputTargetsPrepared_scale base output sample
  refine ⟨by rw [ten, scale]; exact pointer, ?_, ?_⟩
  · rw [(outputTargetsPrepared_data base output sample).2, scale]
    exact stored
  · intro i hi j hj
    rw [ten, thirteen, scale]
    exact separate i hi j hj

/-- The host computes the exact selected output targets and charges the full arithmetic path. -/
theorem outputTargetsBlock_run [BN254.FieldCertificate] [BN254.GroupCertificate]
    (host : Machine) (labels : Fin 4289 → Fin (host.size + 1))
    (present : ContainsOutputTargets host labels) (fuel : Nat) (base : Memory)
    (output : BN254.Point) (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase))
    (pointer : base.registers 10 = base.registers 14 + 91)
    (stored : WordsAt base.ram (base.registers 14) 0 (onlineWords sample))
    (selected : selectedOutputPoint base.ram (base.registers 11) = some output)
    (separate : ∀ i, i < 270 → ∀ j, j < 273 →
      base.registers 10 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j ∧
      base.registers 14 + BitVec.ofNat 256 i ≠ base.registers 13 + BitVec.ofNat 256 j) :
    run host (fuel + outputTargetsCost sample.1) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 4288, outputTargetsMemory base output sample⟩).map
        (Option.map fun result => (result.1, result.2 + outputTargetsCost sample.1)) := by
  let points := (Vector.ofFn sample.1).toList
  let current := pointHorner radix points
  let hornerMemory := pointHornerMemory points base
  let correctionMemory := clampPointMemory hornerMemory current output
  have hornerSpec := pointHornerMemory_spec points base
  have hornerSource (i : Fin 90) :
      storedPoint base.ram (base.registers 10 + BitVec.ofNat 256 (3 * i.val)) = some ((points[i.val]?).getD 0) := by
    rw [pointer, StoredPointEncoding.read _ _ _ (onlineWords_pointEncoding base.ram (base.registers 14) sample stored i)]
    simp [points, i.isLt]
  have horner := pointHornerBlock_run host 90 (by decide) (labels ∘ targetHornerLabels)
    (outputTargetsCode_horner host labels present) points (by simp [points])
    (fuel + 1996 + 1 + clampPointCost current) base hornerSource
  have correction := clampPointBlock_run host (labels ∘ targetClampLabels)
    (outputTargetsCode_clamp host labels present) (fuel + 1996 + 1) hornerMemory current output hornerSpec.1
    (by rw [hornerSpec.2.2.1, hornerSpec.2.2.2 11 (by decide) (by decide) (by decide)]; exact selected)
  have preparation := outputTargetsCode_pointer host labels present (fuel + 1996) correctionMemory
  have source := outputTargetsPrepared_source base output sample pointer stored separate
  have rows := outputTargetRowsBlock_run host (labels ∘ targetRowLabels)
    (outputTargetsCode_rows host labels present) fuel (outputTargetsPrepared base output sample) output sample
    (outputTargetsPrepared_encoding base output sample) source.1 source.2.1 source.2.2
  have amount : fuel + outputTargetsCost sample.1 =
      (fuel + 1996 + 1 + clampPointCost current) + pointHornerCost 90 := by unfold outputTargetsCost current points; omega
  rw [amount]
  change run host ((fuel + 1996 + 1 + clampPointCost current) + pointHornerCost 90)
    ⟨(labels ∘ targetHornerLabels) 0, base⟩ = _
  rw [horner]
  change (run host ((fuel + 1996 + 1) + clampPointCost current) ⟨(labels ∘ targetClampLabels) 0, hornerMemory⟩).map _ = _
  rw [correction]
  change ((run host ((fuel + 1996) + 1) ⟨labels 2011, correctionMemory⟩).map _).map _ = _
  rw [preparation]
  change (((run host (fuel + 1996) ⟨(labels ∘ targetRowLabels) 0, outputTargetsPrepared base output sample⟩).map _).map _).map _ = _
  rw [rows]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  apply congrArg (fun transform => PMF.map transform (run host fuel ⟨labels 4288, outputTargetsMemory base output sample⟩))
  funext result
  cases result <;> simp [outputTargetsCost, current, points, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- The complete target block uses at most 144904 executed instructions. -/
theorem outputTargetsCost_bound [BN254.FieldCertificate] [BN254.GroupCertificate] (free : Fin 90 → BN254.Point) :
    outputTargetsCost free ≤ 144904 := by
  have horner := pointHornerCost_bound 90
  have correction := clampPointCost_bound (pointHorner radix (Vector.ofFn free).toList)
  unfold outputTargetsCost
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
