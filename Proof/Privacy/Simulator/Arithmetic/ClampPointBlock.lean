import Proof.Privacy.Simulator.Arithmetic.ClampPointMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains every correction instruction before its return. -/
def ContainsClampPoint (host : Machine) (labels : Fin 27 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 27, pc.val < 26 → host.code[(labels pc).val] =
    relocate labels (clampPoint.code[pc.val]'(by exact pc.isLt))

/-- The correction machine contains the fixed scalar multiplication block. -/
theorem clampBlock_scalar (host : Machine) (labels : Fin 27 → Fin (host.size + 1))
    (present : ContainsClampPoint host labels) : ContainsScalarMul host (labels ∘ clampScalarLabels) := by
  intro pc inside
  have source : clampPoint.code[(clampScalarLabels pc).val] = relocate clampScalarLabels (scalarMul.code[pc.val]) := by
    simp only [clampPoint, Vector.getElem_ofFn, clampScalarLabels]
    simp only [show pc.val + 1 ≠ 0 by omega, ↓reduceIte, show pc.val + 1 < 11 by omega,
      Nat.add_sub_cancel]
    simp only [dite_true, dite_false]
  exact ((present (clampScalarLabels pc) (by simp [clampScalarLabels]; omega)).trans
    (congrArg (relocate labels) source)).trans (relocate_comp clampScalarLabels labels _)

/-- The correction machine contains the fixed point negation block. -/
theorem clampBlock_negation (host : Machine) (labels : Fin 27 → Fin (host.size + 1))
    (present : ContainsClampPoint host labels) : ContainsPointNegation host (labels ∘ clampNegationLabels) := by
  intro pc inside
  have source : clampPoint.code[(clampNegationLabels pc).val] = relocate clampNegationLabels (pointNegation.code[pc.val]) := by
    simp only [clampPoint, Vector.getElem_ofFn, clampNegationLabels]
    simp only [show 13 + pc.val ≠ 0 by omega, ↓reduceIte, show ¬13 + pc.val < 11 by omega,
      show 13 + pc.val ≠ 11 by omega, show 13 + pc.val ≠ 12 by omega,
      show 13 + pc.val < 16 by omega, Nat.add_sub_cancel_left]
    simp only [dite_true, dite_false]
  exact ((present (clampNegationLabels pc) (by simp [clampNegationLabels]; omega)).trans
    (congrArg (relocate labels) source)).trans (relocate_comp clampNegationLabels labels _)

/-- The correction machine normalizes the accumulator in two instructions. -/
theorem clampBlock_canonical [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) (point : BN254.Point)
    (input : readPoint base.registers scalarAccumulator = some point) :
    run host (fuel + 2) ⟨labels 11, base⟩ =
      (run host fuel ⟨labels 13, clampCanonical base point⟩).map
        (Option.map fun result => (result.1, result.2 + 2)) := by
  have acc : readPoint (Function.update base.registers 5 0#256) scalarAccumulator = some point := by
    rw [readPoint_update_other base.registers scalarAccumulator 5 0#256 (by decide) (by decide) (by decide)]
    exact input
  have mul : readPoint (Function.update base.registers 5 0#256) scalarMultiple = some (0 : BN254.Point) := by
    simp [readPoint, scalarMultiple]
  simp [run, step, present 11 (by decide), present 12 (by decide), clampPoint, relocate, acc, mul,
    clampCanonical, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The correction machine reads the selected output in nine instructions. -/
theorem clampBlock_load [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + 9) ⟨labels 16, base⟩ =
      (run host fuel ⟨labels 25, clampLoaded base⟩).map
        (Option.map fun result => (result.1, result.2 + 9)) := by
  simp [run, step, present 16 (by decide), present 17 (by decide), present 18 (by decide),
    present 19 (by decide), present 20 (by decide), present 21 (by decide), present 22 (by decide),
    present 23 (by decide), present 24 (by decide), clampPoint, relocate, Arithmetic.eval,
    clampLoaded, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    Function.update_comm, BitVec.add_assoc]

/-- The final load and addition compute the exact correction sum. -/
theorem clampBlock_tail [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) (negative output : BN254.Point)
    (input : readPoint base.registers scalarAccumulator = some negative)
    (source : selectedOutputPoint base.ram (base.registers 11) = some output) :
    run host (fuel + 10) ⟨labels 16, base⟩ =
      (run host fuel ⟨labels 26, clampAdded base negative output⟩).map
        (Option.map fun result => (result.1, result.2 + 10)) := by
  rw [show fuel + 10 = (fuel + 1) + 9 by omega, clampBlock_load host labels present (fuel + 1) base]
  have acc := (clampLoaded_accumulator base).trans input
  have mul := (clampLoaded_point base).trans source
  simp [run, step, present 25 (by decide), clampPoint, relocate, acc, mul, clampAdded,
    PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The canonical point write preserves all caller registers. -/
theorem clampCanonical_caller [BN254.FieldCertificate] (base : Memory) (point : BN254.Point)
    (register : Register) (caller : 9 ≤ register.val) :
    (clampCanonical base point).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro same; have value := congrArg Fin.val same; omega
  change writePoint (Function.update base.registers 5 0) scalarAccumulator point register = base.registers register
  rw [writePoint_other _ scalarAccumulator _ register
    (different 2 (by decide)) (different 3 (by decide)) (different 4 (by decide)),
    Function.update_of_ne (different 5 (by decide))]

/-- The correction budget charges its scalar, normalization, negation, and output load. -/
def clampPointCost [BN254.FieldCertificate] [BN254.GroupCertificate] (current : BN254.Point) : Nat :=
  scalarLoopCost radix.val + 16 + pointNegationCost (radix • current)

/-- The correction machine loads the paper radix before the scalar block. -/
theorem clampBlock_prepare [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) :
    run host (fuel + 1) ⟨labels 0, base⟩ =
      (run host fuel ⟨(labels ∘ clampScalarLabels) 0, hornerReady base⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  simp [run, step, present 0 (by decide), clampPoint, relocate, clampScalarLabels, hornerReady]

/-- The final correction phase normalizes, negates, and adds the selected output. -/
theorem clampBlock_finish [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) (point output : BN254.Point)
    (input : readPoint base.registers scalarAccumulator = some point)
    (source : selectedOutputPoint base.ram (base.registers 11) = some output) :
    run host (fuel + (pointNegationCost point + 12)) ⟨labels 11, base⟩ =
      (run host fuel ⟨labels 26, clampAdded (pointNegationMemory (clampCanonical base point) point) (-point) output⟩).map
        (Option.map fun result => (result.1, result.2 + (pointNegationCost point + 12))) := by
  let canonical := clampCanonical base point
  let negated := pointNegationMemory canonical point
  have encoded := clampCanonical_encoding base point
  have negative := accumulatorEncoding_read negated (-point) (pointNegationMemory_encoding canonical point encoded)
  have pointer : negated.registers 11 = base.registers 11 := by
    rw [pointNegationMemory_register canonical point 11 (by decide) (by decide),
      clampCanonical_caller base point 11 (by decide)]
  have ram : negated.ram = base.ram := by cases point <;> rfl
  have tail := clampBlock_tail host labels present fuel negated (-point) output negative
    (by rw [ram, pointer]; exact source)
  have negation := pointNegationBlock_run host (labels ∘ clampNegationLabels) (clampBlock_negation host labels present)
    (fuel + 10) canonical point encoded
  have normalize := clampBlock_canonical host labels present (fuel + 10 + pointNegationCost point) base point input
  rw [show fuel + (pointNegationCost point + 12) = (fuel + 10 + pointNegationCost point) + 2 by omega, normalize]
  change (run host (fuel + 10 + pointNegationCost point) ⟨(labels ∘ clampNegationLabels) 0, canonical⟩).map _ = _
  rw [negation]
  change ((run host (fuel + 10) ⟨labels 16, negated⟩).map _).map _ = _
  rw [tail]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  apply congrArg (fun transform => PMF.map transform _)
  funext result
  cases result <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- The host returns the exact correction memory and charges its complete path. -/
theorem clampPointBlock_run [BN254.FieldCertificate] [BN254.GroupCertificate] (host : Machine)
    (labels : Fin 27 → Fin (host.size + 1)) (present : ContainsClampPoint host labels)
    (fuel : Nat) (base : Memory) (current output : BN254.Point)
    (input : readPoint base.registers scalarMultiple = some current)
    (source : selectedOutputPoint base.ram (base.registers 11) = some output) :
    run host (fuel + clampPointCost current) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 26, clampPointMemory base current output⟩).map
        (Option.map fun result => (result.1, result.2 + clampPointCost current)) := by
  let scaled := scalarFinish (hornerReady base) current
  have spec := hornerScaled_spec base current input
  have finish := clampBlock_finish host labels present fuel scaled (radix • current) output spec.1
    (by rw [spec.2.2.1, spec.2.2.2 11 (by decide)]; exact source)
  have ready : readPoint (hornerReady base).registers scalarMultiple = some current := by
    rw [hornerReady, readPoint_update_other base.registers scalarMultiple 0 _ (by decide) (by decide) (by decide)]
    exact input
  have bounded : radix.val < 2 ^ 256 := lt_trans radix.val_lt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
  have value : ((hornerReady base).registers 0).toNat = radix.val := by
    simp only [hornerReady, Function.update_self, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounded]
  have block := scalarMulBlock_memory host (labels ∘ clampScalarLabels) (clampBlock_scalar host labels present)
    (hornerReady base) current ready
  rw [value] at block
  have continued := run_after_prefix host (scalarLoopCost radix.val + 3)
    (fuel + (pointNegationCost (radix • current) + 12)) ⟨(labels ∘ clampScalarLabels) 0, hornerReady base⟩
  rw [block, PMF.pure_bind] at continued
  have total : fuel + clampPointCost current =
      (scalarLoopCost radix.val + 3 + (fuel + (pointNegationCost (radix • current) + 12))) + 1 := by
    unfold clampPointCost; omega
  rw [total, clampBlock_prepare host labels present, continued]
  change ((run host (fuel + (pointNegationCost (radix • current) + 12)) ⟨labels 11, scaled⟩).map _).map _ = _
  rw [finish]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  apply congrArg (fun transform => PMF.map transform (run host fuel ⟨labels 26, clampPointMemory base current output⟩))
  funext result
  cases result <;> simp [clampPointCost, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Every correction path uses at most 1557 fixed instructions. -/
theorem clampPointCost_bound [BN254.FieldCertificate] [BN254.GroupCertificate] (current : BN254.Point) :
    clampPointCost current ≤ 1557 := by
  have bound := hornerStepCost_bound
  have negation : pointNegationCost (radix • current) ≤ 3 := by cases radix • current <;> simp [pointNegationCost]
  unfold clampPointCost hornerStepCost at *
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
