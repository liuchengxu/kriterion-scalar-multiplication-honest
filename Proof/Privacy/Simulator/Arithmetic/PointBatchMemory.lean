import Construction.Simulator.PointBatch
import Proof.Privacy.Simulator.Arithmetic.PointSamplerBlock
import Proof.Privacy.Simulator.Arithmetic.SamplerBatchSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each point uses its tag and two canonical field words. -/
def pointWords [BN254.FieldCertificate] : BN254.Point → List Word
  | .zero => [0, 0, 0]
  | .some x y _ => [1, BitVec.ofNat 256 x.val, BitVec.ofNat 256 y.val]

/-- The decoded result names the sampled point. -/
def pointValue [BN254.FieldCertificate] (base : Memory) : BN254.Point :=
  (readPoint base.registers scalarAccumulator).getD 0

/-- The canonical write normalizes the point at its existing accumulator registers. -/
def pointCanonical [BN254.FieldCertificate] (base : Memory) : Memory :=
  {base with registers := writePoint (Function.update base.registers 5 0) scalarAccumulator (pointValue base)}

/-- The point store writes three canonical words and retains the final store address. -/
def pointStored [BN254.FieldCertificate] (base : Memory) (index : Nat) : Memory :=
  {pointCanonical base with
    registers := Function.update (pointCanonical base).registers 8
      (base.registers 10 + BitVec.ofNat 256 (3 * index + 2))
    ram := storeDrawWords (base.registers 10) (3 * index) base.ram (pointWords (pointValue base))}

/-- Each point entry includes its eleven canonical-write and RAM-store instructions. -/
noncomputable def pointBatchStepMemory [BN254.FieldCertificate] (attempts index : Nat) (base : Memory) :
    PMF (Memory × Nat) :=
  (pointSamplerReturnMemory attempts base).map fun result => (pointStored result.1 index, result.2 + 11)

/-- Each point entry has a fixed instruction budget. -/
def pointBatchStepBudget (attempts : Nat) : Nat := pointSamplerFuel attempts - 1 + 11

/-- The sampler always returns a valid point before the canonical write. -/
theorem pointSamplerReturnMemory_valid [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointSamplerReturnMemory attempts base).support) :
    readPoint final.registers scalarAccumulator = some (pointValue final) := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have valid := (pointSamplerFinal_spec memory).1
  dsimp only
  unfold pointValue
  rw [valid]
  rfl

/-- The point decoder has the exact total source point law. -/
theorem pointSamplerReturnMemory_value [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) :
    (pointSamplerReturnMemory attempts base).map (fun result => pointValue result.1) =
      (Security.SimulatorSampling.point.total attempts).law := by
  have source := congrArg (PMF.map (fun value : Option BN254.Point => value.getD 0))
    (pointSamplerReturnMemory_source attempts base)
  simp only [PMF.map_comp, Function.comp_def, Option.getD_some] at source
  exact source.trans (PMF.map_id _)

/-- Each point entry fits its full fixed instruction budget. -/
theorem pointBatchStepMemory_cost [BN254.FieldCertificate] (attempts index : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointBatchStepMemory attempts index base).support) :
    cost ≤ pointBatchStepBudget attempts := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have bounded := pointSamplerReturnMemory_cost attempts base memory spent member
  dsimp only
  unfold pointBatchStepBudget
  omega

/-- Each point entry preserves caller stacks. -/
theorem pointBatchStepMemory_bits [BN254.FieldCertificate] (attempts index : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (pointBatchStepMemory attempts index base).support) :
    final.bits = base.bits := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (pointSamplerReturnMemory_data attempts base memory spent member).1

/-- The canonical write and store preserve registers nine through fifteen. -/
theorem pointStored_caller [BN254.FieldCertificate] (base : Memory) (index : Nat)
    (register : Register) (caller : 9 ≤ register.val) :
    (pointStored base index).registers register = base.registers register := by
  have different (target : Register) (small : target.val < 9) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  simp only [pointStored, pointCanonical, Function.update_of_ne (different 8 (by decide))]
  rw [writePoint_other _ scalarAccumulator _ register (different 2 (by decide))
    (different 3 (by decide)) (different 4 (by decide)), Function.update_of_ne (different 5 (by decide))]

/-- Each point entry preserves registers nine through fifteen. -/
theorem pointBatchStepMemory_caller [BN254.FieldCertificate] (attempts index : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 9 ≤ register.val)
    (supported : (final, cost) ∈ (pointBatchStepMemory attempts index base).support) :
    final.registers register = base.registers register := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (pointStored_caller memory index register caller).trans
    (pointSamplerReturnMemory_caller attempts base memory spent register caller member)

/-- Each point entry stores its exact total source point in RAM. -/
theorem pointBatchStepMemory_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts index : Nat) (base : Memory) :
    (pointBatchStepMemory attempts index base).map (fun result => result.1.ram) =
      (Security.SimulatorSampling.point.total attempts).law.map
        (fun point => storeDrawWords (base.registers 10) (3 * index) base.ram (pointWords point)) := by
  rw [pointBatchStepMemory, PMF.map_comp]
  have retained : (pointSamplerReturnMemory attempts base).map
      (fun result => (pointStored result.1 index).ram) =
      (pointSamplerReturnMemory attempts base).map
        (fun result => storeDrawWords (base.registers 10) (3 * index) base.ram (pointWords (pointValue result.1))) := by
    change (pointSamplerReturnMemory attempts base).bind _ = (pointSamplerReturnMemory attempts base).bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    apply congrArg PMF.pure
    rcases result with ⟨memory, cost⟩
    dsimp only [pointStored]
    rw [(pointSamplerReturnMemory_data attempts base memory cost supported).2,
      pointSamplerReturnMemory_caller attempts base memory cost 10 (by decide) supported]
  change (pointSamplerReturnMemory attempts base).map (fun result => (pointStored result.1 index).ram) = _
  rw [retained]
  have source := congrArg (PMF.map
    (fun point => storeDrawWords (base.registers 10) (3 * index) base.ram (pointWords point)))
    (pointSamplerReturnMemory_value attempts base)
  simpa only [PMF.map_comp, Function.comp_def] using source

end Kriterion.ArgoMAC.ArithmeticSimulator
