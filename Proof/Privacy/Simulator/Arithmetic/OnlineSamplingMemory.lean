import Proof.Privacy.Simulator.Arithmetic.PointBatch
import Proof.Privacy.Simulator.Arithmetic.SamplerBatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
open Security.SimulatorSampling

/-- The online scale schedule stores the canonical nonzero field words of every digit. -/
def onlineScaleSchedule : PrivateSchedule (scale.vector 91) := scaleSchedule.vector 91

/-- The online scale plan has a fixed 91-entry vector representation. -/
def onlineScalePlan : Vector DrawSpec 91 := ⟨onlineScaleSchedule.plan.toArray, by
  simpa using onlineScaleSchedule.planLength⟩

/-- The point phase starts after the 91 stored scales. -/
def onlinePointInitial (base : Memory) : Memory :=
  {base with registers := Function.update (Function.update base.registers 8 91) 10 (base.registers 10 + 91)}

/-- The online return law samples all scales before all points. -/
noncomputable def onlineSamplingMemory [BN254.FieldCertificate] (attempts : Nat) (base : Memory) : PMF (Memory × Nat) :=
  (samplerBatchMemory onlineScalePlan attempts 91 0 base).bind fun scales =>
    (pointBatchMemory attempts 0 90 (onlinePointInitial scales.1)).map fun points =>
      (points.1, scales.2 + 2 + points.2)

/-- The online budget pays for both sampling phases and the pointer change. -/
def onlineSamplingBudget (attempts : Nat) : Nat :=
  batchStepBudget attempts * 91 + pointBatchStepBudget attempts * 90 + 2

/-- Every online return fits the complete prefix budget. -/
theorem onlineSamplingMemory_cost [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts base).support) :
    cost ≤ onlineSamplingBudget attempts := by
  obtain ⟨⟨scaleMemory, scaleCost⟩, scaleSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨⟨pointMemory, pointCost⟩, pointSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have scales := samplerBatchMemory_cost onlineScalePlan attempts 91 0 base scaleMemory scaleCost scaleSupport
  have points := pointBatchMemory_cost attempts 0 90 (onlinePointInitial scaleMemory) pointMemory pointCost pointSupport
  dsimp only
  unfold onlineSamplingBudget
  omega

/-- The scale batch has the exact total nonzero-field vector law. -/
theorem onlineScaleMemory_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (samplerBatchMemory onlineScalePlan attempts 91 0 base).map (fun result => result.1.ram) =
      ((scale.vector 91).total attempts).law.map
        (fun scales => storeDrawWords (base.registers 10) 0 base.ram (onlineScaleSchedule.words scales)) := by
  rw [samplerBatchMemory_source]
  have planList : onlineScalePlan.toList = onlineScaleSchedule.plan := by simp [onlineScalePlan]
  rw [planList, onlineScaleSchedule.sourceLaw, PMF.map_comp]
  rfl

/-- A base-pointer shift agrees with the corresponding index shift. -/
theorem storeDrawWords_shift (pointer : Word) (offset index : Nat) (ram : Word → Word) (words : List Word) :
    storeDrawWords (pointer + BitVec.ofNat 256 offset) index ram words =
      storeDrawWords pointer (offset + index) ram words := by
  induction words generalizing index ram with
  | nil => rfl
  | cons head tail ih =>
      simp only [storeDrawWords, ih]
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [Nat.add_assoc]

/-- The online word representation stores scales before point coordinates. -/
def onlineWords [BN254.FieldCertificate]
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) : List Word :=
  onlineScaleSchedule.words (Vector.ofFn sample.2) ++ vectorWords pointWords (Vector.ofFn sample.1)

/-- The online source samples its scale vector before its point vector. -/
theorem online_vector_law [BN254.FieldCertificate] (attempts : Nat) :
    (online.total attempts).law = ((scale.vector 91).total attempts).law.bind fun scales =>
      ((point.vector 90).total attempts).law.map fun points =>
        (Security.vectorFunctionEquiv.symm points, Security.vectorFunctionEquiv.symm scales) := by
  simp only [online, Code.pair, Code.total, Security.BoundedIntegerSampling.BitCode.bind_law,
    totalCode_map_law, Code.arrayFunction, totalCode_map_law, PMF.bind_map, PMF.map_comp, Function.comp_def]

/-- The online arithmetic memory has the exact total selected-path draw law. -/
theorem onlineSamplingMemory_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) :
    (onlineSamplingMemory attempts base).map (fun result => result.1.ram) =
      (online.total attempts).law.map
        (fun sample => storeDrawWords (base.registers 10) 0 base.ram (onlineWords sample)) := by
  let next (ram : Word → Word) := ((point.vector 90).total attempts).law.map
    (fun points => storeDrawWords (base.registers 10) 91 ram (vectorWords pointWords points))
  rw [onlineSamplingMemory, PMF.map_bind]
  calc
    _ = (samplerBatchMemory onlineScalePlan attempts 91 0 base).bind (fun result => next result.1.ram) := by
      apply Security.ThreePhase.bind_eq_on_support
      intro result supported
      rcases result with ⟨memory, cost⟩
      simp only [PMF.map_comp, Function.comp_def]
      rw [pointBatchMemory_source]
      simp only [onlinePointInitial, Function.update_self, Nat.mul_zero]
      rw [samplerBatchMemory_caller onlineScalePlan attempts 91 0 base memory cost 10 (by decide) supported]
      apply congrArg (fun transform => ((point.vector 90).total attempts).law.map transform)
      funext points
      exact storeDrawWords_shift (base.registers 10) 91 0 memory.ram _
    _ = ((samplerBatchMemory onlineScalePlan attempts 91 0 base).map (fun result => result.1.ram)).bind next := by
      rw [PMF.bind_map]
      rfl
    _ = _ := by
      rw [onlineScaleMemory_source, PMF.bind_map, online_vector_law, PMF.map_bind]
      apply congrArg (fun continuation => ((scale.vector 91).total attempts).law.bind continuation)
      funext scales
      simp only [Function.comp_def, next, PMF.map_comp]
      apply congrArg (fun transform => ((point.vector 90).total attempts).law.map transform)
      funext points
      have vectorRoundtrip {A : Type} {count : Nat} (value : Vector A count) :
          Vector.ofFn (Security.vectorFunctionEquiv.symm value) = value := by
        apply Vector.ext
        intro index inside
        simp [Security.vectorFunctionEquiv]
        rfl
      simp only [onlineWords, vectorRoundtrip]
      rw [storeDrawWords_append, onlineScaleSchedule.wordsLength]

/-- The online source uses exactly 361 private RAM words. -/
theorem onlineWords_length [BN254.FieldCertificate]
    (sample : (Fin 90 → BN254.Point) × (Fin 91 → BN254.NonZeroBase)) :
    (onlineWords sample).length = 361 := by
  simp only [onlineWords, List.length_append, onlineScaleSchedule.wordsLength, pointVectorWords_length]

/-- The complete online sampler preserves caller stacks. -/
theorem onlineSamplingMemory_bits [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts base).support) :
    final.bits = base.bits := by
  obtain ⟨⟨scaleMemory, scaleCost⟩, scaleSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨⟨pointMemory, pointCost⟩, pointSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (pointBatchMemory_bits attempts 0 90 (onlinePointInitial scaleMemory) pointMemory pointCost pointSupport).trans
    (samplerBatchMemory_bits onlineScalePlan attempts 91 0 base scaleMemory scaleCost scaleSupport)

/-- The complete online sampler advances its destination pointer by 91 words. -/
theorem onlineSamplingMemory_pointer [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts base).support) :
    final.registers 10 = base.registers 10 + 91 := by
  obtain ⟨⟨scaleMemory, scaleCost⟩, scaleSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨⟨pointMemory, pointCost⟩, pointSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  dsimp only
  rw [pointBatchMemory_caller attempts 0 90 (onlinePointInitial scaleMemory) pointMemory pointCost 10 (by decide) pointSupport]
  simp only [onlinePointInitial, Function.update_self]
  rw [samplerBatchMemory_caller onlineScalePlan attempts 91 0 base scaleMemory scaleCost 10 (by decide) scaleSupport]

/-- The complete online sampler preserves every other caller register. -/
theorem onlineSamplingMemory_caller [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (register : Register) (caller : 9 ≤ register.val) (other : register ≠ 10)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts base).support) :
    final.registers register = base.registers register := by
  obtain ⟨⟨scaleMemory, scaleCost⟩, scaleSupport, supported⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨⟨pointMemory, pointCost⟩, pointSupport, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  dsimp only
  rw [pointBatchMemory_caller attempts 0 90 (onlinePointInitial scaleMemory) pointMemory pointCost register caller pointSupport]
  have temporary : register ≠ 8 := by intro equal; have value := congrArg Fin.val equal; omega
  simp only [onlinePointInitial, Function.update_of_ne other, Function.update_of_ne temporary]
  exact samplerBatchMemory_caller onlineScalePlan attempts 91 0 base scaleMemory scaleCost register caller scaleSupport

end Kriterion.ArgoMAC.ArithmeticSimulator
