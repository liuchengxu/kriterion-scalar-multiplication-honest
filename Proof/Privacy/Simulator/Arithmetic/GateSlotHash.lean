import Proof.Privacy.Simulator.Arithmetic.GateSlotInvariant

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

/-- Every successful checked program retains the complete hash table. -/
theorem checkedSlotJointSamples_hash (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : (result, some next) ∈ (checkedSlotJointSamples attempts memory state command).support) :
    next.family.hash = state.family.hash := by
  unfold checkedSlotJointSamples at supported
  split at supported
  · obtain ⟨⟨before, spent⟩, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    have outcome := congrArg Prod.snd equal
    dsimp only at outcome
    unfold checkedProgramFamilyValue at outcome
    cases observed : overlayQueryValue (state.family.permutations (sharedPhysicalIndex (.inl command.1))).overlay.length before with
    | none => simp only [observed, Option.map_none] at outcome; contradiction
    | some word =>
      simp only [observed, Option.map_some, Option.some.injEq] at outcome
      subst next
      rfl
  · simp only [PMF.mem_support_pure_iff, Prod.mk.injEq, Option.some.injEq] at supported
    obtain ⟨rfl, rfl⟩ := supported
    rfl

/-- The coupled program retains the complete hash table. -/
theorem checkedSlotCoupledSamples_hash (attempts : Nat) (memory : Memory) (state : SharedOracleSource)
    (command : SharedCommand) (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (checkedSlotCoupledSamples attempts memory state command).support) :
    next.family.hash = state.family.hash := by
  obtain ⟨⟨actual, source⟩, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases source with
  | none => simp at equal
  | some found =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨rfl, rfl⟩ := equal
    exact checkedSlotJointSamples_hash attempts memory state command actual found reached

/-- The loaded coupled slot retains the complete hash table. -/
theorem gateDriverSlotCoupledSamples_hash (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (state : SharedOracleSource) (command : SharedCommand)
    (result : Fin 305 × Memory × Nat) (next : SharedOracleSource)
    (supported : some ((), (result, next)) ∈ (gateDriverSlotCoupledSamples attempts gate slot memory state command).support) :
    next.family.hash = state.family.hash := by
  obtain ⟨draw, reached, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases draw with
  | none => simp at equal
  | some draw =>
    obtain ⟨value, actual, found⟩ := draw
    cases value
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at equal
    obtain ⟨resultEqual, rfl⟩ := equal
    exact checkedSlotCoupledSamples_hash attempts _ state command actual found reached

end
end Kriterion.ArgoMAC.ArithmeticSimulator
