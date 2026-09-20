import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRun
import Proof.Privacy.Simulator.Arithmetic.PermutationFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The canonical query reader preserves the response stack. -/
theorem queryInputMemory_output (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (queryInputMemory memory request rest).bits 3 = memory.bits 3 := by
  cases request <;> simp [queryInputMemory, fixedQueryMemory, encQueryMemory, hashQueryMemory,
    decodedInput, inputFinal, inputFrame, queryTagState, queryFamilyState, queryFixedState,
    queryEncState, queryOperandState, queryHashState]

/-- The complete input prefix preserves the response stack. -/
theorem publicInputMemory_output (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (publicInputMemory memory request rest).bits 3 = memory.bits 3 :=
  (congrFun (publicDispatchMemory_data (queryInputMemory memory request rest)).2.2.2.2 3).trans
    (queryInputMemory_output memory request rest)

/-- Every stored forward result preserves all bit stacks before output. -/
theorem storedForwardSamples_bits (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedForwardSamples attempts count memory).support) :
    final.bits = memory.bits := by
  unfold storedForwardSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact permutationForwardSamples_bits attempts count count (oracleLoaded memory) before spent member

/-- Every stored inverse result preserves all bit stacks before output. -/
theorem storedInverseSamples_bits (attempts count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (storedInverseSamples attempts count memory).support) :
    final.bits = memory.bits := by
  unfold storedInverseSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact permutationForwardSamples_bits attempts count count (inverseLoaded memory) before spent member

/-- Every sparse hash tail preserves all bit stacks before output. -/
theorem hashTailSamples_bits (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashTailSamples memory).support) : final.bits = memory.bits := by
  unfold hashTailSamples at supported
  split at supported
  · obtain ⟨value, _, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    rfl
  · simp only [PMF.mem_support_pure_iff] at supported
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj supported
    rfl

/-- Every complete sparse hash sample preserves all bit stacks before output. -/
theorem hashHandlerSamples_bits (count : Nat) (memory final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (hashHandlerSamples count memory).support) : final.bits = memory.bits := by
  unfold hashHandlerSamples at supported
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact (hashTailSamples_bits (hashScan count memory).1 before spent member).trans
    (tableScan_data count (tableInitial (hashReady (oracleLoaded memory)))).1

/-- Inverse overlay removal preserves all bit stacks before the stored inverse query. -/
theorem publicInversePrepared_bits (count : Nat) (memory : Memory) :
    (publicInversePrepared count memory).bits = memory.bits :=
  (overlayInverse_data count (oracleLoaded memory)).2.1

end Kriterion.ArgoMAC.ArithmeticSimulator
