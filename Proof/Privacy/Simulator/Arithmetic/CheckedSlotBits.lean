import Proof.Privacy.Simulator.Arithmetic.GateDriverSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

set_option maxRecDepth 4096

/-- The complete successful slot finish preserves every bit stack. -/
theorem checkedSlotFinished_bits (memory : Memory) : (checkedSlotFinished memory).bits = memory.bits := by
  unfold checkedSlotFinished
  rw [(historyAppended_data _).2.2.2.2, (checkedSlotHistory_values _).2.2.2, (overlayAppended_data _).2.2.2, (checkedSlotTarget_values _).2.2.2]

/-- The cutoff and successful forward tails preserve every bit stack. -/
theorem checkedSlotForwardResult_bits (overlayCount : Nat) (memory : Memory) :
    (checkedSlotForwardResult overlayCount memory).bits = memory.bits := by
  unfold checkedSlotForwardResult
  split
  · exact (internalForwardTail_data overlayCount memory).2.1
  · exact (checkedSlotFinished_bits _).trans (internalForwardTail_data overlayCount memory).2.1

/-- Every checked slot sample preserves every bit stack, including collision and cutoff paths. -/
theorem checkedSlotSamples_bits (attempts count overlayCount historyCount : Nat) (memory : Memory)
    (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotSamples attempts count overlayCount historyCount memory).support) :
    result.2.1.bits = memory.bits := by
  obtain ⟨branch, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have prepared : (checkedSlotPrepared historyCount memory).bits = memory.bits :=
    (historyFreshSource_data historyCount (executeLinear checkedSlotStart memory)).2.1.trans
      (checkedSlotStart_values memory).2.2.2.2.2
  unfold checkedSlotBranchSamples at member
  split at member
  · have same := (PMF.mem_support_pure_iff _ _).mp member
    subst branch
    exact prepared
  · obtain ⟨draw, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    exact (checkedSlotForwardResult_bits overlayCount draw.1).trans
      ((storedForwardSamples_bits attempts count _ draw.1 draw.2 reached).trans prepared)

/-- The automatic source uses the same stack-preserving checked slot. -/
theorem checkedSlotAutomaticSamples_bits (attempts : Nat) (memory : Memory) (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (checkedSlotAutomaticSamples attempts memory).support) :
    result.2.1.bits = memory.bits :=
  checkedSlotSamples_bits attempts _ _ _ memory result supported

/-- The gate slot loader and complete checked source preserve every bit stack. -/
theorem gateDriverSlotSamples_bits (attempts : Nat) (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (result : Fin 305 × Memory × Nat)
    (supported : result ∈ (gateDriverSlotSamples attempts gate slot memory).support) :
    result.2.1.bits = memory.bits := by
  obtain ⟨draw, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact (checkedSlotAutomaticSamples_bits attempts _ draw member).trans
    (gateSlotLoad_values (gate.oracle slot) slot memory).2.2.2.2

end Kriterion.ArgoMAC.ArithmeticSimulator
