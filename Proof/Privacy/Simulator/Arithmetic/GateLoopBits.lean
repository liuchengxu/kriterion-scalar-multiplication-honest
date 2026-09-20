import Proof.Privacy.Simulator.Arithmetic.CheckedSlotBits
import Proof.Privacy.Simulator.Arithmetic.GateLoopSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A stack-preserving continuation retains the complete slot source's bit stacks. -/
theorem gateAfterSlot_bits (attempts : Nat) (gate : GateCode) (slot : Fin 3) (memory : Memory)
    (next : Memory → PMF (Fin 1036 × Memory × Nat))
    (kept : ∀ memory result, result ∈ (next memory).support → result.2.1.bits = memory.bits)
    (result : Fin 1036 × Memory × Nat)
    (supported : result ∈ ((gateDriverSlotSamples attempts gate slot memory).bind (gateDriverAfterSlot next)).support) :
    result.2.1.bits = memory.bits := by
  obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  have first := gateDriverSlotSamples_bits attempts gate slot memory head member
  unfold gateDriverAfterSlot at tail
  split at tail
  · obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
    exact (kept head.2.1 last lastMember).trans first
  · have same := (PMF.mem_support_pure_iff _ _).mp tail
    subst result
    exact first

/-- The final pointer restore preserves every bit stack. -/
theorem gateRestoreSamples_bits (memory : Memory) (result : Fin 1036 × Memory × Nat)
    (supported : result ∈ (gateRestoreSamples memory).support) : result.2.1.bits = memory.bits := by
  have same := (PMF.mem_support_pure_iff _ _).mp supported
  subst result
  exact (gateDirectiveRestore_data memory).2

/-- The optional third slot preserves every bit stack. -/
theorem gateThirdSamples_bits (attempts : Nat) (gate : GateCode) (memory : Memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateThirdSamples attempts gate memory).support) :
    result.2.1.bits = memory.bits :=
  gateAfterSlot_bits attempts gate 2 memory gateRestoreSamples gateRestoreSamples_bits result supported

/-- The saved slot-count test preserves every bit stack. -/
theorem gateTestSamples_bits (attempts : Nat) (gate : GateCode) (memory : Memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateTestSamples attempts gate memory).support) :
    result.2.1.bits = memory.bits := by
  obtain ⟨tail, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have testBits : (executeLinear gateDriverTest memory).bits = memory.bits := by
    simp [gateDriverTest, executeLinear, LinearInstruction.execute]
  split at member
  · exact (gateThirdSamples_bits attempts gate (executeLinear gateDriverTest memory) tail member).trans testBits
  · exact (gateRestoreSamples_bits (executeLinear gateDriverTest memory) tail member).trans testBits

/-- The second slot preserves every bit stack through its complete continuation. -/
theorem gateSecondSamples_bits (attempts : Nat) (gate : GateCode) (memory : Memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateSecondSamples attempts gate memory).support) :
    result.2.1.bits = memory.bits :=
  gateAfterSlot_bits attempts gate 1 memory (gateTestSamples attempts gate) (gateTestSamples_bits attempts gate) result supported

/-- Gate preparation preserves every bit stack. -/
theorem gateDriverPrepared_bits (gate : GateCode) (memory : Memory) :
    (gateDriverPrepared gate memory).bits = memory.bits := by
  unfold gateDriverPrepared
  rw [gateDirectiveSave_bits]
  have branches (bit : Bool) (loaded : Memory) : (gateBlocksMemory gate.tweak bit loaded).bits = loaded.bits := by
    cases bit
    · exact (gateHashProgram_preserves loaded gate.tweak).2.1
    · exact (gatePadProgram_preserves loaded gate.tweak).2.1
  rw [branches]
  exact (gateDirectiveLoad_preserves gate.selected gate.target gate.quotient gate.table memory).2.1

/-- The complete gate source preserves every bit stack on normal, collision, and cutoff paths. -/
theorem gateDriverSamples_bits (attempts : Nat) (gate : GateCode) (memory : Memory)
    (result : Fin 1036 × Memory × Nat) (supported : result ∈ (gateDriverSamples attempts gate memory).support) :
    result.2.1.bits = memory.bits := by
  obtain ⟨body, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact (gateAfterSlot_bits attempts gate 0 (gateDriverPrepared gate memory) (gateSecondSamples attempts gate)
    (gateSecondSamples_bits attempts gate) body member).trans (gateDriverPrepared_bits gate memory)

/-- Every complete gate-loop sample preserves every bit stack. -/
theorem gateLoopSamples_bits {count : Nat} (plan : Vector GateCode count)
    (attempts remaining index : Nat) (memory : Memory) (result : Bool × Memory × Nat)
    (supported : result ∈ (gateLoopSamples plan attempts remaining index memory).support) :
    result.2.1.bits = memory.bits := by
  induction remaining generalizing index memory result with
  | zero =>
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst result
      rfl
  | succ remaining ih =>
      by_cases inside : index < count
      · simp only [gateLoopSamples, dif_pos inside] at supported
        obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        have first := gateDriverSamples_bits attempts plan[index] memory head member
        split at tail
        · obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
          exact (ih (index + 1) head.2.1 last lastMember).trans first
        · have same := (PMF.mem_support_pure_iff _ _).mp tail
          subst result
          exact first
      · simp only [gateLoopSamples, dif_neg inside] at supported
        have same := (PMF.mem_support_pure_iff _ _).mp supported
        subst result
        rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
