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

/-- Each strict gate preserves all bit stacks. -/
theorem lazyGateDriverResult_bits {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (gate : GateCode) (memory : Memory) (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex)
    (result) (success : lazyGateDriverResult gate memory oracle = some result) :
    result.1.bits = memory.bits := by
  unfold lazyGateDriverResult at success
  dsimp only [Bind.bind] at success
  obtain ⟨first, firstEq, second, secondEq, success⟩ :=
    (by simpa only [Option.bind_eq_some_iff] using success)
  have firstBits := (lazyGateSlot_memory gate 0 _ first.1 oracle first.2 firstEq).2.1
  have secondBits := (lazyGateSlot_memory gate 1 _ second.1 first.2 second.2 secondEq).2.1
  split at success
  · obtain ⟨third, thirdEq, success⟩ := Option.bind_eq_some_iff.mp success
    cases success
    have thirdBits := (lazyGateSlot_memory gate 2 _ third.1 second.2 third.2 thirdEq).2.1
    rw [(gateDirectiveRestore_data third.1).2]
    rw [thirdBits]
    change second.1.bits = memory.bits
    exact secondBits.trans (firstBits.trans (gateDriverPrepared_bits gate memory))
  · cases success
    rw [(gateDirectiveRestore_data (executeLinear gateDriverTest second.1)).2]
    change second.1.bits = memory.bits
    exact secondBits.trans (firstBits.trans (gateDriverPrepared_bits gate memory))

/-- Each successful strict loop preserves all bit stacks. -/
theorem lazyGateLoopResults_bits {count : Nat} {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (plan : Vector GateCode count) (remaining index : Nat) (memory : Memory)
    (oracle : Cryptography.LazyOracle.State FixedIndex EncIndex) (result)
    (success : lazyGateLoopResults plan remaining index memory oracle = some result) :
    result.1.bits = memory.bits := by
  induction remaining generalizing index memory oracle result with
  | zero =>
    simp only [lazyGateLoopResults, Option.some.injEq] at success
    subst result
    rfl
  | succ remaining ih =>
    unfold lazyGateLoopResults at success
    split at success
    · rename_i inside
      dsimp only [Bind.bind] at success
      obtain ⟨head, reached, tail, tailReached, equal⟩ :=
        (by simpa only [Option.bind_eq_some_iff] using success)
      cases equal
      exact (ih (index + 1) head.1 head.2.1 tail tailReached).trans
        (lazyGateDriverResult_bits plan[index] memory oracle head reached)
    · contradiction

end Kriterion.ArgoMAC.ArithmeticSimulator
