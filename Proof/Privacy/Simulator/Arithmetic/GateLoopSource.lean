import Proof.Privacy.Simulator.Arithmetic.GateLoopCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source visits each gate in order and stops only on sampler cutoff. -/
noncomputable def gateLoopSamples {count : Nat} (plan : Vector GateCode count) (attempts : Nat) :
    Nat → Nat → Memory → PMF (Bool × Memory × Nat)
  | 0, _, memory => PMF.pure (true, memory, 0)
  | remaining + 1, index, memory =>
      if inside : index < count then
        (gateDriverSamples attempts plan[index] memory).bind fun result =>
          if result.1 = 1034 then
            (gateLoopSamples plan attempts remaining (index + 1) result.2.1).map fun tail =>
              (tail.1, tail.2.1, result.2.2 + tail.2.2)
          else PMF.pure (false, result.2.1, result.2.2)
      else PMF.pure (false, memory, 0)

/-- Each reached gate satisfies the concrete RAM count and coherence conditions. -/
noncomputable def GateLoopReady {count : Nat} (plan : Vector GateCode count) (attempts limit : Nat) :
    Nat → Nat → Memory → Prop
  | 0, _, _ => True
  | remaining + 1, index, memory =>
      if inside : index < count then
        GateDriverReady attempts limit plan[index] memory ∧
        ∀ result ∈ (gateDriverSamples attempts plan[index] memory).support, result.1 = 1034 →
          GateLoopReady plan attempts limit remaining (index + 1) result.2.1
      else False

/-- Every supported loop sample fits the sum of its gate reserves. -/
theorem gateLoopSamples_cost [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (attempts limit remaining index : Nat) (memory : Memory) (attemptFits : attempts < 2 ^ 256)
    (ready : GateLoopReady plan attempts limit remaining index memory)
    (result : Bool × Memory × Nat) (supported : result ∈ (gateLoopSamples plan attempts remaining index memory).support) :
    result.2.2 ≤ gateDriverRunBudget attempts limit * remaining := by
  induction remaining generalizing index memory result with
  | zero =>
      have same : result = (true, memory, 0) := by
        simpa only [gateLoopSamples, PMF.support_pure, Set.mem_singleton_iff] using supported
      subst result
      simp
  | succ remaining ih =>
      by_cases inside : index < count
      · simp only [GateLoopReady, dif_pos inside] at ready
        simp only [gateLoopSamples, dif_pos inside] at supported
        obtain ⟨head, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        have bound := gateDriverSamples_cost attempts limit plan[index] memory attemptFits ready.1 head member
        by_cases normal : head.1 = 1034
        · simp only [if_pos normal] at tail
          obtain ⟨rest, restMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
          have restBound := ih (index + 1) head.2.1 (ready.2 head member normal) rest restMember
          dsimp only
          rw [Nat.mul_succ]
          omega
        · simp only [if_neg normal] at tail
          have same : result = (false, head.2.1, head.2.2) := by
            simpa only [PMF.support_pure, Set.mem_singleton_iff] using tail
          subst result
          change head.2.2 ≤ _
          rw [Nat.mul_succ]
          omega
      · simp only [GateLoopReady, dif_neg inside] at ready

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The loop stops at the first refused program and sums the successful gate costs. -/
noncomputable def lazyGateLoopResults {count : Nat} {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (plan : Vector GateCode count) :
    Nat → Nat → Memory → LazyOracle.State FixedIndex EncIndex →
      Option (Memory × LazyOracle.State FixedIndex EncIndex × Nat)
  | 0, _, memory, oracle => some (memory, oracle, 0)
  | remaining + 1, index, memory, oracle =>
      if inside : index < count then do
        let first ← lazyGateDriverResult plan[index] memory oracle
        let rest ← lazyGateLoopResults plan remaining (index + 1) first.1 first.2.1
        pure (rest.1, rest.2.1, first.2.2 + rest.2.2)
      else none

/-- Every successful loop stays within the sum of its gate limits. -/
theorem lazyGateLoopResults_cost {count : Nat} {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (plan : Vector GateCode count) (remaining index : Nat)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex)
    (result : Memory × LazyOracle.State FixedIndex EncIndex × Nat)
    (success : lazyGateLoopResults plan remaining index memory oracle = some result) :
    result.2.2 ≤ 117 * remaining := by
  induction remaining generalizing index memory oracle result with
  | zero => simp [lazyGateLoopResults] at success; cases success; simp
  | succ remaining ih =>
      simp only [lazyGateLoopResults] at success
      split at success
      · rename_i inside
        cases first : lazyGateDriverResult plan[index] memory oracle with
        | none => simp [first] at success
        | some firstResult =>
            cases rest : lazyGateLoopResults plan remaining (index + 1) firstResult.1 firstResult.2.1 with
            | none => simp [first, rest] at success
            | some restResult =>
                simp [first, rest] at success
                cases success
                have firstBound := lazyGateDriverResult_cost _ _ _ firstResult first
                have restBound := ih _ _ _ restResult rest
                dsimp only
                rw [Nat.mul_succ]
                omega
      · contradiction

end Kriterion.ArgoMAC.ArithmeticSimulator
