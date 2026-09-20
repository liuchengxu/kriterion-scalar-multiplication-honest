import Proof.Privacy.Simulator.Arithmetic.GateLoopJoint
import Proof.Privacy.Simulator.Arithmetic.GatePreparedMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- Every accepted loop preserves the represented source, hash table, and all private caller buffers. -/
theorem gateLoopCoupled_memory [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit)
    (ready : GateLoopCoupledReady plan commands third attempts remaining index limit memory state)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110)
    (result : GateLoopJointResult)
    (supported : some result ∈ (gateLoopCoupled plan commands attempts remaining index memory state).support) :
    SharedSourceMemory result.1.2.1 result.2 (limit + 3 * remaining) ∧
    result.2.family.hash = state.family.hash ∧
    ∀ cell, 32 ≤ cell → cell < 2 ^ 96 → result.1.2.1.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  induction remaining generalizing index limit memory state result with
  | zero =>
    simp only [gateLoopCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at supported
    subst result
    exact ⟨by simpa only [Nat.mul_zero, Nat.add_zero] using represented, rfl, fun _ _ _ => rfl⟩
  | succ remaining ih =>
    by_cases inside : index < count
    · simp only [GateLoopCoupledReady, dif_pos inside] at ready
      simp only [gateLoopCoupled, dif_pos inside] at supported
      obtain ⟨head, reached, tailReached⟩ := (mem_support_bindCutoff _ _ _).mp supported
      obtain ⟨draw, tailMember, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp tailReached
      cases draw with
      | none => simp at equal
      | some tail =>
        have same := Option.some.inj equal
        subst result
        have retained := gateDriverCoupled_memory attempts limit plan[index] (commands ⟨index, inside⟩) memory state
          ready.1 ready.2.1 (by omega) head reached
        have tailRetained := ih (index + 1) (limit + 3) head.1.2.1 head.2 retained.1
          (ready.2.2.2 head reached) (by omega) tail tailMember
        refine ⟨?_, tailRetained.2.1.trans retained.2, ?_⟩
        · convert tailRetained.1 using 1 <;> omega
        · intro cell lower privateBound
          exact (tailRetained.2.2 cell lower privateBound).trans
            ((gateDriverCoupled_private attempts limit plan[index] (commands ⟨index, inside⟩) memory state ready.1 ready.2.1
              (by omega) cell privateBound (by omega) (by omega) (by omega) (by omega) (by omega) head reached).trans
                (gateDriverPrepared_private plan[index] memory cell lower privateBound))
    · simp only [GateLoopCoupledReady, dif_neg inside] at ready

end
end Kriterion.ArgoMAC.ArithmeticSimulator
