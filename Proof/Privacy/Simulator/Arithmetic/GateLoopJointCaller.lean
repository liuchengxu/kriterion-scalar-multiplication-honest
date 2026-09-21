import Proof.Privacy.Simulator.Arithmetic.GateLoopJoint
import Proof.Privacy.Simulator.Arithmetic.GateDriverJointCaller

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- Every accepted gate loop preserves all five original caller registers. -/
theorem gateLoopCoupled_caller [BN254.FieldCertificate] {count : Nat} (plan : Vector GateCode count)
    (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit : Nat) (memory : Memory) (state : SharedOracleSource)
    (ready : GateLoopCoupledReady plan commands third attempts remaining index limit memory state)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110)
    (result : GateLoopJointResult)
    (supported : some result ∈ (gateLoopCoupled plan commands attempts remaining index memory state).support) :
    result.1.2.1.registers 11 = memory.registers 11 ∧ result.1.2.1.registers 12 = memory.registers 12 ∧
    result.1.2.1.registers 13 = memory.registers 13 ∧ result.1.2.1.registers 14 = memory.registers 14 ∧
    result.1.2.1.registers 15 = memory.registers 15 := by
  induction remaining generalizing index limit memory state result with
  | zero =>
    simp only [gateLoopCoupled, PMF.mem_support_pure_iff, Option.some.injEq] at supported
    subst result
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
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
        have retained := gateDriverCoupled_caller attempts limit plan[index] (commands ⟨index, inside⟩) memory state
          ready.1 ready.2.1 (by omega) head reached
        have tailRetained := ih (index + 1) (limit + 3) head.1.2.1 head.2
          (ready.2.2.2 head reached) (by omega) tail tailMember
        exact ⟨tailRetained.1.trans retained.1, tailRetained.2.1.trans retained.2.1,
          tailRetained.2.2.1.trans retained.2.2.1, tailRetained.2.2.2.1.trans retained.2.2.2.1,
          tailRetained.2.2.2.2.trans retained.2.2.2.2⟩
    · simp only [GateLoopCoupledReady, dif_neg inside] at ready

end
end Kriterion.ArgoMAC.ArithmeticSimulator
