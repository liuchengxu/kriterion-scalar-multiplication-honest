import Proof.Privacy.Simulator.Arithmetic.GateLoopJointMemory
import Proof.Privacy.Simulator.Arithmetic.GateDriverJointCaller

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.SharedSimulatorMachine
noncomputable section

/-- The gate loop retains the three data pointers and every private source word. -/
structure GatePrivateAgreement (memory initial : Memory) : Prop where
  source : memory.registers 11 = initial.registers 11
  input : memory.registers 12 = initial.registers 12
  labels : memory.registers 14 = initial.registers 14
  words : ∀ cell, 32 ≤ cell → cell < 2 ^ 96 →
    memory.ram (BitVec.ofNat 256 cell) = initial.ram (BitVec.ofNat 256 cell)

theorem GatePrivateAgreement.refl (memory : Memory) : GatePrivateAgreement memory memory :=
  ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩

/-- Each accepted gate retains the initial private data relation. -/
theorem GatePrivateAgreement.afterGate [BN254.FieldCertificate]
    (attempts limit : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory initial : Memory) (state : SharedOracleSource)
    (agreement : GatePrivateAgreement memory initial)
    (represented : SharedSourceMemory (gateDriverPrepared gate memory) state limit)
    (stored : ∀ slot, slot.val < 2 ∨ (gateDriverPrepared gate memory).ram 20 = 3 →
      GateCommandMemory gate slot (gateDriverPrepared gate memory) (commands slot))
    (room : 256 + 2 * (limit + 3) < 2 ^ 110) (result : GateJointResult)
    (supported : some result ∈ (gateDriverCoupled attempts gate commands memory state).support) :
    GatePrivateAgreement result.1.2.1 initial := by
  have caller := gateDriverCoupled_caller attempts limit gate commands memory state represented stored room result supported
  refine ⟨caller.1.trans agreement.source, caller.2.1.trans agreement.input,
    caller.2.2.2.1.trans agreement.labels, ?_⟩
  intro cell lower upper
  exact ((gateDriverCoupled_private attempts limit gate commands memory state represented stored room
    cell upper (by omega) (by omega) (by omega) (by omega) (by omega) result supported).trans
    (gateDriverPrepared_private gate memory cell lower upper)).trans (agreement.words cell lower upper)

/-- Initial typed descriptors suffice for every reached gate in the complete loop. -/
theorem gateLoopCoupledReady_of_initial [BN254.FieldCertificate] {count : Nat}
    (plan : Vector GateCode count) (commands : Fin count → Fin 3 → SharedCommand) (third : Fin count → Bool)
    (attempts remaining index limit : Nat) (memory initial : Memory) (state : SharedOracleSource)
    (inside : index + remaining ≤ count) (agreement : GatePrivateAgreement memory initial)
    (represented : SharedSourceMemory memory state limit)
    (room : 256 + 2 * (limit + 3 * remaining) < 2 ^ 110)
    (prepared : ∀ current, GatePrivateAgreement current initial → ∀ gate : Fin count,
      (gateDriverPrepared plan[gate.val] current).ram 20 = (if third gate then 3 else 2) ∧
      ∀ slot, slot.val < 2 ∨ (gateDriverPrepared plan[gate.val] current).ram 20 = 3 →
        GateCommandMemory plan[gate.val] slot (gateDriverPrepared plan[gate.val] current) (commands gate slot)) :
    GateLoopCoupledReady plan commands third attempts remaining index limit memory state := by
  induction remaining generalizing index limit memory state with
  | zero => trivial
  | succ remaining ih =>
      have here : index < count := by omega
      have exactCommands := prepared memory agreement ⟨index, here⟩
      have source := represented.gatePrepared plan[index] (by omega)
      simp only [GateLoopCoupledReady, dif_pos here]
      refine ⟨source, exactCommands.2, exactCommands.1, ?_⟩
      intro result supported
      have retained := gateDriverCoupled_memory attempts limit plan[index] (commands ⟨index, here⟩)
        memory state source exactCommands.2 (by omega) result supported
      exact ih (index + 1) (limit + 3) result.1.2.1 result.2 (by omega)
        (GatePrivateAgreement.afterGate attempts limit plan[index] (commands ⟨index, here⟩) memory initial state agreement
          source exactCommands.2 (by omega) result supported) retained.1 (by omega) prepared

end
end Kriterion.ArgoMAC.ArithmeticSimulator
