import Proof.Privacy.Simulator.Arithmetic.SharedGateDirectiveCommands
import Proof.Privacy.Simulator.Arithmetic.GateLoopJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Security Security.SharedSimulatorMachine
noncomputable section

/-- The loop command list follows the source schedule over each bounded interval. -/
theorem sharedDirectiveLoop_interval {count : Nat} (directives : Fin count → GateDirective)
    (remaining index : Nat) (inside : index + remaining ≤ count) :
    gateLoopCommandList (fun gate => sharedDirectiveSlot (directives gate))
      (fun gate => !(directives gate).bit) remaining index =
      (scheduleCommands (List.ofFn fun gate : Fin remaining =>
        directives ⟨index + gate.val, by omega⟩)).map sharedCommand := by
  induction remaining generalizing index with
  | zero => simp [gateLoopCommandList, scheduleCommands]
  | succ remaining ih =>
    have current : index < count := by omega
    simp only [gateLoopCommandList, dif_pos current, sharedDirectiveSlot_list,
      List.ofFn_succ, scheduleCommands, List.flatMap_cons, List.map_append]
    rw [ih (index + 1) (by omega)]
    congr 1
    congr 1
    apply congrArg scheduleCommands
    apply congrArg List.ofFn
    funext gate
    congr 1
    apply Fin.ext
    simp only [Fin.val_succ]
    omega

/-- The complete loop has the exact shared source schedule. -/
theorem sharedDirectiveLoop_list {count : Nat} (directives : Fin count → GateDirective) :
    gateLoopCommandList (fun gate => sharedDirectiveSlot (directives gate))
      (fun gate => !(directives gate).bit) count 0 =
      (scheduleCommands (List.ofFn directives)).map sharedCommand := by
  simpa only [Nat.zero_add] using sharedDirectiveLoop_interval directives count 0 (by omega)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
