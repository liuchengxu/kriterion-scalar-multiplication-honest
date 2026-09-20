import Construction.Simulator.PhaseMachine
import Proof.Privacy.Simulator.Arithmetic.AssemblyRun
import Proof.Privacy.Simulator.Arithmetic.PhaseDispatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The combined table contains all three dispatch instructions. -/
theorem phaseMachine_dispatch (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) :
    ContainsPhaseDispatch (phaseMachine setup online query fits) (phaseMachineLabels setup online query) := by
  intro pc valid
  change (phaseMachine setup online query fits).code[(phaseMachineLabels setup online query pc).val] =
    relocate (phaseMachineLabels setup online query) (phaseDispatch.code[pc.val])
  simp [phaseMachine, phaseMachineLabels, valid]

/-- The setup body retains every instruction and its halt. -/
theorem phaseMachine_setup (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) :
    ContainsMachine (phaseMachine setup online query fits) setup (phaseSetupLabels setup online query) := by
  intro pc
  have bound := pc.isLt
  simp [phaseMachine, phaseSetupLabels, show ¬ 3 + pc.val < 3 by omega,
    show 3 + pc.val < 4 + setup.size by omega]

/-- The online body retains every instruction and its halt. -/
theorem phaseMachine_online (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) :
    ContainsMachine (phaseMachine setup online query fits) online (phaseOnlineLabels setup online query) := by
  intro pc
  have bound := pc.isLt
  simp [phaseMachine, phaseOnlineLabels, show ¬ 4 + setup.size + pc.val < 3 by omega,
    show ¬ 4 + setup.size + pc.val < 4 + setup.size by omega,
    show 4 + setup.size + pc.val < 5 + setup.size + online.size by omega]

/-- The public body retains every instruction and its halt. -/
theorem phaseMachine_query (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) :
    ContainsMachine (phaseMachine setup online query fits) query (phaseQueryLabels setup online query) := by
  intro pc
  have bound := pc.isLt
  simp [phaseMachine, phaseQueryLabels, show ¬ 5 + setup.size + online.size + pc.val < 3 by omega,
    show ¬ 5 + setup.size + online.size + pc.val < 4 + setup.size by omega,
    show ¬ 5 + setup.size + online.size + pc.val < 5 + setup.size + online.size by omega,
    show 5 + setup.size + online.size + pc.val < phaseMachineSize setup online query by
      unfold phaseMachineSize; omega]

end Kriterion.ArgoMAC.ArithmeticSimulator
