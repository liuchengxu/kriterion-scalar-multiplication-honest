import Construction.Simulator.PhaseDispatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The combined table stores three dispatch instructions, three bodies, and one rejection halt. -/
def phaseMachineSize (setup online query : Machine) : Nat := setup.size + online.size + query.size + 6

def phaseSetupLabels (setup online query : Machine) (pc : Fin (setup.size + 1)) :
    Fin (phaseMachineSize setup online query + 1) := ⟨3 + pc.val, by
  have := pc.isLt; unfold phaseMachineSize; omega⟩

def phaseOnlineLabels (setup online query : Machine) (pc : Fin (online.size + 1)) :
    Fin (phaseMachineSize setup online query + 1) := ⟨4 + setup.size + pc.val, by
  have := pc.isLt; unfold phaseMachineSize; omega⟩

def phaseQueryLabels (setup online query : Machine) (pc : Fin (query.size + 1)) :
    Fin (phaseMachineSize setup online query + 1) := ⟨5 + setup.size + online.size + pc.val, by
  have := pc.isLt; unfold phaseMachineSize; omega⟩

def phaseMachineLabels (setup online query : Machine) (pc : Fin 7) :
    Fin (phaseMachineSize setup online query + 1) :=
  if dispatch : pc.val < 3 then ⟨pc.val, by unfold phaseMachineSize; omega⟩
  else if pc = 3 then phaseSetupLabels setup online query 0
  else if pc = 4 then phaseOnlineLabels setup online query 0
  else if pc = 5 then phaseQueryLabels setup online query 0
  else ⟨phaseMachineSize setup online query, Nat.lt_succ_self _⟩

/-- The machine selects one complete phase body from the two protocol bits. -/
def phaseMachine (setup online query : Machine)
    (fits : phaseMachineSize setup online query < 2 ^ 256) : Machine :=
  ⟨phaseMachineSize setup online query, Vector.ofFn (fun pc =>
    if dispatch : pc.val < 3 then
      relocate (phaseMachineLabels setup online query) (phaseDispatch.code[pc.val]'(by change pc.val < 7; omega))
    else if offline : pc.val < 4 + setup.size then
      relocate (phaseSetupLabels setup online query) (setup.code[pc.val - 3]'(by omega))
    else if encoding : pc.val < 5 + setup.size + online.size then
      relocate (phaseOnlineLabels setup online query) (online.code[pc.val - (4 + setup.size)]'(by omega))
    else if external : pc.val < phaseMachineSize setup online query then
      relocate (phaseQueryLabels setup online query)
        (query.code[pc.val - (5 + setup.size + online.size)]'(by unfold phaseMachineSize at external; omega))
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
