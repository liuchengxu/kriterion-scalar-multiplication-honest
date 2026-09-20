import Construction.Simulator.GateDriver

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each gate has a separate normal continuation and a shared cutoff return. -/
def gateLoopLabels {count : Nat} (index : Fin count) (pc : Fin 1036) : Fin (1036 * count + 2) :=
  if pc = 1034 then ⟨1036 * (index.val + 1), by have bound := index.isLt; omega⟩
  else if pc = 1035 then ⟨1036 * count + 1, by omega⟩
  else ⟨1036 * index.val + pc.val, by have bound := index.isLt; have p := pc.isLt; omega⟩

/-- The symbolic table contains every fixed gate instruction.
The normal exit starts the next gate. The cutoff exit stops the loop. -/
def gateLoop {count : Nat} (plan : Vector GateCode count) (attempts : Nat)
    (fits : 1036 * count + 1 < 2 ^ 256) : Machine := ⟨1036 * count + 1,
  Vector.ofFn (fun pc : Fin (1036 * count + 2) =>
    if inside : pc.val < 1036 * count then
      let index : Fin count := ⟨pc.val / 1036, by omega⟩
      relocate (gateLoopLabels index)
        ((gateDriver attempts plan[index]).code[pc.val % 1036]'(by change pc.val % 1036 < 1036; omega))
    else .halt), fits⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
