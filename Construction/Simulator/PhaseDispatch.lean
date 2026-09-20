import Construction.Simulator.Assembly

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The dispatcher consumes the two protocol bits without changing registers or RAM.
Labels three, four, five, and six select setup, online encoding, a public query, and rejection. -/
def phaseDispatch : Machine := ⟨6, #v[
  .pop 0 6 1 2, .pop 0 6 3 4, .pop 0 6 5 6,
  .halt, .halt, .halt, .halt], by decide⟩

/-- The host contains all three dispatch instructions. -/
def ContainsPhaseDispatch (host : Machine) (labels : Fin 7 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 7, pc.val < 3 → host.code[labels pc] = relocate labels (phaseDispatch.code[pc])

/-- The first bit selects the public-query branch. The second bit selects online encoding. -/
def phaseDispatchReturn (first second : Bool) : Fin 7 :=
  if first then if second then 6 else 5 else if second then 4 else 3

/-- The dispatch memory keeps the unread protocol body and every private value. -/
def phaseDispatchMemory (memory : Memory) (body : List Bool) : Memory :=
  {memory with bits := Function.update memory.bits 0 body}

end Kriterion.ArgoMAC.ArithmeticSimulator
