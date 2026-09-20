import Proof.Privacy.Simulator.Arithmetic.OnlineInputProtocol
import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine
set_option maxRecDepth 4096

/-- The host supplies the online reader and selects its return instruction. -/
def ContainsOnlineInput (host : Machine) (labels : Fin 98 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 98, pc.val < 97 → host.code[(labels pc).val] =
    relocate labels (onlineInput.code[pc.val]'(by exact pc.isLt))

/-- Each word reader keeps its source behavior in the host. -/
theorem onlineInputBlock_word (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (width : Nat) (offset : Fin 84) (returnLabel : Fin 98)
    (source : ContainsWordInput onlineInput width (onlineInputLabels offset returnLabel)) :
    ContainsWordInput host width (fun pc => labels (onlineInputLabels offset returnLabel pc)) := by
  intro pc inside
  have small : (onlineInputLabels offset returnLabel pc).val < 97 := by
    simp only [onlineInputLabels, dif_pos inside, Fin.val_mk]
    have := offset.isLt
    omega
  exact (present _ small).trans ((congrArg (relocate labels) (source pc inside)).trans
    (relocate_comp (onlineInputLabels offset returnLabel) labels _))

/-- Each RAM store keeps its source behavior in the host. -/
theorem onlineInputBlock_linear (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (program : List LinearInstruction)
    (sourceLabels : Nat → Fin 98) (source : ContainsLinear onlineInput program sourceLabels)
    (inside : ∀ index, index < program.length → (sourceLabels index).val < 97) :
    ContainsLinear host program (fun index => labels (sourceLabels index)) := by
  intro index valid
  exact (present _ (inside index valid)).trans ((congrArg (relocate labels)
    (source index valid)).trans (LinearInstruction.relocate_emit labels _ _))

/-- Each store returns to the selected host label. -/
theorem onlineInputBlock_store (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (offset : Word) (start : Fin 96) (returnLabel : Fin 98)
    (source : ContainsLinear onlineInput (onlineInputStore offset) (onlineStoreLabels start returnLabel))
    (small : start.val < 95) :
    ContainsLinear host (onlineInputStore offset) (fun index => labels (onlineStoreLabels start returnLabel index)) := by
  apply onlineInputBlock_linear host labels present _ _ source
  intro index valid
  have bound : index < 3 := valid
  simp only [onlineStoreLabels, dif_pos bound, Fin.val_mk]
  omega

/-- The output branch chooses the same path in the host. -/
theorem onlineInputBlock_branch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 98 → Fin (host.size + 1)) (present : ContainsOnlineInput host labels) (memory : Memory) :
    runPrefix host 3 ⟨labels 51, memory⟩ =
      PMF.pure (some (false, ⟨if memory.registers 0 = 1 then labels 54 else labels 90,
        onlineBranchMemory memory⟩, 3)) := by
  by_cases affine : memory.registers 0 = 1 <;>
    simp [runPrefix, step, present 51 (by decide), present 52 (by decide), present 53 (by decide),
      relocate, onlineInput, Arithmetic.eval, onlineBranchMemory, affine, BitVec.sub_eq_iff_eq_add, PMF.pure_map]
  all_goals rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
