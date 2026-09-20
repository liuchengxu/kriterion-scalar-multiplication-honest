import Proof.Privacy.Simulator.Arithmetic.HashHandler
import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A host contains the complete hash handler before its final return. -/
def ContainsHashHandler (host : Machine) (labels : Fin 74 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 74, pc ≠ 73 → host.code[(labels pc).val] =
    relocate labels (hashHandler.code[pc.val]'(by exact pc.isLt))

/-- A contained linear block retains its relocated continuation labels. -/
theorem hashHandlerBlock_linear (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) (program : List LinearInstruction)
    (sourceLabels : Nat → Fin 74) (source : ContainsLinear hashHandler program sourceLabels)
    (inside : ∀ index, index < program.length → sourceLabels index ≠ 73) :
    ContainsLinear host program (labels ∘ sourceLabels) := by
  intro index valid
  exact (present (sourceLabels index) (inside index valid)).trans
    ((congrArg (relocate labels) (source index valid)).trans (LinearInstruction.relocate_emit labels _ _))

/-- The host contains the metadata loader. -/
theorem hashHandlerBlock_load (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsLinear host oracleLoad (labels ∘ hashLoadLabels) := by
  apply hashHandlerBlock_linear host labels present oracleLoad hashLoadLabels hashHandler_load
  intro index valid equal
  have bound : index < 22 := valid
  have values := congrArg Fin.val equal
  simp [hashLoadLabels, Nat.min_eq_left (by omega : index ≤ 22)] at values
  omega

/-- The host contains the hash setup. -/
theorem hashHandlerBlock_setup (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsLinear host hashSetup (labels ∘ hashSetupLabels) := by
  apply hashHandlerBlock_linear host labels present hashSetup hashSetupLabels hashHandler_setup
  intro index valid equal
  have bound : index < 4 := valid
  have values := congrArg Fin.val equal
  simp [hashSetupLabels, Nat.min_eq_left (by omega : index ≤ 4)] at values
  omega

/-- The host contains the fresh hash insertion. -/
theorem hashHandlerBlock_install (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsLinear host hashInstall (labels ∘ hashInstallLabels) := by
  apply hashHandlerBlock_linear host labels present hashInstall hashInstallLabels hashHandler_install
  intro index valid equal
  have bound : index < 16 := valid
  have values := congrArg Fin.val equal
  simp [hashInstallLabels, bound] at values
  omega

/-- The host contains the stored-answer branch. -/
theorem hashHandlerBlock_known (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsLinear host hashKnown (labels ∘ hashKnownLabels) := by
  apply hashHandlerBlock_linear host labels present hashKnown hashKnownLabels hashHandler_known
  intro index valid equal
  have bound : index < 3 := valid
  have values := congrArg Fin.val equal
  simp [hashKnownLabels, Nat.min_eq_left (by omega : index ≤ 3)] at values
  omega

/-- The host contains the persistent count commit. -/
theorem hashHandlerBlock_commit (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsLinear host oracleCommit (labels ∘ hashCommitLabels) := by
  apply hashHandlerBlock_linear host labels present oracleCommit hashCommitLabels hashHandler_commit
  intro index valid equal
  have bound : index < 3 := valid
  have values := congrArg Fin.val equal
  simp [hashCommitLabels, Nat.min_eq_left (by omega : index ≤ 3)] at values
  omega

/-- The host contains every table lookup instruction. -/
theorem hashHandlerBlock_table (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsTableLookup host (labels ∘ hashTableLabels) := by
  intro pc valid
  have inside : hashTableLabels pc ≠ 73 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [hashTableLabels] at values
    omega
  exact (present (hashTableLabels pc) inside).trans
    ((congrArg (relocate labels) (hashHandler_table pc valid)).trans (relocate_comp hashTableLabels labels _))

/-- The host contains the exact 256-bit sampler. -/
theorem hashHandlerBlock_word (host : Machine) (labels : Fin 74 → Fin (host.size + 1))
    (present : ContainsHashHandler host labels) : ContainsWordSampler host 256 (labels ∘ hashWordLabels) := by
  intro pc valid
  have inside : hashWordLabels pc ≠ 73 := by
    intro equal
    have values := congrArg Fin.val equal
    simp [hashWordLabels] at values
    omega
  exact (present (hashWordLabels pc) inside).trans
    ((congrArg (relocate labels) (hashHandler_word pc valid)).trans (relocate_comp hashWordLabels labels _))

/-- The host selects a fresh draw or its stored-answer branch in one instruction. -/
theorem hashHandlerBlock_branch [BN254.FieldCertificate] (host : Machine)
    (labels : Fin 74 → Fin (host.size + 1)) (present : ContainsHashHandler host labels)
    (fuel : Nat) (memory : Memory) :
    run host (fuel + 1) ⟨labels 35, memory⟩ =
      (run host fuel ⟨if memory.registers 12 = 0#256 then labels 39 else labels 67, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  simp [run, step, present 35 (by decide), hashHandler, relocate]

end Kriterion.ArgoMAC.ArithmeticSimulator
