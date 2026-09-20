import Proof.Privacy.Simulator.Arithmetic.OracleFamilySource
import Proof.Privacy.Simulator.Arithmetic.InternalForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The internal observer recovers the next source state from the accepted final reply. -/
def internalForwardMemoryState (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (memory : Memory) : ProgrammedPermutation (2 ^ 128) :=
  ((queryValue memory).map fun word =>
    programmedForwardNext state input (sparseWordValue (2 ^ 128) (by decide) word)).getD state

/-- The internal tail observer agrees with the existing programmed source observer. -/
theorem internalForwardMemoryState_tail (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) (memory : Memory) :
    internalForwardMemoryState state input (internalForwardTail state.overlay.length memory).1 =
      programmedForwardMemoryState state input memory := by
  unfold internalForwardMemoryState programmedForwardMemoryState
  rw [internalForwardTail_value]

/-- Every internal query retains the full physical oracle family. -/
theorem internalForwardSamples_family [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (internalForwardSamples attempts
      (state.permutations oracle).base.used (state.permutations oracle).overlay.length memory).support) :
    OracleFamilyMemory final.ram
      (state.updatePermutation oracle (internalForwardMemoryState (state.permutations oracle) input final)) := by
  obtain ⟨⟨before, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  rw [internalForwardMemoryState_tail, (internalForwardTail_data _ before).1]
  have family := storedForwardSamples_family attempts memory before spent state oracle input
    represented capacity index operand fits member
  rw [publicForwardTail_ram] at family
  exact family

/-- The complete internal reply and family update have the exact cutoff source law. -/
theorem internalForwardSamples_family_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110) :
    (internalForwardSamples attempts (state.permutations oracle).base.used
      (state.permutations oracle).overlay.length memory).map
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, state.updatePermutation oracle (programmedForwardNext (state.permutations oracle) input value))) =
      (drawCutoffLaw attempts ((state.permutations oracle).forward input)).map
        (Option.map fun result => (result.1, state.updatePermutation oracle result.2)) := by
  simp only [internalForwardSamples, PMF.map_comp, Function.comp_def, internalForwardTail_value]
  exact storedForwardSamples_family_joint attempts memory state oracle input represented index operand fits overlayFits

end Kriterion.ArgoMAC.ArithmeticSimulator
