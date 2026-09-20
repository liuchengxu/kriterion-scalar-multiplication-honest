import Proof.Privacy.Simulator.Arithmetic.ProgrammedForwardSource
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRam

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The programmed reply determines the base update after removal of the output swaps. -/
def programmedForwardNext (state : ProgrammedPermutation (2 ^ 128)) (input output : Fin (2 ^ 128)) :
    ProgrammedPermutation (2 ^ 128) :=
  { state with base := sparseForwardNext state.base input ((swaps state.overlay).symm output) }

/-- The programmed forward source retains its complete state under reply recovery. -/
theorem programmedForward_recover (attempts : Nat) (state : ProgrammedPermutation (2 ^ 128))
    (input : Fin (2 ^ 128)) :
    (drawCutoffLaw attempts (state.forward input)).map
      (Option.map fun result => (result.1, programmedForwardNext state input result.1)) =
      drawCutoffLaw attempts (state.forward input) := by
  have recovered := sparseForward_recover attempts state.base input
  have result := congrArg (PMF.map (Option.map fun pair : Fin (2 ^ 128) × SparsePermutation (2 ^ 128) =>
    (swaps state.overlay pair.1, {state with base := pair.2}))) recovered
  simpa only [ProgrammedPermutation.forward, drawCutoffLaw_map, PMF.map_comp, Function.comp_def,
    Option.map_map, programmedForwardNext, Equiv.symm_apply_apply] using result

/-- The programmed forward observer has the exact joint source law, including cutoff failure. -/
theorem programmedForwardSamples_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedForwardSamples attempts state.base.used memory).map
      (fun result => (overlayQueryValue state.overlay.length result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, programmedForwardNext state input value)) =
      drawCutoffLaw attempts (state.forward input) := by
  have reply := programmedForwardSamples_wordReply attempts memory oracle state input represented index operand fits overlayFits
  have joint := congrArg (PMF.map (Option.map fun word =>
    let value := sparseWordValue (2 ^ 128) (by decide) word
    (value, programmedForwardNext state input value))) reply
  simp only [PMF.map_comp, Function.comp_def, Option.map_map,
    sparseWordValue_encoded _ _ (by decide : 2 ^ 128 ≤ 2 ^ 256)] at joint
  exact joint.trans (programmedForward_recover attempts state input)

/-- Every accepted base reply has a valid finite word encoding. -/
theorem storedForwardSamples_valueWitness [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : SparsePermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : SparseMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val) (fits : 2 * state.used ≤ 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.used memory).support)
    (accepted : final.registers 7 ≠ 0#256) :
    ∃ value : Fin (2 ^ 128), final.registers 8 = BitVec.ofNat 256 value.val := by
  have reached : some (final.registers 8) ∈
      ((storedForwardSamples attempts state.used memory).map (fun result => queryValue result.1)).support := by
    apply (PMF.mem_support_map_iff _ _ _).mpr
    exact ⟨(final, cost), supported, by simp [queryValue, accepted]⟩
  rw [storedForwardSamples_wordReply attempts memory oracle state input represented index operand fits] at reached
  obtain ⟨value, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  cases value with
  | none => simp at same
  | some value => exact ⟨value.1, (Option.some.inj same).symm⟩

/-- The programmed RAM observer retains the old state after cutoff failure. -/
def programmedForwardMemoryState (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (memory : Memory) : ProgrammedPermutation (2 ^ 128) :=
  ((overlayQueryValue state.overlay.length memory).map fun word =>
    programmedForwardNext state input (sparseWordValue (2 ^ 128) (by decide) word)).getD state

/-- The final forward answer tail stores the exact programmed source state on every path. -/
theorem programmedForwardSamples_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) + 256 < 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.base.used memory).support) :
    ProgrammedMemory (publicForwardTail state.overlay.length final).1.ram oracle
      (programmedForwardMemoryState state input final) := by
  rw [publicForwardTail_ram]
  have base := storedForwardSamples_memory attempts memory final cost oracle state.base input represented.base index operand fits supported
  have overlay := storedForwardSamples_overlayMemory attempts memory final cost oracle state represented index (by omega) overlayFits supported
  by_cases failed : final.registers 7 = 0#256
  · simp only [programmedForwardMemoryState, overlayQueryValue, if_pos failed, Option.map_none, Option.getD_none]
    rw [sparseForwardMemoryState_failed state.base input final failed] at base
    exact ⟨base, overlay.2⟩
  · obtain ⟨value, valueWord⟩ := storedForwardSamples_valueWitness attempts memory final cost oracle state.base input
      represented.base index operand (by omega) supported failed
    have output := overlayForward_encoded final oracle state.overlay overlay.2 value overlay.1 valueWord (by decide)
    simp only [programmedForwardMemoryState, overlayQueryValue, if_neg failed, output, Option.map_some, Option.getD_some,
      sparseWordValue_encoded _ _ (by decide : 2 ^ 128 ≤ 2 ^ 256), programmedForwardNext, Equiv.symm_apply_apply]
    refine ⟨?_, overlay.2⟩
    simpa only [sparseForwardMemoryState, queryValue, if_neg failed, valueWord, Option.map_some, Option.getD_some,
      sparseWordValue_encoded _ _ (by decide : 2 ^ 128 ≤ 2 ^ 256)] using base

end Kriterion.ArgoMAC.ArithmeticSimulator
