import Proof.Privacy.Simulator.Arithmetic.StoredInverseWord
import Proof.Privacy.Simulator.Arithmetic.StoredInverseOverlay
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerRam

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Inverse preparation retains the complete programmed oracle memory relation. -/
theorem publicInversePrepared_memory (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (represented : ProgrammedMemory memory.ram oracle state)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    ProgrammedMemory (publicInversePrepared state.overlay.length memory).ram oracle state := by
  refine ⟨SparseMemory.congr memory.ram _ oracle state.base represented.base fits
    (publicInversePrepared_public state.overlay.length memory oracle), ?_⟩
  exact OverlayMemory.congr memory.ram _ oracle state.overlay represented.overlay overlayFits
    (publicInversePrepared_public state.overlay.length memory oracle 2)

/-- Inverse preparation removes the exact finite output overlay from the operand. -/
theorem publicInversePrepared_operand (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (publicInversePrepared state.overlay.length memory).registers 8 =
      BitVec.ofNat 256 ((swaps state.overlay).symm input).val := by
  have loaded := OverlayMemory.congr memory.ram (oracleLoaded memory).ram oracle state.overlay represented.overlay
    overlayFits (oracleLoadRam_public memory oracle 2)
  have decoded := overlayInverse_encoded (oracleLoaded memory) oracle state.overlay loaded input
    (oracleLoaded_header memory oracle index) ((oracleLoaded_query memory).1.trans operand) (by decide)
  have preserved : ∀ source : Memory, (queryRestored source).registers 8 = source.registers 8 := by
    intro source
    simp [queryRestored]
  exact (preserved _).trans decoded

/-- The programmed inverse handler has the exact operational word-reply law. -/
theorem programmedInverseSamples_wordReply [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedInverseSamples attempts state.base.used (publicInversePrepared state.overlay.length memory)).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.inverse input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  have prepared := publicInversePrepared_memory memory oracle state represented fits overlayFits
  have reply := storedInverseSamples_wordReply attempts (publicInversePrepared state.overlay.length memory)
    oracle state.base ((swaps state.overlay).symm input) prepared.base
    ((publicInversePrepared_data state.overlay.length memory).2.trans index)
    (publicInversePrepared_operand memory oracle state input represented index operand overlayFits) fits
  simpa only [ProgrammedPermutation.inverse, drawCutoffLaw_map, PMF.map_comp, Function.comp_def, Option.map_map] using reply

/-- The inverse reply determines the next base state in its original orientation. -/
def programmedInverseNext (state : ProgrammedPermutation (2 ^ 128)) (input output : Fin (2 ^ 128)) :
    ProgrammedPermutation (2 ^ 128) :=
  { state with base := (sparseForwardNext state.base.reverse ((swaps state.overlay).symm input) output).reverse }

/-- The programmed inverse observer has the complete joint operational cutoff law. -/
theorem programmedInverseSamples_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * state.base.used ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedInverseSamples attempts state.base.used (publicInversePrepared state.overlay.length memory)).map
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, programmedInverseNext state input value)) =
      drawCutoffLaw attempts (state.inverse input) := by
  have prepared := publicInversePrepared_memory memory oracle state represented fits overlayFits
  have base := storedInverseSamples_joint attempts (publicInversePrepared state.overlay.length memory)
    oracle state.base ((swaps state.overlay).symm input) prepared.base
    ((publicInversePrepared_data state.overlay.length memory).2.trans index)
    (publicInversePrepared_operand memory oracle state input represented index operand overlayFits) fits
  have joint := congrArg (PMF.map (Option.map fun result : Fin (2 ^ 128) × SparsePermutation (2 ^ 128) =>
    (result.1, {state with base := result.2}))) base
  simpa only [ProgrammedPermutation.inverse, drawCutoffLaw_map, PMF.map_comp, Function.comp_def,
    Option.map_map, programmedInverseNext] using joint

/-- The inverse RAM observer retains the old state after cutoff failure. -/
def programmedInverseMemoryState (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (memory : Memory) : ProgrammedPermutation (2 ^ 128) :=
  ((queryValue memory).map fun word =>
    programmedInverseNext state input (sparseWordValue (2 ^ 128) (by decide) word)).getD state

/-- The final inverse answer tail stores the same programmed state as the joint source law. -/
theorem programmedInverseSamples_memory [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) + 256 < 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈
      (storedInverseSamples attempts state.base.used (publicInversePrepared state.overlay.length memory)).support) :
    ProgrammedMemory (publicInverseTail final).1.ram oracle (programmedInverseMemoryState state input final) := by
  rw [publicInverseTail_ram]
  have prepared := publicInversePrepared_memory memory oracle state represented (by omega) overlayFits
  have preparedIndex := (publicInversePrepared_data state.overlay.length memory).2.trans index
  have base := storedInverseSamples_memory attempts (publicInversePrepared state.overlay.length memory) final cost oracle
    state.base ((swaps state.overlay).symm input) prepared.base preparedIndex
    (publicInversePrepared_operand memory oracle state input represented index operand overlayFits) fits supported
  have retained := storedInverseSamples_overlayFrame attempts state.base.used (publicInversePrepared state.overlay.length memory)
    final cost supported oracle preparedIndex prepared.base.count (by omega)
  have overlay := OverlayMemory.congr _ final.ram oracle state.overlay prepared.overlay overlayFits retained
  unfold sparseInverseMemoryState sparseForwardMemoryState at base
  unfold programmedInverseMemoryState
  cases observed : queryValue final with
  | none =>
      simp only [observed, Option.map_none, Option.getD_none, SparsePermutation.reverse_reverse] at base ⊢
      exact ⟨base, overlay⟩
  | some word =>
      simp only [observed, Option.map_some, Option.getD_some] at base ⊢
      exact ⟨base, overlay⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
