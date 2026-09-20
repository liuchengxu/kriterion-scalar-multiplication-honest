import Proof.Privacy.Simulator.Arithmetic.StoredForwardWord
import Proof.Privacy.Simulator.Arithmetic.OracleMemoryCongr
import Proof.Privacy.Simulator.Arithmetic.StoredForwardFrame

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The programmed oracle relation stores its sparse base and its ordered output swaps. -/
structure ProgrammedMemory (ram : Word → Word) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) : Prop where
  base : SparseMemory ram oracle state.base
  overlay : OverlayMemory ram oracle state.overlay

/-- The forward observer applies the output swaps only after an accepted base reply. -/
def overlayQueryValue (count : Nat) (memory : Memory) : Option Word :=
  if memory.registers 7 = 0#256 then none else some ((overlayForwardScan count memory).1.registers 8)

/-- Every supported forward base reply retains the complete overlay memory relation. -/
theorem storedForwardSamples_overlayMemory (attempts : Nat) (memory final : Memory) (cost : Nat)
    (oracle : Fin 15749) (state : ProgrammedPermutation (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts state.base.used memory).support) :
    final.registers 6 = oracleAddress oracle 0 0 ∧ OverlayMemory final.ram oracle state.overlay := by
  have retained := storedForwardSamples_overlayFrame attempts state.base.used memory final cost supported
    oracle index represented.base.count fits
  exact ⟨retained.1, OverlayMemory.congr memory.ram final.ram oracle state.overlay represented.overlay overlayFits retained.2⟩

/-- The forward observer applies the represented word permutation to the base reply. -/
theorem overlayQueryValue_source (memory : Memory) (oracle : Fin 15749)
    (pairs : List (Fin (2 ^ 128) × Fin (2 ^ 128)))
    (represented : OverlayMemory memory.ram oracle pairs)
    (header : memory.registers 6 = oracleAddress oracle 0 0) :
    overlayQueryValue pairs.length memory = (queryValue memory).map (swaps (sparseWordPairs pairs)) := by
  have scanned := overlayForward_source memory (sparseWordPairs pairs)
    (by simpa only [overlayBase_address memory oracle header] using represented.stored)
  simp only [sparseWordPairs, List.length_map] at scanned
  by_cases failed : memory.registers 7 = 0#256
  · simp [overlayQueryValue, queryValue, failed]
  · simp only [overlayQueryValue, queryValue, if_neg failed, Option.map_some]
    exact congrArg some scanned

/-- The complete programmed forward reply has the exact operational cutoff law. -/
theorem programmedForwardSamples_wordReply [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (oracle : Fin 15749)
    (state : ProgrammedPermutation (2 ^ 128)) (input : Fin (2 ^ 128))
    (represented : ProgrammedMemory memory.ram oracle state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.base.used + 1) ≤ 2 ^ 110) (overlayFits : 256 + 2 * state.overlay.length < 2 ^ 110) :
    (storedForwardSamples attempts state.base.used memory).map
      (fun result => overlayQueryValue state.overlay.length result.1) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  have observed : (storedForwardSamples attempts state.base.used memory).map
      (fun result => overlayQueryValue state.overlay.length result.1) =
      ((storedForwardSamples attempts state.base.used memory).map (fun result => queryValue result.1)).map
        (Option.map (swaps (sparseWordPairs state.overlay))) := by
    rw [PMF.map_comp]
    change (storedForwardSamples attempts state.base.used memory).bind _ =
      (storedForwardSamples attempts state.base.used memory).bind _
    apply Security.ThreePhase.bind_eq_on_support
    intro result supported
    have retained := storedForwardSamples_overlayMemory attempts memory result.1 result.2 oracle state represented index fits overlayFits supported
    exact congrArg PMF.pure (overlayQueryValue_source result.1 oracle state.overlay retained.2 retained.1)
  rw [observed, storedForwardSamples_wordReply attempts memory oracle state.base input represented.base index operand (by omega)]
  rw [ProgrammedPermutation.forward, drawCutoffLaw_map, PMF.map_comp, PMF.map_comp]
  simp only [Function.comp_def, Option.map_map]
  congr 1
  funext result
  cases result with
  | none => rfl
  | some result =>
      simp only [Option.map_some]
      exact congrArg some (encoded_swaps _ (finiteWord_injective (2 ^ 128) (by decide)) state.overlay result.1)

end Kriterion.ArgoMAC.ArithmeticSimulator
