import Proof.Privacy.Simulator.Arithmetic.PermutationForwardSource
import Proof.Privacy.Simulator.Arithmetic.OverlayMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Public draws retain cutoff failure as an explicit absent result. -/
noncomputable def drawCutoffLaw {A : Type} (attempts : Nat) : Draw A → PMF (Option A)
  | .pure value => PMF.pure (some value)
  | .uniform bound _ next => (Security.BoundedIntegerSampling.cutoff bound attempts).law.map (Option.map next)

/-- The cutoff interpreter preserves every deterministic source conversion. -/
theorem drawCutoffLaw_map {A B : Type} (attempts : Nat) (draw : Draw A) (convert : A → B) :
    drawCutoffLaw attempts (draw.map convert) = (drawCutoffLaw attempts draw).map (Option.map convert) := by
  cases draw <;> simp [drawCutoffLaw, Draw.map, PMF.pure_map, PMF.map_comp, Option.map_map, Function.comp_def]

/-- A positive narrow integer has its exact runtime range. -/
theorem runtimeRange_narrow (size : Nat) (positive : 0 < size) (fits : size < 2 ^ 256) :
    runtimeRange (BitVec.ofNat 256 size) = size := by
  have nonzero : BitVec.ofNat 256 size ≠ 0#256 := by
    intro equal
    have values := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, BitVec.toNat_ofNat, Nat.zero_mod] at values
    omega
  simp only [runtimeRange, if_neg nonzero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The sparse finite source and the word machine have the same forward reply law. -/
theorem permutationForwardSamples_finite [BN254.FieldCertificate] {size : Nat}
    (attempts : Nat) (state : SparsePermutation size) (input : Fin size) (memory : Memory)
    (sizeFits : size < 2 ^ 256)
    (used : memory.registers 0 = BitVec.ofNat 256 state.used)
    (domain : memory.registers 5 = BitVec.ofNat 256 size)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (inputCounter : memory.registers 2 = BitVec.ofNat 256 state.inputs.length)
    (outputCounter : memory.registers 4 = BitVec.ofNat 256 state.outputs.length)
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) (sparseWordPairs state.inputs))
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) (sparseWordPairs state.outputs))
    (safeCells : ∀ index, index < 2 * state.outputs.length →
      8 ≤ (memory.registers 3 + BitVec.ofNat 256 index).toNat) :
    (permutationForwardSamples attempts state.inputs.length state.outputs.length memory).map
      (fun result => queryValue result.1) =
      (drawCutoffLaw attempts (state.forward input)).map
        (Option.map fun result => BitVec.ofNat 256 result.1.val) := by
  have inputLength : (sparseWordPairs state.inputs).length = state.inputs.length := by simp [sparseWordPairs]
  have outputLength : (sparseWordPairs state.outputs).length = state.outputs.length := by simp [sparseWordPairs]
  have source := permutationForwardSamples_reply attempts (sparseWordPairs state.inputs)
    (sparseWordPairs state.outputs) memory
    (by rw [inputLength]; exact lt_of_le_of_lt (state.inputLength.trans state.within) sizeFits)
    (by rw [outputLength]; exact lt_of_le_of_lt (state.outputLength.trans state.within) sizeFits)
    (by simpa only [inputLength] using inputCounter) (by simpa only [outputLength] using outputCounter)
    inputStored outputStored (by simpa only [outputLength] using safeCells)
  simp only [inputLength, outputLength] at source
  rw [source]
  have position : (swaps (sparseWordPairs state.inputs)).symm (memory.registers 8) =
      BitVec.ofNat 256 (state.input.symm input).val := by
    rw [operand]
    exact encoded_swaps_inverse state.inputs input (Nat.le_of_lt sizeFits)
  have usedFits : state.used < 2 ^ 256 := lt_of_le_of_lt state.within sizeFits
  have positionFits : (state.input.symm input).val < 2 ^ 256 := lt_trans (state.input.symm input).isLt sizeFits
  rw [position, used]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedFits, Nat.mod_eq_of_lt positionFits]
  unfold SparsePermutation.forward
  by_cases known : (state.input.symm input).val < state.used
  · simp only [dif_pos known, if_pos known, drawCutoffLaw, PMF.pure_map, Option.map_some]
    congr 2
    exact encoded_swaps _ (finiteWord_injective size (Nat.le_of_lt sizeFits)) state.outputs (state.input.symm input)
  · simp only [dif_neg known, if_neg known, drawCutoffLaw, PMF.map_comp, Function.comp_def, Option.map_map]
    have room : state.used < size := by have := (state.input.symm input).isLt; omega
    have range : runtimeRange (memory.registers 5 - BitVec.ofNat 256 state.used) = size - state.used := by
      rw [domain, BitVec.ofNat_sub_ofNat_of_le size state.used usedFits state.within]
      exact runtimeRange_narrow _ (by omega) (by omega)
    rw [range]
    congr 1
    funext value
    cases value with
    | none => rfl
    | some rank =>
        simp only [Option.map_some]
        congr 1
        have chosen : BitVec.ofNat 256 rank.val + BitVec.ofNat 256 state.used =
            BitVec.ofNat 256 (state.suffix rank).val := by
          simp only [SparsePermutation.suffix, BitVec.ofNat_add, add_comm]
        rw [chosen]
        exact encoded_swaps _ (finiteWord_injective size (Nat.le_of_lt sizeFits)) state.outputs (state.suffix rank)

end Kriterion.ArgoMAC.ArithmeticSimulator
