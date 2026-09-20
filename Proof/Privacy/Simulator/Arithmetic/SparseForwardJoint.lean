import Proof.Privacy.Simulator.Arithmetic.SparseForwardSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The finite observer decodes one word inside the declared source domain. -/
def sparseWordValue (size : Nat) (positive : 0 < size) (value : Word) : Fin size :=
  ⟨value.toNat % size, Nat.mod_lt _ positive⟩

/-- The finite observer preserves every valid encoded source value. -/
theorem sparseWordValue_encoded {size : Nat} (positive : 0 < size) (value : Fin size)
    (fits : size ≤ 2 ^ 256) :
    sparseWordValue size positive (BitVec.ofNat 256 value.val) = value := by
  apply Fin.ext
  simp only [sparseWordValue, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (lt_of_lt_of_le value.isLt fits), Nat.mod_eq_of_lt value.isLt]

/-- A forward reply determines the complete next sparse state. -/
def sparseForwardNext {size : Nat} (state : SparsePermutation size) (input output : Fin size) :
    SparsePermutation size :=
  if known : (state.input.symm input).val < state.used then state
  else state.extend (by have := (state.input.symm input).isLt; omega)
    (state.input.symm input) (state.output.symm output)

/-- The forward source retains its full state update after the reply observer. -/
theorem sparseForward_recover {size : Nat} (attempts : Nat) (state : SparsePermutation size)
    (input : Fin size) :
    (drawCutoffLaw attempts (state.forward input)).map
      (Option.map fun result => (result.1, sparseForwardNext state input result.1)) =
      drawCutoffLaw attempts (state.forward input) := by
  unfold SparsePermutation.forward
  dsimp only
  split
  next known => simp [drawCutoffLaw, PMF.pure_map, sparseForwardNext, known]
  next fresh =>
    simp only [drawCutoffLaw, PMF.map_comp, Function.comp_def, Option.map_map]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some rank => simp [sparseForwardNext, fresh]

/-- The finite word observer preserves the full joint cutoff law, including failure. -/
theorem sparseForward_wordJoint {size : Nat} (attempts : Nat) (state : SparsePermutation size)
    (input : Fin size) (sizeFits : size ≤ 2 ^ 256) :
    ((drawCutoffLaw attempts (state.forward input)).map
      (Option.map fun result => BitVec.ofNat 256 result.1.val)).map
        (Option.map fun word =>
          let value := sparseWordValue size (by have := input.isLt; omega) word
          (value, sparseForwardNext state input value)) =
      drawCutoffLaw attempts (state.forward input) := by
  rw [PMF.map_comp]
  simp only [Function.comp_def, Option.map_map, sparseWordValue_encoded _ _ sizeFits]
  exact sparseForward_recover attempts state input

/-- The compiled forward source has the complete finite reply and next-state distribution. -/
theorem permutationForwardSamples_joint [BN254.FieldCertificate] {size : Nat}
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
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue size (by have := input.isLt; omega) word
        (value, sparseForwardNext state input value)) =
      drawCutoffLaw attempts (state.forward input) := by
  have reply := permutationForwardSamples_finite attempts state input memory sizeFits used domain operand
    inputCounter outputCounter inputStored outputStored safeCells
  have joint := congrArg (PMF.map (Option.map fun word =>
    let value := sparseWordValue size (by have := input.isLt; omega) word
    (value, sparseForwardNext state input value))) reply
  rw [sparseForward_wordJoint attempts state input (Nat.le_of_lt sizeFits)] at joint
  simpa only [PMF.map_comp, Function.comp_def] using joint

end Kriterion.ArgoMAC.ArithmeticSimulator
