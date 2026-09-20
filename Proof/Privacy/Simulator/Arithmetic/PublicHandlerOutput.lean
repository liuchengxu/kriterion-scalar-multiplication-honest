import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- A halt returns the current state in one charged instruction. -/
theorem handlerHalt [BN254.FieldCertificate] (host : Machine) (label : Fin (host.size + 1))
    (code : host.code[label.val] = .halt) (fuel : Nat) (memory : Memory) :
    run host (fuel + 1) ⟨label, memory⟩ = PMF.pure (some (⟨label, memory⟩, 1)) := by
  simp [run, step, code]

/-- A branch charges one instruction before the selected continuation. -/
theorem handlerBranch [BN254.FieldCertificate] (host : Machine)
    (label zero nonzero : Fin (host.size + 1)) (register : Register)
    (code : host.code[label.val] = .branch register zero nonzero) (fuel : Nat) (memory : Memory) :
    run host (fuel + 1) ⟨label, memory⟩ =
      (run host fuel ⟨if memory.registers register = 0#256 then zero else nonzero, memory⟩).map
        (Option.map fun result => (result.1, result.2 + 1)) := by
  simp [run, step, code, PMF.pure_bind]

/-- The final public label returns without a further memory change. -/
theorem publicHandler_halt [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (fuel + 1) ⟨1770, memory⟩ =
      PMF.pure (some (⟨1770, memory⟩, 1)) := by
  apply handlerHalt
  simp [publicHandler]
  try rfl

/-- The permutation output writes its wire answer and returns after 385 instructions. -/
theorem publicHandler_blockReply [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (publicHandler attempts) (385 + extra) ⟨616, memory⟩ =
      PMF.pure (some (⟨1770, executeLinear (wordOutput 128) memory⟩, 385)) := by
  have output := linear_continue (publicHandler attempts) (wordOutput 128) publicBlockOutputLabels
    (publicHandler_blockOutput attempts) memory (extra + 1)
  rw [wordOutput_length] at output
  change run (publicHandler attempts) (384 + (extra + 1)) ⟨616, memory⟩ = _ at output
  rw [show 385 + extra = 384 + (extra + 1) by omega, output]
  change (run (publicHandler attempts) (extra + 1) ⟨1770, executeLinear (wordOutput 128) memory⟩).map _ = _
  rw [publicHandler_halt, PMF.pure_map]
  rfl

/-- The hash output writes both wire blocks and returns after 771 instructions. -/
theorem publicHandler_hashReply [BN254.FieldCertificate] (attempts extra : Nat) (memory : Memory) :
    run (publicHandler attempts) (771 + extra) ⟨1000, memory⟩ =
      PMF.pure (some (⟨1770, executeLinear hashOutput memory⟩, 771)) := by
  have output := linear_continue (publicHandler attempts) hashOutput publicHashOutputLabels
    (publicHandler_hashOutput attempts) memory (extra + 1)
  rw [hashOutput_length] at output
  change run (publicHandler attempts) (770 + (extra + 1)) ⟨1000, memory⟩ = _ at output
  rw [show 771 + extra = 770 + (extra + 1) by omega, output]
  change (run (publicHandler attempts) (extra + 1) ⟨1770, executeLinear hashOutput memory⟩).map _ = _
  rw [publicHandler_halt, PMF.pure_map]
  rfl

/-- The one-word parser accepts the canonical low-bit encoding. -/
theorem blockWords_single (value : Nat) : words 128 1 (bits 128 value) =
    some #v[BitVec.ofNat 128 value] := by
  have encoded := words_encoded 128 1 #v[BitVec.ofNat 128 value]
  simp only [Vector.toList_mk, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    BitVec.toNat_ofNat, bits_mod] at encoded
  exact encoded

/-- The wire parser accepts exactly the low 128 bits from the permutation output. -/
theorem blockOutput_words (memory : Memory) (empty : memory.bits 3 = []) :
    words 128 1 ((executeLinear (wordOutput 128) memory).bits 3) =
      some #v[BitVec.ofNat 128 (memory.registers 8).toNat] := by
  rw [wordOutput_bits 128 memory (by decide), Function.update_self, wordOutput_protocol,
    empty, List.append_nil, blockWords_single]

/-- Every permutation query uses the same canonical one-block wire answer. -/
theorem blockOutput_answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (memory : Memory) (empty : memory.bits 3 = []) :
    match request with
    | .fixedForward index value =>
        answer (PublicQuery.fixedForward (FixedIndex := FixedIndex) (EncIndex := EncIndex) index value)
          ((executeLinear (wordOutput 128) memory).bits 3) =
            some (BitVec.ofNat 128 (memory.registers 8).toNat)
    | .fixedInverse index value =>
        answer (PublicQuery.fixedInverse (FixedIndex := FixedIndex) (EncIndex := EncIndex) index value)
          ((executeLinear (wordOutput 128) memory).bits 3) =
            some (BitVec.ofNat 128 (memory.registers 8).toNat)
    | .encForward index value =>
        answer (PublicQuery.encForward (FixedIndex := FixedIndex) (EncIndex := EncIndex) index value)
          ((executeLinear (wordOutput 128) memory).bits 3) =
            some (BitVec.ofNat 128 (memory.registers 8).toNat)
    | .encInverse index value =>
        answer (PublicQuery.encInverse (FixedIndex := FixedIndex) (EncIndex := EncIndex) index value)
          ((executeLinear (wordOutput 128) memory).bits 3) =
            some (BitVec.ofNat 128 (memory.registers 8).toNat)
    | .hash _ => False := by
  cases request with
  | fixedForward index value => simp [answer, blockOutput_words memory empty]; rfl
  | fixedInverse index value => simp [answer, blockOutput_words memory empty]; rfl
  | encForward index value => simp [answer, blockOutput_words memory empty]; rfl
  | encInverse index value => simp [answer, blockOutput_words memory empty]; rfl
  | hash input => exact (notHash input rfl).elim

/-- The forward handler checks the cutoff flag before it applies the overlay. -/
theorem publicHandler_forwardGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (fuel + 1) ⟨280, memory⟩ =
      (run (publicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 281, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  simp [publicHandler]
  try rfl

/-- The inverse handler checks the cutoff flag before it emits an answer. -/
theorem publicHandler_inverseGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (fuel + 1) ⟨541, memory⟩ =
      (run (publicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 616, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  simp [publicHandler]
  try rfl

/-- The hash handler checks its success flag before it emits both answer blocks. -/
theorem publicHandler_hashGate [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (fuel + 1) ⟨615, memory⟩ =
      (run (publicHandler attempts) fuel
        ⟨if memory.registers 7 = 0#256 then 1771 else 1000, memory⟩).map
          (Option.map fun result => (result.1, result.2 + 1)) := by
  apply handlerBranch
  simp [publicHandler]
  try rfl

/-- The cutoff return does not write an answer. -/
theorem publicHandler_abort [BN254.FieldCertificate] (attempts fuel : Nat) (memory : Memory) :
    run (publicHandler attempts) (fuel + 1) ⟨1771, memory⟩ =
      PMF.pure (some (⟨1771, memory⟩, 1)) := by
  apply handlerHalt
  simp [publicHandler]
  try rfl

/-- Every public answer parser rejects the empty cutoff output. -/
theorem publicHandler_abortAnswer {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) : answer request [] = none := by
  cases request <;> simp [answer, words] <;> rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
