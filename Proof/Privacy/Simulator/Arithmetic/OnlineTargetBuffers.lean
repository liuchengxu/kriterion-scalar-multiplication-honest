import Proof.Privacy.Simulator.Arithmetic.OnlineMachinePrepare
import Proof.Privacy.Simulator.Arithmetic.OnlineSamplingWitness
import Proof.Privacy.Simulator.Arithmetic.RetargetPointPassSource

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine Security.SimulatorSampling
noncomputable section
attribute [local irreducible] onlineWords onlineSamplingMemory

/-- The source writer preserves each address outside its written words. -/
theorem storeDrawWords_other (pointer : Word) (start : Nat) (ram : Word → Word)
    (words : List Word) (address : Word)
    (separate : ∀ index, index < words.length → address ≠ pointer + BitVec.ofNat 256 (start + index)) :
    storeDrawWords pointer start ram words address = ram address := by
  induction words generalizing start ram with
  | nil => rfl
  | cons word rest ih =>
      rw [storeDrawWords, ih]
      · exact Function.update_of_ne (by simpa only [Nat.add_zero] using separate 0 (by simp)) _ _
      · intro index inside
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using separate (index + 1) (by simp; omega)

/-- A source interval preserves every lower natural address without word wraparound. -/
theorem storeDrawWords_before (pointer cell : Nat) (ram : Word → Word) (words : List Word)
    (lower : cell < pointer) (fits : pointer + words.length ≤ 2 ^ 256) :
    storeDrawWords (BitVec.ofNat 256 pointer) 0 ram words (BitVec.ofNat 256 cell) = ram (BitVec.ofNat 256 cell) := by
  apply storeDrawWords_other
  intro index inside same
  rw [Nat.zero_add, ← BitVec.ofNat_add] at same
  have values := congrArg BitVec.toNat same
  have cellFits : cell < 2 ^ 256 := by omega
  have indexFits : pointer + index < 2 ^ 256 := by omega
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt cellFits, Nat.mod_eq_of_lt indexFits] at values
  omega

/-- The online sampler preserves all source and input cells below its destination. -/
theorem onlineSamplingMemory_before [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost cell : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (lower : cell < onlineSampleBase) :
    final.ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  obtain ⟨sample, _, stored⟩ := onlineSamplingMemory_witness attempts memory final cost supported
  rw [stored, pointer]
  exact storeDrawWords_before onlineSampleBase cell memory.ram (onlineWords sample) lower
    (by rw [onlineWords_length]; decide)

/-- The source writer cannot change any cell in a public oracle region. -/
theorem storeDrawWords_public (pointer : Nat) (ram : Word → Word) (words : List Word)
    (privateFits : pointer + words.length ≤ 2 ^ 96)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    storeDrawWords (BitVec.ofNat 256 pointer) 0 ram words (oracleAddress oracle table offset) =
      ram (oracleAddress oracle table offset) := by
  apply storeDrawWords_other
  intro index inside
  rw [Nat.zero_add, ← BitVec.ofNat_add]
  exact oracleAddress_private_disjoint oracle table offset (pointer + index) fits (by omega)

/-- The actual online sampler preserves every public oracle cell. -/
theorem onlineSamplingMemory_public [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support)
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    final.ram (oracleAddress oracle table offset) = memory.ram (oracleAddress oracle table offset) := by
  obtain ⟨sample, _, stored⟩ := onlineSamplingMemory_witness attempts memory final cost supported
  rw [stored, pointer]
  exact storeDrawWords_public onlineSampleBase memory.ram (onlineWords sample)
    (by rw [onlineWords_length]; decide) oracle table offset fits

/-- The sampled memory retains the supplied output point in its input record. -/
theorem onlineSamplingMemory_selectedOutput [FieldCertificate] [GroupCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat)
    (pointer : memory.registers 10 = BitVec.ofNat 256 onlineSampleBase)
    (supported : (final, cost) ∈ (onlineSamplingMemory attempts memory).support) :
    selectedOutputPoint final.ram (BitVec.ofNat 256 onlineInputBase) =
      selectedOutputPoint memory.ram (BitVec.ofNat 256 onlineInputBase) := by
  have frame := onlineSamplingMemory_before attempts memory final cost
  have address (offset : Nat) : BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 offset =
      BitVec.ofNat 256 (onlineInputBase + offset) := (BitVec.ofNat_add _ _).symm
  unfold selectedOutputPoint
  change readPoint (fun register => if register = 5 then final.ram
    (BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 2) &&& 1
    else if register = 6 then final.ram (BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 3)
    else if register = 7 then final.ram (BitVec.ofNat 256 onlineInputBase + BitVec.ofNat 256 4) else 0) _ = _
  rw [address 2, address 3, address 4,
    frame (onlineInputBase + 2) pointer supported (by decide),
    frame (onlineInputBase + 3) pointer supported (by decide),
    frame (onlineInputBase + 4) pointer supported (by decide)]
  rfl

/-- Each target vector occupies 273 words in the dedicated target buffer. -/
theorem onlineTargetMemory_words [FieldCertificate] [GroupCertificate]
    (memory : Memory) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase)) :
    WordsAt (onlineTargetMemory memory output sample).ram (BitVec.ofNat 256 onlineTargetBase) 0
      (vectorWords homogeneousWords (Security.outputTargets output (Vector.ofFn sample.1) sample.2)) := by
  rw [onlineTargetMemory, outputTargetsMemory_ram, (onlineTargetSetup_state memory).1,
    (onlineTargetSetup_state memory).2.2.2.2.2]
  apply wordsAt_store
  have length : (vectorWords homogeneousWords (Security.outputTargets output (Vector.ofFn sample.1) sample.2)).length = 273 := by
    rw [← outputTargets_words]
    exact homogeneousRowsWords_length _ _ 91
  rw [length]
  decide

/-- The target writer preserves the original source and input buffers. -/
theorem onlineTargetMemory_before [FieldCertificate] [GroupCertificate]
    (memory : Memory) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (cell : Nat) (lower : cell < onlineTargetBase) :
    (onlineTargetMemory memory output sample).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  rw [onlineTargetMemory, outputTargetsMemory_ram, (onlineTargetSetup_state memory).1,
    (onlineTargetSetup_state memory).2.2.2.2.2]
  apply storeDrawWords_before onlineTargetBase cell _ _ lower
  rw [← outputTargets_words, homogeneousRowsWords_length]
  decide

/-- The target writer preserves every public oracle cell. -/
theorem onlineTargetMemory_public [FieldCertificate] [GroupCertificate]
    (memory : Memory) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (oracle : Fin 15749) (table : Fin 4) (offset : Nat) (fits : offset < 2 ^ 110) :
    (onlineTargetMemory memory output sample).ram (oracleAddress oracle table offset) =
      memory.ram (oracleAddress oracle table offset) := by
  rw [onlineTargetMemory, outputTargetsMemory_ram, (onlineTargetSetup_state memory).1,
    (onlineTargetSetup_state memory).2.2.2.2.2]
  apply storeDrawWords_public onlineTargetBase _ _ _ oracle table offset fits
  rw [← outputTargets_words, homogeneousRowsWords_length]
  decide

/-- The coordinate selector names each typed target field in RAM order. -/
def onlineTargetField [FieldCertificate] [GroupCertificate]
    (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (row : Fin FieldMacToECMac.outputMacCount) (coordinate : Fin 3) : BaseField :=
  let target := (Security.outputTargets output (Vector.ofFn sample.1) sample.2).get row
  ![target.x, target.y, target.z] coordinate

/-- Each target coordinate has the exact canonical field word. -/
theorem onlineTargetMemory_field [FieldCertificate] [GroupCertificate]
    (memory : Memory) (output : Point) (sample : (Fin 90 → Point) × (Fin 91 → NonZeroBase))
    (row : Fin FieldMacToECMac.outputMacCount) (coordinate : Fin 3) :
    (onlineTargetMemory memory output sample).ram
      (BitVec.ofNat 256 onlineTargetBase + BitVec.ofNat 256 (3 * row.val + coordinate.val)) =
      BitVec.ofNat 256 (onlineTargetField output sample row coordinate).val := by
  have stored := wordsAt_vector homogeneousWords 3 (by intro value; rfl)
    (Security.outputTargets output (Vector.ofFn sample.1) sample.2)
    (onlineTargetMemory memory output sample).ram (BitVec.ofNat 256 onlineTargetBase) 0 row
    (onlineTargetMemory_words memory output sample)
  have field := stored coordinate.val (by simp only [homogeneousWords, List.length_cons, List.length_nil]; exact coordinate.isLt)
  simp only [Nat.zero_add] at field
  fin_cases coordinate <;> simpa [onlineTargetField, homogeneousWords] using field

end
end Kriterion.ArgoMAC.ArithmeticSimulator
