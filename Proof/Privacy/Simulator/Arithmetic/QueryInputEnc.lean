import Proof.Privacy.Simulator.Arithmetic.QueryInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The source state records the three input blocks and their encryption index move. -/
def encQueryMemory (base : Memory) (tag index value : Nat) (rest : List Bool) : Memory :=
  let tagged := decodedInput base 3 tag (bits 9 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryFamilyState (queryTagState tagged)) 9 index (bits 128 value ++ rest)
  queryOperandState (decodedInput (queryEncState indexed) 128 value rest)

/-- Both encryption-permutation directions return after 1010 instructions. -/
theorem queryInput_encPrefix [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagLower : 2 ≤ tag) (tagBound : tag < 4)
    (wire : base.bits 0 = bits 3 tag ++ bits 9 index ++ bits 128 value ++ rest) :
    runPrefix queryInput 1010 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨96, encQueryMemory base tag index value rest⟩, 1010)) := by
  let tagged := decodedInput base 3 tag (bits 9 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryFamilyState (queryTagState tagged)) 9 index (bits 128 value ++ rest)
  let payload := decodedInput (queryEncState indexed) 128 value rest
  have tagRead := decodedInput_prefix 3 tag (queryInputLabels 0 14)
    queryInput_blocks.1 base (bits 9 index ++ bits 128 value ++ rest) wire (by decide)
  change runPrefix queryInput 27 ⟨0, base⟩ = PMF.pure (some (false, ⟨14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = tag := by
    rw [decodedInput_value base 3 tag _ (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans tagBound (by decide : 4 < 2 ^ 256))]
  have branch := queryInput_tag tagged
  rw [tagValue, if_neg (Nat.not_lt.mpr tagLower)] at branch
  have family := queryInput_family (queryTagState tagged)
  have familyValue : ((queryTagState tagged).registers 10).toNat = tag := by
    simpa [queryTagState] using tagValue
  rw [familyValue, if_pos tagBound] at family
  have indexRead := decodedInput_prefix 9 index (queryInputLabels 38 52)
    queryInput_blocks.2.2.1 (queryFamilyState (queryTagState tagged)) (bits 128 value ++ rest) rfl (by decide)
  change runPrefix queryInput 69 ⟨38, queryFamilyState (queryTagState tagged)⟩ =
    PMF.pure (some (false, ⟨52, indexed⟩, 69)) at indexRead
  have payloadRead := decodedInput_prefix 128 value (queryInputLabels 80 94)
    queryInput_blocks.2.2.2.2 (queryEncState indexed) rest rfl (by decide)
  change runPrefix queryInput 902 ⟨80, queryEncState indexed⟩ =
    PMF.pure (some (false, ⟨94, payload⟩, 902)) at payloadRead
  change runPrefix queryInput (27 + (5 + (3 + (69 + (3 + (902 + 1)))))) ⟨0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, family, PMF.pure_bind]
  dsimp only
  rw [prefix_add, indexRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, queryInput_encIndex, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, encQueryMemory, tagged, indexed, payload]
  rfl

/-- The complete encryption-query reader includes its final halt. -/
theorem queryInput_encRun [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagLower : 2 ≤ tag) (tagBound : tag < 4)
    (wire : base.bits 0 = bits 3 tag ++ bits 9 index ++ bits 128 value ++ rest) :
    run queryInput 1011 ⟨0, base⟩ =
      PMF.pure (some (⟨96, encQueryMemory base tag index value rest⟩, 1011)) := by
  rw [show 1011 = 1010 + 1 by decide, run_after_prefix,
    queryInput_encPrefix base tag index value rest tagLower tagBound wire, PMF.pure_bind]
  simp [run, step, queryInput, PMF.pure_map]

/-- The source state retains the parsed tag, index, operand, suffix, and RAM. -/
theorem encQueryMemory_values (base : Memory) (tag index value : Nat) (rest : List Bool)
    (tagBound : tag < 4) (indexBound : index < 508) (valueBound : value < 2 ^ 128) :
    let result := encQueryMemory base tag index value rest
    result.registers 8 = BitVec.ofNat 256 value ∧
    result.registers 9 = BitVec.ofNat 256 (index + 15240) ∧
    result.registers 10 = BitVec.ofNat 256 tag ∧
    result.bits 0 = rest ∧ result.ram = base.ram := by
  have tagFits : tag < 2 ^ 3 := by omega
  have indexFits : index < 2 ^ 9 := by omega
  norm_num at tagFits indexFits valueBound
  simp [encQueryMemory, queryOperandState, queryEncState, queryFamilyState, queryTagState,
    decodedInput, inputFinal, inputFrame, inputFold_value, bits_value,
    BitVec.ofNat_add, Nat.mod_eq_of_lt tagFits, Nat.mod_eq_of_lt indexFits, Nat.mod_eq_of_lt valueBound]

/-- The encryption-query reader meets the public protocol interface and exact cost. -/
theorem queryInput_encSource [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagLower : 2 ≤ tag) (tagBound : tag < 4)
    (indexBound : index < 508) (valueBound : value < 2 ^ 128)
    (wire : base.bits 0 = bits 3 tag ++ bits 9 index ++ bits 128 value ++ rest) :
    (run queryInput 1011 ⟨0, base⟩).map (Option.map fun result =>
      (result.1.memory.registers 8, result.1.memory.registers 9,
        result.1.memory.registers 10, result.1.memory.bits 0, result.1.memory.ram, result.2)) =
      PMF.pure (some (BitVec.ofNat 256 value, BitVec.ofNat 256 (index + 15240),
        BitVec.ofNat 256 tag, rest, base.ram, 1011)) := by
  rw [queryInput_encRun base tag index value rest tagLower tagBound wire, PMF.pure_map]
  obtain ⟨operand, oracle, direction, suffix, ram⟩ :=
    encQueryMemory_values base tag index value rest tagBound indexBound valueBound
  simp [operand, oracle, direction, suffix, ram]

end Kriterion.ArgoMAC.ArithmeticSimulator
