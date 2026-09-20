import Proof.Privacy.Simulator.Arithmetic.QueryInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The source state records the three input blocks and their fixed register moves. -/
def fixedQueryMemory (base : Memory) (tag index value : Nat) (rest : List Bool) : Memory :=
  let tagged := decodedInput base 3 tag (bits 14 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryTagState tagged) 14 index (bits 128 value ++ rest)
  queryOperandState (decodedInput (queryFixedState indexed) 128 value rest)

/-- Both fixed-permutation directions return after 1041 instructions. -/
theorem queryInput_fixedPrefix [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagBound : tag < 2)
    (wire : base.bits 0 = bits 3 tag ++ bits 14 index ++ bits 128 value ++ rest) :
    runPrefix queryInput 1041 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨96, fixedQueryMemory base tag index value rest⟩, 1041)) := by
  let tagged := decodedInput base 3 tag (bits 14 index ++ bits 128 value ++ rest)
  let indexed := decodedInput (queryTagState tagged) 14 index (bits 128 value ++ rest)
  let payload := decodedInput (queryFixedState indexed) 128 value rest
  have tagRead := decodedInput_prefix 3 tag (queryInputLabels 0 14)
    queryInput_blocks.1 base (bits 14 index ++ bits 128 value ++ rest) wire (by decide)
  change runPrefix queryInput 27 ⟨0, base⟩ = PMF.pure (some (false, ⟨14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = tag := by
    rw [decodedInput_value base 3 tag _ (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (lt_trans tagBound (by decide : 2 < 2 ^ 256))]
  have branch := queryInput_tag tagged
  rw [tagValue, if_pos tagBound] at branch
  have indexRead := decodedInput_prefix 14 index (queryInputLabels 19 33)
    queryInput_blocks.2.1 (queryTagState tagged) (bits 128 value ++ rest) rfl (by decide)
  change runPrefix queryInput 104 ⟨19, queryTagState tagged⟩ =
    PMF.pure (some (false, ⟨33, indexed⟩, 104)) at indexRead
  have payloadRead := decodedInput_prefix 128 value (queryInputLabels 80 94)
    queryInput_blocks.2.2.2.2 (queryFixedState indexed) rest rfl (by decide)
  change runPrefix queryInput 902 ⟨80, queryFixedState indexed⟩ =
    PMF.pure (some (false, ⟨94, payload⟩, 902)) at payloadRead
  change runPrefix queryInput (27 + (5 + (104 + (2 + (902 + 1))))) ⟨0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, indexRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, queryInput_fixedIndex, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, fixedQueryMemory, tagged, indexed, payload]
  rfl

/-- The complete fixed-query reader includes its final halt. -/
theorem queryInput_fixedRun [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagBound : tag < 2)
    (wire : base.bits 0 = bits 3 tag ++ bits 14 index ++ bits 128 value ++ rest) :
    run queryInput 1042 ⟨0, base⟩ =
      PMF.pure (some (⟨96, fixedQueryMemory base tag index value rest⟩, 1042)) := by
  rw [show 1042 = 1041 + 1 by decide, run_after_prefix,
    queryInput_fixedPrefix base tag index value rest tagBound wire, PMF.pure_bind]
  simp [run, step, queryInput, PMF.pure_map]

/-- The source state retains the parsed tag, index, operand, suffix, and RAM. -/
theorem fixedQueryMemory_values (base : Memory) (tag index value : Nat) (rest : List Bool)
    (tagBound : tag < 2) (indexBound : index < 15240) (valueBound : value < 2 ^ 128) :
    let result := fixedQueryMemory base tag index value rest
    result.registers 8 = BitVec.ofNat 256 value ∧
    result.registers 9 = BitVec.ofNat 256 index ∧
    result.registers 10 = BitVec.ofNat 256 tag ∧
    result.bits 0 = rest ∧ result.ram = base.ram := by
  have tagFits : tag < 2 ^ 3 := by omega
  have indexFits : index < 2 ^ 14 := by omega
  norm_num at tagFits indexFits valueBound
  simp [fixedQueryMemory, queryOperandState, queryFixedState, queryTagState,
    decodedInput, inputFinal, inputFrame, inputFold_value, bits_value,
    Nat.mod_eq_of_lt tagFits, Nat.mod_eq_of_lt indexFits, Nat.mod_eq_of_lt valueBound]

/-- The fixed-query reader meets the public protocol interface and exact cost. -/
theorem queryInput_fixedSource [BN254.FieldCertificate] (base : Memory)
    (tag index value : Nat) (rest : List Bool) (tagBound : tag < 2)
    (indexBound : index < 15240) (valueBound : value < 2 ^ 128)
    (wire : base.bits 0 = bits 3 tag ++ bits 14 index ++ bits 128 value ++ rest) :
    (run queryInput 1042 ⟨0, base⟩).map (Option.map fun result =>
      (result.1.memory.registers 8, result.1.memory.registers 9,
        result.1.memory.registers 10, result.1.memory.bits 0, result.1.memory.ram, result.2)) =
      PMF.pure (some (BitVec.ofNat 256 value, BitVec.ofNat 256 index,
        BitVec.ofNat 256 tag, rest, base.ram, 1042)) := by
  rw [queryInput_fixedRun base tag index value rest tagBound wire, PMF.pure_map]
  obtain ⟨operand, oracle, direction, suffix, ram⟩ :=
    fixedQueryMemory_values base tag index value rest tagBound indexBound valueBound
  simp [operand, oracle, direction, suffix, ram]

end Kriterion.ArgoMAC.ArithmeticSimulator
