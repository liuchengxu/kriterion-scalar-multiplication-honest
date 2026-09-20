import Proof.Privacy.Simulator.Arithmetic.QueryInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The hash query selects the final public oracle region. -/
def queryHashState (memory : Memory) : Memory :=
  { memory with registers := Function.update memory.registers 9 15748 }

/-- The hash source state records its tag and 254-bit operand. -/
def hashQueryMemory (base : Memory) (value : Nat) (rest : List Bool) : Memory :=
  let tagged := decodedInput base 3 4 (bits 254 value ++ rest)
  let selected := queryHashState (queryFamilyState (queryTagState tagged))
  queryOperandState (decodedInput selected 254 value rest)

/-- The hash reader returns before its final halt after 1821 instructions. -/
theorem queryInput_hashPrefix [BN254.FieldCertificate] (base : Memory)
    (value : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 3 4 ++ bits 254 value ++ rest) :
    runPrefix queryInput 1821 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨96, hashQueryMemory base value rest⟩, 1821)) := by
  let tagged := decodedInput base 3 4 (bits 254 value ++ rest)
  let selected := queryHashState (queryFamilyState (queryTagState tagged))
  let payload := decodedInput selected 254 value rest
  have tagRead := decodedInput_prefix 3 4 (queryInputLabels 0 14)
    queryInput_blocks.1 base (bits 254 value ++ rest) wire (by decide)
  change runPrefix queryInput 27 ⟨0, base⟩ = PMF.pure (some (false, ⟨14, tagged⟩, 27)) at tagRead
  have tagValue : (tagged.registers 0).toNat = 4 := by
    rw [decodedInput_value base 3 4 _ (by decide)]
    rfl
  have branch := queryInput_tag tagged
  simp only [tagValue, show ¬ 4 < 2 by decide, if_false] at branch
  have family := queryInput_family (queryTagState tagged)
  have familyValue : ((queryTagState tagged).registers 10).toNat = 4 := by
    simpa [queryTagState] using tagValue
  simp only [familyValue, lt_self_iff_false, if_false] at family
  have select : runPrefix queryInput 1 ⟨56, queryFamilyState (queryTagState tagged)⟩ =
      PMF.pure (some (false, ⟨57, selected⟩, 1)) := by
    simp [runPrefix, step, queryInput, selected, queryHashState, PMF.pure_map]
    rfl
  have payloadRead := decodedInput_prefix 254 value (queryInputLabels 57 71)
    queryInput_blocks.2.2.2.1 selected rest rfl (by decide)
  change runPrefix queryInput 1784 ⟨57, selected⟩ =
    PMF.pure (some (false, ⟨71, payload⟩, 1784)) at payloadRead
  change runPrefix queryInput (27 + (5 + (3 + (1 + (1784 + 1))))) ⟨0, base⟩ = _
  rw [prefix_add, tagRead, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, family, PMF.pure_bind]
  dsimp only
  rw [prefix_add, select, PMF.pure_bind]
  dsimp only
  rw [prefix_add, payloadRead, PMF.pure_bind]
  dsimp only
  simp [runPrefix, step, queryInput, queryOperandState, Arithmetic.eval,
    PMF.pure_map, hashQueryMemory, tagged, selected, payload]
  rfl

/-- The complete hash-query reader charges its final halt. -/
theorem queryInput_hashRun [BN254.FieldCertificate] (base : Memory)
    (value : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 3 4 ++ bits 254 value ++ rest) :
    run queryInput 1822 ⟨0, base⟩ =
      PMF.pure (some (⟨96, hashQueryMemory base value rest⟩, 1822)) := by
  rw [show 1822 = 1821 + 1 by decide, run_after_prefix,
    queryInput_hashPrefix base value rest wire, PMF.pure_bind]
  simp [run, step, queryInput, PMF.pure_map]

/-- The hash source state retains the parsed query and permanent RAM. -/
theorem hashQueryMemory_values (base : Memory) (value : Nat) (rest : List Bool)
    (valueBound : value < 2 ^ 254) :
    let result := hashQueryMemory base value rest
    result.registers 8 = BitVec.ofNat 256 value ∧
    result.registers 9 = 15748 ∧ result.registers 10 = 4 ∧
    result.bits 0 = rest ∧ result.ram = base.ram := by
  norm_num at valueBound
  simp [hashQueryMemory, queryOperandState, queryHashState, queryFamilyState, queryTagState,
    decodedInput, inputFinal, inputFrame, inputFold_value, bits_value, Nat.mod_eq_of_lt valueBound]

/-- The hash reader meets the public protocol interface and exact cost. -/
theorem queryInput_hashSource [BN254.FieldCertificate] (base : Memory)
    (value : Nat) (rest : List Bool) (valueBound : value < 2 ^ 254)
    (wire : base.bits 0 = bits 3 4 ++ bits 254 value ++ rest) :
    (run queryInput 1822 ⟨0, base⟩).map (Option.map fun result =>
      (result.1.memory.registers 8, result.1.memory.registers 9,
        result.1.memory.registers 10, result.1.memory.bits 0, result.1.memory.ram, result.2)) =
      PMF.pure (some (BitVec.ofNat 256 value, 15748, 4, rest, base.ram, 1822)) := by
  rw [queryInput_hashRun base value rest wire, PMF.pure_map]
  obtain ⟨operand, oracle, direction, suffix, ram⟩ := hashQueryMemory_values base value rest valueBound
  simp [operand, oracle, direction, suffix, ram]

end Kriterion.ArgoMAC.ArithmeticSimulator
