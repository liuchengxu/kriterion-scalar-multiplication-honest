import Proof.Privacy.Simulator.Arithmetic.OracleFamilyMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- Every forward sample retains the complete oracle family, including cutoff paths. -/
theorem storedForwardSamples_family [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedForwardSamples attempts (state.permutations oracle).base.used memory).support) :
    OracleFamilyMemory (publicForwardTail (state.permutations oracle).overlay.length final).1.ram
      (state.updatePermutation oracle (programmedForwardMemoryState (state.permutations oracle) input final)) := by
  apply OracleFamilyMemory.updatePermutation memory.ram _ state oracle _ represented capacity
  · exact programmedForwardSamples_memory attempts memory final cost oracle.castSucc _ input
      (represented.permutations oracle) index operand fits (capacity.overlay oracle) supported
  · intro other separate table offset offsetFits
    rw [publicForwardTail_ram]
    exact storedForwardSamples_otherOracle attempts _ memory final cost supported oracle.castSucc other separate
      table offset offsetFits index (represented.permutations oracle).base.count (by omega)

/-- Every inverse sample retains the complete oracle family, including cutoff paths. -/
theorem storedInverseSamples_family [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (storedInverseSamples attempts (state.permutations oracle).base.used
      (publicInversePrepared (state.permutations oracle).overlay.length memory)).support) :
    OracleFamilyMemory (publicInverseTail final).1.ram
      (state.updatePermutation oracle (programmedInverseMemoryState (state.permutations oracle) input final)) := by
  apply OracleFamilyMemory.updatePermutation memory.ram _ state oracle _ represented capacity
  · exact programmedInverseSamples_memory attempts memory final cost oracle.castSucc _ input
      (represented.permutations oracle) index operand fits (capacity.overlay oracle) supported
  · intro other separate table offset offsetFits
    rw [publicInverseTail_ram]
    have prepared := publicInversePrepared_memory memory oracle.castSucc _ (represented.permutations oracle)
      (capacity.base oracle) (capacity.overlay oracle)
    have preserved := storedInverseSamples_otherOracle attempts _
      (publicInversePrepared (state.permutations oracle).overlay.length memory) final cost supported
      oracle.castSucc other separate table offset offsetFits
      ((publicInversePrepared_data _ memory).2.trans index) prepared.base.count (by omega)
    exact preserved.trans (publicInversePrepared_public _ memory other table offset offsetFits)

/-- Every hash sample retains all permutations and the exact updated hash table. -/
theorem hashHandlerSamples_family (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (key : BN254.BaseField) (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 15748) (operand : memory.registers 8 = hashKeyWord key)
    (fits : 2 * (state.hash.length + 1) + 256 < 2 ^ 110)
    (supported : (final, cost) ∈ (hashHandlerSamples state.hash.length memory).support) :
    OracleFamilyMemory (publicHashTail final).1.ram
      (state.updateHash (hashNextTable state.hash key (final.registers 8).toFin)) := by
  rw [publicHashTail_ram]
  apply OracleFamilyMemory.updateHash memory.ram final.ram state _ represented capacity
  · exact hashHandlerSamples_memory hashKeyWord hashKeyWord_injective state.hash key memory final cost 15748
      represented.hash index operand fits supported
  · intro other separate table offset offsetFits
    have counter : memory.ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.hash.length := by
      simpa only [hashWordPairs, List.length_map] using represented.hash.count
    exact hashHandlerSamples_otherOracle state.hash.length memory final cost supported 15748 other separate
      table offset offsetFits index counter (by omega)

/-- The forward RAM observer has the exact complete family cutoff law. -/
theorem storedForwardSamples_family_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110) :
    (storedForwardSamples attempts (state.permutations oracle).base.used memory).map
      (fun result => (overlayQueryValue (state.permutations oracle).overlay.length result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, state.updatePermutation oracle (programmedForwardNext (state.permutations oracle) input value))) =
      (drawCutoffLaw attempts ((state.permutations oracle).forward input)).map
        (Option.map fun result => (result.1, state.updatePermutation oracle result.2)) := by
  have law := congrArg (PMF.map (Option.map fun result : Fin (2 ^ 128) × ProgrammedPermutation (2 ^ 128) =>
    (result.1, state.updatePermutation oracle result.2)))
    (programmedForwardSamples_joint attempts memory oracle.castSucc _ input (represented.permutations oracle)
      index operand fits overlayFits)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map] using law

/-- The inverse RAM observer has the exact complete family cutoff law. -/
theorem storedInverseSamples_family_joint [BN254.FieldCertificate]
    (attempts : Nat) (memory : Memory) (state : SparseOracleFamily) (oracle : Fin 15748)
    (input : Fin (2 ^ 128)) (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * (state.permutations oracle).base.used ≤ 2 ^ 110)
    (overlayFits : 256 + 2 * (state.permutations oracle).overlay.length < 2 ^ 110) :
    (storedInverseSamples attempts (state.permutations oracle).base.used
      (publicInversePrepared (state.permutations oracle).overlay.length memory)).map
      (fun result => (queryValue result.1).map fun word =>
        let value := sparseWordValue (2 ^ 128) (by decide) word
        (value, state.updatePermutation oracle (programmedInverseNext (state.permutations oracle) input value))) =
      (drawCutoffLaw attempts ((state.permutations oracle).inverse input)).map
        (Option.map fun result => (result.1, state.updatePermutation oracle result.2)) := by
  have law := congrArg (PMF.map (Option.map fun result : Fin (2 ^ 128) × ProgrammedPermutation (2 ^ 128) =>
    (result.1, state.updatePermutation oracle result.2)))
    (programmedInverseSamples_joint attempts memory oracle.castSucc _ input (represented.permutations oracle)
      index operand fits overlayFits)
  simpa only [PMF.map_comp, Function.comp_def, Option.map_map] using law

/-- The hash RAM observer has the exact complete family source law. -/
theorem hashHandlerSamples_family_joint (memory : Memory) (state : SparseOracleFamily) (key : BN254.BaseField)
    (represented : OracleFamilyMemory memory.ram state)
    (index : memory.registers 9 = BitVec.ofNat 256 15748) (operand : memory.registers 8 = hashKeyWord key)
    (fits : 2 * state.hash.length ≤ 2 ^ 110) :
    (hashHandlerSamples state.hash.length memory).map
      (fun result => let value := (result.1.registers 8).toFin
        (value, state.updateHash (hashNextTable state.hash key value))) =
      (state.hash.query (by decide) key).distribution.map (fun result => (result.1, state.updateHash result.2)) := by
  have law := congrArg (PMF.map (fun result : Fin (2 ^ 256) × HashTable BN254.BaseField (2 ^ 256) =>
    (result.1, state.updateHash result.2)))
    (hashHandlerSamples_joint hashKeyWord hashKeyWord_injective state.hash key memory 15748
      represented.hash index operand fits)
  simpa only [PMF.map_comp, Function.comp_def] using law

end Kriterion.ArgoMAC.ArithmeticSimulator
