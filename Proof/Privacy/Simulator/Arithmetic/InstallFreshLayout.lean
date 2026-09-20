import Proof.Privacy.Simulator.Arithmetic.DescendingPairsLayout

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Prepending a pair moves its base by exactly two cells. -/
theorem oracleAddress_prepend (oracle : Fin 15749) (table : Fin 4) (count : Nat)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    oracleAddress oracle table (2 ^ 110 - 2 * count) - 2#256 =
      oracleAddress oracle table (2 ^ 110 - 2 * (count + 1)) := by
  apply sub_eq_iff_eq_add.mpr
  change _ = oracleAddress oracle table (2 ^ 110 - 2 * (count + 1)) + BitVec.ofNat 256 2
  rw [oracleAddress_add]
  congr 1
  omega

/-- The fixed memory layout supplies every pair-insertion separation condition. -/
theorem installedFresh_layout (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (inputs outputs : List (Word × Word))
    (inputLength : inputs.length = count) (outputLength : outputs.length = count)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (inputStored : RepresentsPairs memory.ram (memory.registers 1) inputs)
    (outputStored : RepresentsPairs memory.ram (memory.registers 3) outputs)
    (fits : 2 * (count + 1) ≤ 2 ^ 110) :
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 1)
      ((memory.registers 0, memory.ram 6) :: inputs) ∧
    RepresentsPairs (installedFresh memory).ram ((installedFresh memory).registers 3)
      ((memory.registers 0, memory.ram 7) :: outputs) := by
  apply installedFresh_represents memory inputs outputs inputStored outputStored
  · rw [inputLength]
    have upper : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  · rw [outputLength]
    have upper : 2 ^ 110 < 2 ^ 256 := by decide
    omega
  · intro first firstFits second secondFits
    rw [inputBase, outputBase, oracleAddress_prepend oracle 0 count fits,
      oracleAddress_prepend oracle 1 count fits]
    exact descendingPairs_disjoint oracle 0 1 (by decide) (count + 1) (count + 1) fits fits
      first second (by simpa [inputLength] using firstFits) (by simpa [outputLength] using secondFits)

/-- Capacity leaves all descending pair cells above the public header. -/
theorem descendingPairs_header_disjoint (oracle : Fin 15749) (table : Fin 4) (count index : Nat)
    (fits : 2 * count + 256 < 2 ^ 110) (inside : index < 2 * count) :
    oracleAddress oracle table (2 ^ 110 - 2 * count) + BitVec.ofNat 256 index ≠
      oracleAddress oracle 0 0 := by
  rw [oracleAddress_add]
  intro equal
  have offsets := (oracleAddress_injective oracle oracle table 0 _ 0
    (by omega) (by decide) equal).2.2
  omega

/-- Fresh installation preserves the public count header until the explicit commit. -/
theorem installedFresh_header (memory : Memory) (oracle : Fin 15749) (count : Nat)
    (inputBase : memory.registers 1 = oracleAddress oracle 0 (2 ^ 110 - 2 * count))
    (outputBase : memory.registers 3 = oracleAddress oracle 1 (2 ^ 110 - 2 * count))
    (fits : 2 * (count + 1) + 256 < 2 ^ 110) :
    (installedFresh memory).ram (oracleAddress oracle 0 0) = memory.ram (oracleAddress oracle 0 0) := by
  have capacity : 2 * (count + 1) ≤ 2 ^ 110 := by omega
  have i0 := descendingPairs_header_disjoint oracle 0 (count + 1) 0 fits (by omega)
  have i1 := descendingPairs_header_disjoint oracle 0 (count + 1) 1 fits (by omega)
  have o0 := descendingPairs_header_disjoint oracle 1 (count + 1) 0 fits (by omega)
  have o1 := descendingPairs_header_disjoint oracle 1 (count + 1) 1 fits (by omega)
  apply installedFresh_other memory
  · rw [inputBase, oracleAddress_prepend oracle 0 count capacity]
    simpa using Ne.symm i0
  · rw [inputBase, oracleAddress_prepend oracle 0 count capacity]
    simpa using Ne.symm i1
  · rw [outputBase, oracleAddress_prepend oracle 1 count capacity]
    simpa using Ne.symm o0
  · rw [outputBase, oracleAddress_prepend oracle 1 count capacity]
    simpa using Ne.symm o1

end Kriterion.ArgoMAC.ArithmeticSimulator
