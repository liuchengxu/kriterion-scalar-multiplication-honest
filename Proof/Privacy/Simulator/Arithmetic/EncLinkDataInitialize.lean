import Proof.Privacy.Simulator.Arithmetic.EncLinkDataMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkInitializeMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The save block preserves every private data cell above its scratch area. -/
theorem encLinkSaved_private (memory : Memory) (cell : Nat)
    (lower : 256 ≤ cell) (upper : cell < 2 ^ 96) :
    (encLinkSaved memory).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
  have separate (scratch : Nat) (small : scratch < 256) :
      BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch :=
    encLinkOutput_separate cell scratch lower upper small
  simp [encLinkSaved, encLinkSave, executeLinear, LinearInstruction.execute,
    separate 32 (by decide), separate 33 (by decide), separate 34 (by decide),
    separate 35 (by decide), separate 36 (by decide), separate 38 (by decide)]

/-- Every initialized hash sample retains all original labels and both coordinate words. -/
theorem encLinkInitialize_data (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (inputBase : Nat) (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount)
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (hashRoom : 2 * (state.hash.length + 1) + 256 < 2 ^ 110)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = x.setWidth 256) (inputY : memory.registers 13 = y.setWidth 256)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0
      (List.ofFn fun index => (labels index).setWidth 256))
    (supported : (final, cost) ∈ (hashHandlerSamples state.hash.length (encLinkSaved memory)).support) :
    EncLinkDataMemory (encLinkScheduled final) 0 inputBase labels x y
      (Security.SimulatorMachine.hashFin.symm (final.registers 8).toFin).2 := by
  have saved := encLinkSave_state memory
  have family := encLinkSaved_family memory state represented capacity
  have index : (encLinkSaved memory).registers 9 = BitVec.ofNat 256 15748 := saved.2.1
  have counter : (encLinkSaved memory).ram (oracleAddress 15748 0 0) = BitVec.ofNat 256 state.hash.length := by
    simpa only [hashWordPairs, List.length_map] using family.hash.count
  have kept (cell : Nat) (lower : 16 ≤ cell) (upper : cell < 2 ^ 96) :
      final.ram (BitVec.ofNat 256 cell) = (encLinkSaved memory).ram (BitVec.ofNat 256 cell) :=
    hashHandlerSamples_private state.hash.length (encLinkSaved memory) final cost supported
      15748 index counter (by omega) cell lower upper
  have frame (cell : Nat) (lower : 256 ≤ cell) (upper : cell < 2 ^ 96) :
      (encLinkScheduled final).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
    have ne40 : BitVec.ofNat 256 cell ≠ (40 : Word) := encLinkOutput_separate cell 40 lower upper (by decide)
    have ne39 : BitVec.ofNat 256 cell ≠ (39 : Word) := encLinkOutput_separate cell 39 lower upper (by decide)
    rw [(encLinkScheduled_memory final).1,
      Function.update_of_ne ne40, Function.update_of_ne ne39,
      kept cell (by omega) upper, encLinkSaved_private memory cell lower upper]
  constructor
  · intro offset inside
    have bound : offset < 508 := by simpa only [List.length_ofFn] using inside
    have same := frame (inputBase + offset) (by omega) (by omega)
    rw [Nat.zero_add, ← BitVec.ofNat_add, same]
    simpa only [Nat.zero_add, ← BitVec.ofNat_add] using stored offset inside
  · rw [(encLinkScheduled_memory final).1]
    simp only [Function.update_of_ne (by decide : (32 : Word) ≠ 40),
      Function.update_of_ne (by decide : (32 : Word) ≠ 39), Nat.add_zero]
    exact (kept 32 (by decide) (by decide)).trans (saved.2.2.2.1.trans inputPointer)
  · rw [(encLinkScheduled_memory final).1]
    simp only [Function.update_of_ne (by decide : (35 : Word) ≠ 40),
      Function.update_of_ne (by decide : (35 : Word) ≠ 39)]
    have value := (kept 35 (by decide) (by decide)).trans (saved.2.2.2.2.2.2.1.trans inputX)
    simpa [encLinkCoordinateWord] using value
  · rw [(encLinkScheduled_memory final).1]
    simp only [Function.update_of_ne (by decide : (36 : Word) ≠ 40),
      Function.update_of_ne (by decide : (36 : Word) ≠ 39)]
    exact (kept 36 (by decide) (by decide)).trans (saved.2.2.2.2.2.2.2.1.trans inputY)
  · exact (encLinkScheduled_keys final).2

end Kriterion.ArgoMAC.ArithmeticSimulator
