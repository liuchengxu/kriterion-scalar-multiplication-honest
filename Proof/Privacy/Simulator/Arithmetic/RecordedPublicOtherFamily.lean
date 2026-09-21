import Proof.Privacy.Simulator.Arithmetic.RecordedPublicRecoverMemory
import Proof.Privacy.Simulator.Arithmetic.RecordedPublicNonfixed

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle

/-- The stored EncPRF forward branch preserves the exact recovered family. -/
theorem storedForwardSamples_otherFamily [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256)
    (supported : (final, cost) ∈ (storedForwardSamples attempts (state.permutations oracle).base.used memory).support) :
    let next := state.updatePermutation oracle (programmedForwardMemoryState (state.permutations oracle) input final)
    OracleFamilyMemory (recordedPublicForwardTail (state.permutations oracle).overlay.length final).1.ram next ∧
      OracleFamilyFits next := by
  dsimp only
  have stored := storedForwardSamples_family attempts memory final cost state oracle input represented capacity index operand room supported
  have kept := storedForwardSamples_private attempts _ memory final cost supported oracle.castSucc 49 (by decide) (by decide)
    index (represented.permutations oracle).base.count (by omega)
  have growth := programmedForwardMemoryState_growth (state.permutations oracle) input final
  rw [publicForwardTail_ram] at stored
  rw [recordedPublicForwardTail_nonfixedRam _ final (kept ▸ forward) (kept ▸ inverse)]
  exact ⟨stored, OracleFamilyFits.updateRead state oracle _ capacity growth.1 growth.2 (by omega)⟩

/-- The stored EncPRF inverse branch preserves the exact recovered family. -/
theorem storedInverseSamples_otherFamily [BN254.FieldCertificate]
    (attempts : Nat) (memory final : Memory) (cost : Nat) (state : SparseOracleFamily)
    (oracle : Fin 15748) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (index : memory.registers 9 = BitVec.ofNat 256 oracle.val)
    (operand : memory.registers 8 = BitVec.ofNat 256 input.val)
    (room : 2 * ((state.permutations oracle).base.used + 1) + 256 < 2 ^ 110)
    (forward : memory.ram 49#256 ≠ 0#256) (inverse : memory.ram 49#256 ≠ 1#256)
    (supported : (final, cost) ∈ (storedInverseSamples attempts (state.permutations oracle).base.used
      (publicInversePrepared (state.permutations oracle).overlay.length memory)).support) :
    let next := state.updatePermutation oracle (programmedInverseMemoryState (state.permutations oracle) input final)
    OracleFamilyMemory (recordedPublicInverseTail final).1.ram next ∧ OracleFamilyFits next := by
  dsimp only
  have stored := storedInverseSamples_family attempts memory final cost state oracle input represented capacity index operand room supported
  have preparedIndex := (publicInversePrepared_data (state.permutations oracle).overlay.length memory).2.trans index
  have preparedCounter := (publicInversePrepared_public (state.permutations oracle).overlay.length memory oracle.castSucc 0 0 (by decide)).trans
    (represented.permutations oracle).base.count
  have kept := storedInverseSamples_private attempts _ _ final cost supported oracle.castSucc 49 (by decide) (by decide)
    preparedIndex preparedCounter (by omega)
  have prepared : (publicInversePrepared (state.permutations oracle).overlay.length memory).ram 49#256 = memory.ram 49#256 := by
    rw [(publicInversePrepared_data _ memory).1]
    exact oracleLoadRam_private memory 49 (by decide) (by decide)
  have tag := kept.trans prepared
  have growth := programmedInverseMemoryState_growth (state.permutations oracle) input final
  rw [publicInverseTail_ram] at stored
  rw [recordedPublicInverseTail_nonfixedRam final (tag ▸ forward) (tag ▸ inverse)]
  exact ⟨stored, OracleFamilyFits.updateRead state oracle _ capacity growth.1 growth.2 (by omega)⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
