import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock
import Proof.Privacy.Simulator.Arithmetic.QueryInputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The source consumes one fixed index and prepares its Even-Mansour operand. -/
noncomputable def encLinkPrepared (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) : Memory :=
  executeLinear encLinkPrepare (decodedInput memory 14 (encLinkIndexValue index) rest)

/-- The checked reader and preparation block use exactly 121 instructions. -/
theorem encLinkBlock_read [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = encLinkIndexBits index ++ rest) :
    runPrefix host 121 ⟨labels 7208, memory⟩ =
      PMF.pure (some (false, ⟨labels 7239, encLinkPrepared memory index rest⟩, 121)) := by
  have read := decodedInputHost_prefix host 14 (encLinkIndexValue index) (labels ∘ encLinkReaderLabels)
    (encLinkBlock_reader host attempts labels present) memory rest wire (by decide)
  change runPrefix host 104 ⟨labels 7208, memory⟩ = _ at read
  have block := encLinkBlock_linear host attempts labels present encLinkPrepare encLinkPrepareLabels
    (encLink_prepare attempts) (by
      intro position valid
      have bound : position < 17 := valid
      simp [encLinkPrepareLabels, encLinkLabels, bound]
      omega)
  have prepared := linear_prefix host encLinkPrepare (labels ∘ encLinkPrepareLabels) block
    (decodedInput memory 14 (encLinkIndexValue index) rest)
  change runPrefix host 17 ⟨labels 7222, _⟩ = _ at prepared
  rw [show 121 = 104 + 17 from rfl, prefix_add, read, PMF.pure_bind]
  dsimp only
  change (runPrefix host 17 ⟨labels 7222, _⟩).map _ = _
  rw [prepared]
  simp [encLinkPrepared, PMF.pure_map, encLinkPrepareLabels, encLinkLabels,
    show encLinkPrepare.length = 17 from rfl]

/-- The prepared query uses the exact public index and one selected coordinate bit. -/
theorem encLinkPrepared_values (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) :
    let final := encLinkPrepared memory index rest
    final.registers 8 = (memory.ram 35 &&& 1#256) ^^^ memory.ram 39 ∧
    final.registers 9 = BitVec.ofNat 256 (encLinkIndexValue index) ∧ final.registers 10 = 2 ∧
    final.ram = Function.update (Function.update memory.ram 41 (memory.ram (memory.ram 32)))
      35 (memory.ram 35 >>> 1) ∧ final.bits 0 = rest := by
  have prepared := encLinkPrepare_state (decodedInput memory 14 (encLinkIndexValue index) rest)
  have indexValue := decodedInput_value memory 14 (encLinkIndexValue index) rest (encLinkIndexValue_bound index)
  have ram : (decodedInput memory 14 (encLinkIndexValue index) rest).ram = memory.ram := rfl
  dsimp only [encLinkPrepared]
  exact ⟨prepared.1, prepared.2.1.trans indexValue, prepared.2.2.1,
    prepared.2.2.2.1, (congrFun prepared.2.2.2.2 0).trans (decodedInput_values _ _ _ _).2⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
