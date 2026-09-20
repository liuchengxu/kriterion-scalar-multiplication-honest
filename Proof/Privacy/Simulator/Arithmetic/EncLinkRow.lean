import Proof.Privacy.Simulator.Arithmetic.EncLinkIteration
import Proof.Privacy.Simulator.Arithmetic.EncLinkPhysicalIndex
import Proof.Privacy.Simulator.Arithmetic.EncLinkState
import Proof.Privacy.Simulator.Arithmetic.InternalForwardGrowth
import Proof.Privacy.Simulator.Arithmetic.InternalForwardPrivate

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.OperationalOracle

/-- The row source retains the machine sample and the full finite oracle state. -/
noncomputable def encLinkRowSamples (attempts : Nat) (state : SparseOracleFamily)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) (input : Fin (2 ^ 128)) :
    PMF ((Memory × Nat × Fin 7468) × SparseOracleFamily) :=
  let oracle := encLinkPhysicalIndex index
  (internalForwardSamples attempts (state.permutations oracle).base.used
    (state.permutations oracle).overlay.length (encLinkPrepared memory index rest)).map fun result =>
      (chargedResult 121 (encLinkQueryPost result), state.updatePermutation oracle
        (internalForwardMemoryState (state.permutations oracle) input result.1))

/-- The retained source state does not change the machine sample distribution. -/
theorem encLinkRowSamples_machine (attempts : Nat) (state : SparseOracleFamily)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool) (input : Fin (2 ^ 128)) :
    (encLinkRowSamples attempts state memory index rest input).map Prod.fst =
      encLinkIterationSamples attempts (state.permutations (encLinkPhysicalIndex index)).base.used
        (state.permutations (encLinkPhysicalIndex index)).overlay.length memory index rest := by
  simp only [encLinkRowSamples, encLinkIterationSamples, encLinkQuerySamples,
    PMF.map_comp, Function.comp_def]

/-- Preparation preserves the private output cursor. -/
theorem encLinkPrepared_outputCursor (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) : (encLinkPrepared memory index rest).ram 33 = memory.ram 33 := by
  rw [(encLinkPrepared_values memory index rest).2.2.2.1]
  simp

/-- Every row sample retains the complete finite oracle RAM relation. -/
theorem encLinkRowSamples_family [BN254.FieldCertificate]
    (attempts : Nat) (state : SparseOracleFamily) (memory : Memory)
    (index : EncPRF.PermutationIndex) (rest : List Bool) (input : Fin (2 ^ 128))
    (represented : OracleFamilyMemory memory.ram state) (capacity : OracleFamilyFits state)
    (operand : (encLinkPrepared memory index rest).registers 8 = BitVec.ofNat 256 input.val)
    (fits : 2 * ((state.permutations (encLinkPhysicalIndex index)).base.used + 1) + 256 < 2 ^ 110)
    (privateOutput : (memory.ram 33).toNat < 2 ^ 96)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (result : (Memory × Nat × Fin 7468) × SparseOracleFamily)
    (supported : result ∈ (encLinkRowSamples attempts state memory index rest input).support) :
    OracleFamilyMemory result.1.1.ram result.2 ∧ OracleFamilyFits result.2 := by
  obtain ⟨⟨before, spent⟩, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  let oracle := encLinkPhysicalIndex index
  have prepared := encLinkPrepared_family memory index rest state represented capacity
  have physical : (encLinkPrepared memory index rest).registers 9 = BitVec.ofNat 256 oracle.val :=
    (encLinkPrepared_values memory index rest).2.1
  have room : 2 * ((state.permutations oracle).base.used + 1) ≤ 2 ^ 110 := by dsimp only [oracle]; omega
  have family := internalForwardSamples_family attempts (encLinkPrepared memory index rest)
    before spent state oracle input prepared capacity physical operand fits member
  have nextFits := internalForwardFamily_fits state oracle input before capacity room
  have cursor := internalForwardSamples_privateFrame attempts (state.permutations oracle).base.used
    (state.permutations oracle).overlay.length (encLinkPrepared memory index rest) before spent member
    oracle.castSucc physical (prepared.permutations oracle).base.count room 33 (by decide) (by decide)
  change before.ram 33 = (encLinkPrepared memory index rest).ram 33 at cursor
  rw [encLinkPrepared_outputCursor] at cursor
  change OracleFamilyMemory (encLinkAfterQuery before).1.ram _ ∧ _
  refine ⟨encLinkAfterQuery_family before _ family nextFits ?_ ?_ ?_, nextFits⟩
  · simpa only [cursor] using privateOutput
  · change before.ram 33 ≠ (32 : Word)
    rw [cursor]
    exact inputSafe
  · change before.ram 33 ≠ (38 : Word)
    rw [cursor]
    exact countSafe

end Kriterion.ArgoMAC.ArithmeticSimulator
