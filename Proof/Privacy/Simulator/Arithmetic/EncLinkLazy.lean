import Proof.Privacy.Simulator.Arithmetic.EncLinkMachine
import Construction.Simulator.Assembly
import Proof.Privacy.Simulator.Arithmetic.LinearProgram
import Proof.Privacy.Simulator.Arithmetic.EncLinkIndex
import Proof.Privacy.Simulator.Arithmetic.EncLinkRead
import Proof.Privacy.Simulator.Arithmetic.EncLinkControl
import Proof.Privacy.Simulator.Arithmetic.EncLinkSchedule
import Proof.Privacy.Simulator.Arithmetic.EncLinkState

set_option maxRecDepth 4096

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

attribute [local irreducible] encLinkIndices

set_option backward.isDefEq.respectTransparency false in
/-- One fixed oracle query costs one instruction and preserves private memory. -/
theorem simulator_query_continue [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator)
    (pc next : Fin (host.size + 1)) (kind : Fin 5) (index input first second : Register)
    (selected : host.code[pc.val] = .query kind index input first second next)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat)
    (query : PublicQuery FixedIndex EncIndex)
    (decoded : queryFromRegisters kind (memory.registers index) (memory.registers input) = some query) :
    host.run (fuel + 1) ⟨pc, memory⟩ oracle =
      (LazyOracle.query query oracle).bind fun answer =>
        (host.run fuel ⟨next, { memory with registers := (Function.update
          (Function.update memory.registers first (answerWords query answer.1).1)
            second (answerWords query answer.1).2) }⟩ answer.2).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 1)) := by
  rw [Simulator.run]
  simp only [Simulator.step, selected, decoded, PMF.bind_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The link packs the two hash blocks after one fixed oracle query. -/
theorem simulator_hash_link [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator)
    (labels : Nat → Fin (host.size + 1))
    (query : host.code[(labels 0).val] = .query 4 9 8 1 2 (labels 1))
    (pack : ∀ index (valid : index < 3),
      host.code[(labels (index + 1)).val] = .compute
        (([LinearInstruction.constant 3 128, .arithmetic .shiftLeft 8 1 3,
          .arithmetic .xor 8 8 2][index]).emit (labels (index + 2))))
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    host.run (4 + fuel) ⟨labels 0, memory⟩ oracle =
      (LazyOracle.query (.hash (memory.registers 8).toNat) oracle).bind fun answer =>
        (host.run fuel ⟨labels 4,
          executeLinear [.constant 3 128, .arithmetic .shiftLeft 8 1 3, .arithmetic .xor 8 8 2]
            {memory with registers := (Function.update (Function.update memory.registers 1
              (answerWords (.hash (memory.registers 8).toNat) answer.1).1) 2
                (answerWords (.hash (memory.registers 8).toNat) answer.1).2)}⟩ answer.2).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 4)) := by
  rw [show 4 + fuel = (3 + fuel) + 1 by omega,
    simulator_query_continue host (labels 0) (labels 1) 4 9 8 1 2 query memory oracle
      (3 + fuel) (.hash (memory.registers 8).toNat) (by simp [queryFromRegisters])]
  congr 1
  funext answer
  have packed := simulator_linear_continue host [.constant 3 128, .arithmetic .shiftLeft 8 1 3,
    .arithmetic .xor 8 8 2] (fun index => labels (index + 1))
      (by intro index valid; simpa only [Nat.add_assoc] using pack index valid)
      {memory with registers := (Function.update (Function.update memory.registers 1
        (answerWords (.hash (memory.registers 8).toNat) answer.1).1) 2
        (answerWords (.hash (memory.registers 8).toNat) answer.1).2)} answer.2 fuel
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd] at packed
  rw [packed]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The fixed public index excludes the simulator's former table offset. -/
theorem encLink_public_index (index : EncPRF.PermutationIndex) :
    BitVec.ofNat 256 (encLinkIndexValue index) - 15240 =
      BitVec.ofNat 256 (Fintype.equivFin EncPRF.PermutationIndex index).val := by
  unfold encLinkIndexValue
  rw [BitVec.ofNat_add]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The link removes the old memory offset and requests the selected encryption block. -/
theorem simulator_enc_link [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex] (host : Simulator)
    (labels : Nat → Fin (host.size + 1))
    (constant : host.code[(labels 0).val] = .compute (.constant 3 15240 (labels 1)))
    (subtract : host.code[(labels 1).val] = .compute (.arithmetic .sub 9 9 3 (labels 2)))
    (query : host.code[(labels 2).val] = .query 2 9 8 8 7 (labels 3))
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (fuel : Nat) (index : EncPRF.PermutationIndex)
    (selected : memory.registers 9 = BitVec.ofNat 256 (encLinkIndexValue index)) :
    host.run (3 + fuel) ⟨labels 0, memory⟩ oracle =
      let prepared := executeLinear [.constant 3 15240, .arithmetic .sub 9 9 3] memory
      (LazyOracle.query (.encForward index (BitVec.ofNat 128 (memory.registers 8).toNat)) oracle).bind fun answer =>
        (host.run fuel ⟨labels 3, {prepared with registers := (Function.update
          (Function.update prepared.registers 8
            (answerWords (.encForward index (BitVec.ofNat 128 (memory.registers 8).toNat)) answer.1).1) 7
            (answerWords (.encForward index (BitVec.ofNat 128 (memory.registers 8).toNat)) answer.1).2)}⟩ answer.2).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 3)) := by
  have prelude := simulator_linear_continue host [.constant 3 15240, .arithmetic .sub 9 9 3] labels
    (by
      intro position valid
      change position < 2 at valid
      interval_cases position
      · exact constant
      · exact subtract) memory oracle (fuel + 1)
  change host.run (2 + (fuel + 1)) ⟨labels 0, memory⟩ oracle = _ at prelude
  rw [show 3 + fuel = 2 + (fuel + 1) by omega, prelude]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  have prepared : (executeLinear [.constant 3 15240, .arithmetic .sub 9 9 3] memory).registers 9 =
      BitVec.ofNat 256 (Fintype.equivFin EncPRF.PermutationIndex index).val := by
    simpa [executeLinear, LinearInstruction.execute, Arithmetic.eval, selected] using encLink_public_index index
  have input : (executeLinear [.constant 3 15240, .arithmetic .sub 9 9 3] memory).registers 8 =
      memory.registers 8 := by simp [executeLinear, LinearInstruction.execute]
  have small : (Fintype.equivFin EncPRF.PermutationIndex index).val < 2 ^ 256 :=
    lt_trans (Fintype.equivFin EncPRF.PermutationIndex index).isLt (by rw [encPermutationIndex_count]; decide)
  rw [simulator_query_continue host (labels 2) (labels 3) 2 9 8 8 7 query _ oracle fuel
    (.encForward index (BitVec.ofNat 128 (memory.registers 8).toNat)) (by
      rw [prepared, input]
      simp only [queryFromRegisters, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small]
      rw [dif_pos (Fintype.equivFin EncPRF.PermutationIndex index).isLt]
      change some (PublicQuery.encForward
        ((Fintype.equivFin EncPRF.PermutationIndex).symm (Fintype.equivFin EncPRF.PermutationIndex index))
        (BitVec.ofNat 128 (memory.registers 8).toNat)) = _
      rw [Equiv.symm_apply_apply])]
  simp [PMF.map_bind, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc]

/-- The private blocks exclude the two former oracle-table implementations. -/
def EncLinkPrivate (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 7468, (pc.val < 15 ∨ 88 ≤ pc.val ∧ pc.val < 7239 ∨ 7436 ≤ pc.val ∧ pc.val < 7466) →
    host.code[(labels pc).val] = relocate labels ((encLink attempts).code[pc.val])

/-- The host contains the link with fixed oracle query instructions. -/
def ContainsLazyEncLink (host : Simulator) (labels : Fin 7468 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 7468, pc.val < 7466 → host.code[(labels pc).val] =
    relocateSimulator labels (lazyEncLinkInstruction pc)

set_option backward.isDefEq.respectTransparency false in
theorem lazyEncLink_private (host : Simulator) (labels : Fin 7468 → Fin (host.size + 1))
    (present : ContainsLazyEncLink host labels) : EncLinkPrivate host.arithmetic 256 labels := by
  intro pc privateBlock
  have inside : pc.val < 7466 := by rcases privateBlock with first | middle | last <;> omega
  have unchanged : lazyEncLinkInstruction pc = .compute ((encLink 256).code[pc.val]) := by
    unfold lazyEncLinkInstruction
    split <;> try omega
    rfl
  simp only [Simulator.arithmetic, Vector.getElem_map, present pc inside, unchanged, relocateSimulator]

theorem encLinkPrivate_linear (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (program : List LinearInstruction) (block : Nat → Fin 7468)
    (contained : ContainsLinear (encLink attempts) program block)
    (inside : ∀ index, index < program.length →
      (block index).val < 15 ∨ 88 ≤ (block index).val ∧ (block index).val < 7239 ∨
        7436 ≤ (block index).val ∧ (block index).val < 7466) :
    ContainsLinear host program (labels ∘ block) := by
  intro index valid
  exact (present (block index) (inside index valid)).trans
    ((congrArg (relocate labels) (contained index valid)).trans
      (LinearInstruction.relocate_emit labels _ _))

theorem encLinkPrivate_reader (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels) :
    ContainsWordInput host 14 (labels ∘ encLinkReaderLabels) := by
  intro pc valid
  have inside : 88 ≤ (encLinkReaderLabels pc).val ∧ (encLinkReaderLabels pc).val < 7239 := by
    simp [encLinkReaderLabels, encLinkLabels, valid]
    omega
  exact (present (encLinkReaderLabels pc) (Or.inr (Or.inl inside))).trans
    ((congrArg (relocate labels) (encLink_reader attempts pc valid)).trans
      (relocate_comp encLinkReaderLabels labels _))

theorem encLinkPrivate_read [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (memory : Memory) (index : EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = encLinkIndexBits index ++ rest) :
    runPrefix host 121 ⟨labels 7208, memory⟩ =
      PMF.pure (some (false, ⟨labels 7239, encLinkPrepared memory index rest⟩, 121)) := by
  have read := decodedInputHost_prefix host 14 (encLinkIndexValue index) (labels ∘ encLinkReaderLabels)
    (encLinkPrivate_reader host attempts labels present) memory rest wire (by decide)
  change runPrefix host 104 ⟨labels 7208, memory⟩ = _ at read
  have block := encLinkPrivate_linear host attempts labels present encLinkPrepare encLinkPrepareLabels
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

/-- The final count test restores the output pointer before the host return. -/
theorem encLinkPrivate_done [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (memory : Memory) (done : memory.registers 2 = 0#256) :
    runPrefix host 3 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false, ⟨labels 7466, executeLinear encLinkReturn memory⟩, 3)) := by
  have gate : host.code[(labels 7456).val] = .branch 2 (labels 7464) (labels 7457) := by
    exact (present 7456 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).1)
  have block := encLinkPrivate_linear host attempts labels present encLinkReturn encLinkReturnLabels
    (encLink_result attempts) (by
      intro index valid
      have bound : index < 2 := valid
      simp [encLinkReturnLabels, encLinkLabels, bound]
      omega)
  have returned := linear_prefix host encLinkReturn (labels ∘ encLinkReturnLabels) block memory
  change runPrefix host 2 ⟨labels 7464, memory⟩ = _ at returned
  rw [show 3 = 2 + 1 from rfl, runPrefix]
  simp only [step, gate, show (0 : Word) = 0#256 from rfl, done, ↓reduceIte, PMF.pure_bind]
  rw [returned]
  simp [PMF.pure_map, encLinkReturnLabels, encLinkLabels, show encLinkReturn.length = 2 from rfl]

/-- The nonfinal controller consumes four instructions before its next block. -/
theorem encLinkPrivate_compare [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (memory : Memory) (more : memory.registers 2 ≠ 0#256) :
    runPrefix host 4 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false,
        ⟨if memory.registers 2 = 254#256 then labels 7460 else labels 7208,
          encLinkCompared memory⟩, 4)) := by
  have gate : host.code[(labels 7456).val] = .branch 2 (labels 7464) (labels 7457) := by
    exact (present 7456 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).1)
  have constant : host.code[(labels 7457).val] = .constant 3 254 (labels 7458) := by
    exact (present 7457 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.1)
  have compare : host.code[(labels 7458).val] = .arithmetic .xor 3 2 3 (labels 7459) := by
    exact (present 7458 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.2.1)
  have select : host.code[(labels 7459).val] = .branch 3 (labels 7460) (labels 7208) := by
    exact (present 7459 (by decide)).trans (congrArg (relocate labels) (encLink_controlCode attempts).2.2.2)
  simp [runPrefix, step, gate, constant, compare, select, more, encLinkCompared,
    Arithmetic.eval, PMF.pure_map, BitVec.xor_eq_zero_iff, show (0 : Word) = 0#256 from rfl]

/-- The controller returns the exact next state and instruction charge. -/
theorem encLinkPrivate_control [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (memory : Memory) :
    runPrefix host (encLinkControlState memory).2.1 ⟨labels 7456, memory⟩ =
      PMF.pure (some (false,
        ⟨labels (encLinkControlState memory).2.2, (encLinkControlState memory).1⟩,
          (encLinkControlState memory).2.1)) := by
  by_cases done : memory.registers 2 = 0#256
  · simpa [encLinkControlState, done] using encLinkPrivate_done host attempts labels present memory done
  · have compared := encLinkPrivate_compare host attempts labels present memory done
    by_cases boundary : memory.registers 2 = 254#256
    · simp only [if_pos boundary] at compared
      have block := encLinkPrivate_linear host attempts labels present encLinkSwitch encLinkSwitchLabels
        (encLink_switch attempts) (by
          intro index valid
          have bound : index < 4 := valid
          simp [encLinkSwitchLabels, encLinkLabels, bound]
          omega)
      have switched := linear_prefix host encLinkSwitch (labels ∘ encLinkSwitchLabels) block
        (encLinkCompared memory)
      change runPrefix host 4 ⟨labels 7460, encLinkCompared memory⟩ = _ at switched
      simp only [encLinkControlState, if_neg done, if_pos boundary]
      rw [show 8 = 4 + 4 from rfl, prefix_add, compared, PMF.pure_bind]
      dsimp only
      rw [switched]
      simp [PMF.pure_map, encLinkSwitchLabels, encLinkLabels,
        show encLinkSwitch.length = 4 from rfl]
    · simpa [encLinkControlState, done, boundary] using compared

/-- The simulator reads one index and prepares its input in 121 private steps. -/
theorem simulator_encLink_read [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (index : EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = encLinkIndexBits index ++ rest) (fuel : Nat) :
    host.run (121 + fuel) ⟨labels 7208, memory⟩ oracle =
      (host.run fuel ⟨labels 7239, encLinkPrepared memory index rest⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 121)) := by
  apply host.run_prefix
  rw [run_after_prefix, encLinkPrivate_read host.arithmetic attempts labels present memory index rest wire,
    PMF.pure_bind]

/-- The simulator writes the answer and executes the private loop controller. -/
theorem simulator_encLink_tail [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    let result := encLinkControlState (executeLinear encLinkFinish memory)
    host.run (20 + result.2.1 + fuel) ⟨labels 7436, memory⟩ oracle =
      (host.run fuel ⟨labels result.2.2, result.1⟩ oracle).map
        (Option.map fun final => (final.1, final.2.1, final.2.2 + (20 + result.2.1))) := by
  dsimp only
  apply host.run_prefix
  have finish := encLinkPrivate_linear host.arithmetic attempts labels present encLinkFinish encLinkFinishLabels
    (encLink_finish attempts) (by
      intro index valid
      have bound : index < 20 := valid
      simp [encLinkFinishLabels, encLinkLabels, bound]
      omega)
  have privateRun := linear_prefix host.arithmetic encLinkFinish (labels ∘ encLinkFinishLabels) finish memory
  change runPrefix host.arithmetic 20 ⟨labels 7436, memory⟩ = _ at privateRun
  rw [run_after_prefix, prefix_add, privateRun, PMF.pure_bind]
  dsimp only
  change ((runPrefix host.arithmetic (encLinkControlState (executeLinear encLinkFinish memory)).2.1
    ⟨labels 7456, executeLinear encLinkFinish memory⟩).map _).bind _ = _
  rw [encLinkPrivate_control host.arithmetic attempts labels present, PMF.pure_map, PMF.pure_bind]
  simp [encLinkFinishLabels, encLinkLabels, show encLinkFinish.length = 20 from rfl, Nat.add_comm]

/-- Every complete loop row costs at most 152 steps. -/
theorem lazyEncLink_row_cost (memory : Memory) :
    121 + 3 + 20 + (encLinkControlState (executeLinear encLinkFinish memory)).2.1 ≤ 152 := by
  unfold encLinkControlState
  split
  · norm_num
  · split <;> norm_num

theorem encLinkPrivate_schedule [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : EncLinkPrivate host attempts labels)
    (memory : Memory) :
    runPrefix host 7120 ⟨labels 88, memory⟩ =
      PMF.pure (some (false, ⟨labels 7208, encLinkScheduled memory⟩, 7120)) := by
  have whitening := encLinkPrivate_linear host attempts labels present encLinkWhitening encLinkWhiteningLabels
    (encLink_whitening attempts) (by
      intro index valid
      have bound : index < 8 := valid
      simp [encLinkWhiteningLabels, encLinkLabels, bound]
      omega)
  have indices := encLinkPrivate_linear host attempts labels present encLinkIndexPrelude encLinkIndexLabels
    (encLink_indices attempts) (by
      intro index valid
      have bound : index < 7112 := by simpa only [encLinkIndexPrelude_length] using valid
      simp [encLinkIndexLabels, encLinkLabels, bound]
      omega)
  have first := linear_prefix host encLinkWhitening (labels ∘ encLinkWhiteningLabels) whitening memory
  change runPrefix host 8 ⟨labels 88, memory⟩ = _ at first
  have second := linear_prefix host encLinkIndexPrelude (labels ∘ encLinkIndexLabels) indices
    (executeLinear encLinkWhitening memory)
  rw [encLinkIndexPrelude_length] at second
  change runPrefix host 7112 ⟨labels 96, _⟩ = _ at second
  rw [show 7120 = 8 + 7112 from rfl, prefix_add, first, PMF.pure_bind]
  dsimp only
  change (runPrefix host 7112 ⟨labels 96, _⟩).map _ = _
  rw [second]
  simp [encLinkScheduled, PMF.pure_map, encLinkIndexLabels, encLinkLabels,
    show encLinkWhitening.length = 8 from rfl]

/-- The row source contains one public query and the exact private continuation. -/
def lazyEncLinkReply (memory : Memory) (answer : Word × Word) : Memory :=
  let prepared := executeLinear [.constant 3 15240, .arithmetic .sub 9 9 3] memory
  {prepared with registers := (Function.update (Function.update prepared.registers 8
    answer.1) 7 answer.2)}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- One complete row uses a fixed reserve for every oracle history. -/
theorem simulator_encLink_row [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (constant : host.code[(labels 7239).val] = .compute (.constant 3 15240 (labels 7240)))
    (subtract : host.code[(labels 7240).val] = .compute (.arithmetic .sub 9 9 3 (labels 7241)))
    (query : host.code[(labels 7241).val] = .query 2 9 8 8 7 (labels 7436))
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (index : EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = encLinkIndexBits index ++ rest) (fuel : Nat) :
    let prepared := encLinkPrepared memory index rest
    host.run (152 + fuel) ⟨labels 7208, memory⟩ oracle =
      (LazyOracle.query (.encForward index (BitVec.ofNat 128 (prepared.registers 8).toNat)) oracle).bind fun answer =>
        let result := encLinkControlState (executeLinear encLinkFinish (lazyEncLinkReply prepared (answerWords (.encForward index (BitVec.ofNat 128 (prepared.registers 8).toNat)) answer.1)))
        (host.run (152 + fuel - (144 + result.2.1)) ⟨labels result.2.2, result.1⟩ answer.2).map
          (Option.map fun final => (final.1, final.2.1, final.2.2 + (144 + result.2.1))) := by
  dsimp only
  rw [show 152 + fuel = 121 + (3 + (28 + fuel)) by omega,
    simulator_encLink_read host attempts labels present memory oracle index rest wire]
  have link := simulator_enc_link host
    (fun n => match n with | 0 => labels 7239 | 1 => labels 7240 | 2 => labels 7241 | _ => labels 7436)
    constant subtract query (encLinkPrepared memory index rest) oracle (28 + fuel) index
    (encLinkPrepared_values memory index rest).2.1
  change host.run (3 + (28 + fuel)) ⟨labels 7239, encLinkPrepared memory index rest⟩ oracle = _ at link
  rw [link, PMF.map_bind]
  apply PMF.bind_congr
  intro answer _
  rcases answer with ⟨answer, updated⟩
  change PMF.map _ (PMF.map _ (host.run (28 + fuel)
    ⟨labels 7436, lazyEncLinkReply (encLinkPrepared memory index rest)
      (answerWords (.encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index rest).registers 8).toNat)) answer)⟩ updated)) = _
  let result := encLinkControlState
    (executeLinear encLinkFinish (lazyEncLinkReply (encLinkPrepared memory index rest)
      (answerWords (.encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index rest).registers 8).toNat)) answer)))
  have bound : 20 + result.2.1 ≤ 28 := by
    have all := lazyEncLink_row_cost (lazyEncLinkReply (encLinkPrepared memory index rest)
      (answerWords (.encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index rest).registers 8).toNat)) answer))
    dsimp only [result]
    omega
  have tail := simulator_encLink_tail host attempts labels present
    (lazyEncLinkReply (encLinkPrepared memory index rest)
      (answerWords (.encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index rest).registers 8).toNat)) answer)) updated
    (28 + fuel - (20 + result.2.1))
  change host.run (20 + result.2.1 + (28 + fuel - (20 + result.2.1))) _ updated = _ at tail
  rw [show 20 + result.2.1 + (28 + fuel - (20 + result.2.1)) = 28 + fuel by omega] at tail
  rw [tail]
  have remaining : 28 + fuel - (20 + result.2.1) =
      152 + fuel - (144 + result.2.1) := by omega
  rw [show 121 + (3 + (28 + fuel)) = 152 + fuel by omega]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def, remaining]
  congr 1
  · funext final
    cases final <;> simp only [Option.map_none, Option.map_some]
    congr 3
    omega

/-- The schedule executes 7120 private instructions after the hash reply. -/
theorem simulator_encLink_schedule [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    host.run (7120 + fuel) ⟨labels 88, memory⟩ oracle =
      (host.run fuel ⟨labels 7208, encLinkScheduled memory⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 7120)) := by
  apply host.run_prefix
  rw [run_after_prefix, encLinkPrivate_schedule host.arithmetic attempts labels present memory,
    PMF.pure_bind]

/-- The save block retains caller data before the public hash request. -/
theorem simulator_encLink_save [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    host.run (15 + fuel) ⟨labels 0, memory⟩ oracle =
      (host.run fuel ⟨labels 15, executeLinear encLinkSave memory⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 15)) := by
  apply host.run_prefix
  have block := encLinkPrivate_linear host.arithmetic attempts labels present encLinkSave encLinkSaveLabels
    (encLink_save attempts) (by
      intro index valid
      have bound : index < 15 := valid
      simp [encLinkSaveLabels, encLinkLabels, bound])
  have saved := linear_prefix host.arithmetic encLinkSave (labels ∘ encLinkSaveLabels) block memory
  change runPrefix host.arithmetic 15 ⟨labels 0, memory⟩ = _ at saved
  rw [run_after_prefix, saved, PMF.pure_bind]
  rfl

def lazyEncLinkHashReply (memory : Memory) (words : Word × Word) : Memory :=
  executeLinear [.constant 3 128, .arithmetic .shiftLeft 8 1 3, .arithmetic .xor 8 8 2]
    {memory with registers := Function.update (Function.update memory.registers 1 words.1) 2 words.2}

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The complete start costs 7139 steps for every public oracle history. -/
theorem simulator_encLink_start [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (query : host.code[(labels 15).val] = .query 4 9 8 1 2 (labels 16))
    (constant : host.code[(labels 16).val] = .compute (.constant 3 128 (labels 17)))
    (shift : host.code[(labels 17).val] = .compute (.arithmetic .shiftLeft 8 1 3 (labels 18)))
    (combine : host.code[(labels 18).val] = .compute (.arithmetic .xor 8 8 2 (labels 88)))
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    let saved := executeLinear encLinkSave memory
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
    host.run (7139 + fuel) ⟨labels 0, memory⟩ oracle =
      (LazyOracle.query request oracle).bind fun answer =>
        (host.run fuel ⟨labels 7208,
          encLinkScheduled (lazyEncLinkHashReply saved (answerWords request answer.1))⟩ answer.2).map
            (Option.map fun final => (final.1, final.2.1, final.2.2 + 7139)) := by
  dsimp only
  rw [show 7139 + fuel = 15 + (4 + (7120 + fuel)) by omega,
    simulator_encLink_save host attempts labels present memory oracle]
  have hashed := simulator_hash_link host
    (fun n => match n with | 0 => labels 15 | 1 => labels 16 | 2 => labels 17 | 3 => labels 18 | _ => labels 88)
    query (by
      intro index valid
      interval_cases index
      · exact constant
      · exact shift
      · exact combine) (executeLinear encLinkSave memory) oracle (7120 + fuel)
  change host.run (4 + (7120 + fuel)) ⟨labels 15, executeLinear encLinkSave memory⟩ oracle = _ at hashed
  rw [hashed, PMF.map_bind]
  apply PMF.bind_congr
  intro answer _
  change PMF.map _ (PMF.map _ (host.run (7120 + fuel)
    ⟨labels 88, lazyEncLinkHashReply (executeLinear encLinkSave memory)
      (answerWords (.hash ((executeLinear encLinkSave memory).registers 8).toNat) answer.1)⟩ answer.2)) = _
  rw [simulator_encLink_schedule host attempts labels present]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]

noncomputable def lazyEncLinkResult (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) : Memory × Nat × Fin 7468 :=
  let result := encLinkControlState (executeLinear encLinkFinish
    (lazyEncLinkReply (encLinkPrepared memory index rest) answer))
  (result.1, 144 + result.2.1, result.2.2)

theorem lazyEncLinkResult_cost (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) :
    (lazyEncLinkResult memory index rest answer).2.1 ≤ 152 :=
  lazyEncLink_row_cost _

theorem lazyEncLinkResult_bits (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) :
    (lazyEncLinkResult memory index rest answer).1.bits 0 = rest := by
  dsimp only [lazyEncLinkResult]
  rw [encLinkControlState_bits, encLinkFinish_bits]
  simpa only [lazyEncLinkReply, executeLinear, List.foldl_cons, List.foldl_nil, LinearInstruction.execute] using
    (encLinkPrepared_values memory index rest).2.2.2.2

/-- The source executes one fixed public query for each remaining row. -/
noncomputable def lazyEncLinkRows
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF ((Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  match indices with
  | [] => PMF.pure ((memory, 0, 7208), oracle)
  | index :: rest =>
    let wire := rest.flatMap encLinkIndexBits ++ suffix
    let prepared := encLinkPrepared memory index wire
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128 (prepared.registers 8).toNat)
    (LazyOracle.query request oracle).bind fun answer =>
      let result := lazyEncLinkResult memory index wire (answerWords request answer.1)
      if result.2.2 = 7208 then
        (lazyEncLinkRows rest suffix result.1 answer.2).map fun final =>
          ((final.1.1, result.2.1 + final.1.2.1, final.1.2.2), final.2)
      else PMF.pure (result, answer.2)

/-- The source uses at most 152 private and public steps for each row. -/
theorem lazyEncLinkRows_cost
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (final) (supported : final ∈ (lazyEncLinkRows indices suffix memory oracle).support) :
    final.1.2.1 ≤ 152 * indices.length := by
  induction indices generalizing memory oracle final with
  | nil =>
    have equal : final = ((memory, 0, 7208), oracle) := by
      simpa only [lazyEncLinkRows, PMF.support_pure, Set.mem_singleton_iff] using supported
    subst final
    exact Nat.le_refl 0
  | cons index indices ih =>
    simp only [lazyEncLinkRows, PMF.mem_support_bind_iff] at supported
    obtain ⟨answer, _, supported⟩ := supported
    split at supported
    · simp only [PMF.mem_support_map_iff] at supported
      obtain ⟨tail, inside, rfl⟩ := supported
      have tailBound := ih _ _ tail inside
      have rowBound := lazyEncLinkResult_cost memory index
        (indices.flatMap encLinkIndexBits ++ suffix)
        (answerWords (.encForward index (BitVec.ofNat 128
          ((encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8).toNat)) answer.1)
      simp only [List.length_cons]
      omega
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at supported
      subst final
      have rowBound := lazyEncLinkResult_cost memory index
        (indices.flatMap encLinkIndexBits ++ suffix)
        (answerWords (.encForward index (BitVec.ofNat 128
          ((encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8).toNat)) answer.1)
      simp only [List.length_cons]
      omega

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The machine executes the row source with its exact cost and oracle state. -/
theorem simulator_encLink_rows [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (attempts : Nat) (labels : Fin 7468 → Fin (host.size + 1))
    (present : EncLinkPrivate host.arithmetic attempts labels)
    (constant : host.code[(labels 7239).val] = .compute (.constant 3 15240 (labels 7240)))
    (subtract : host.code[(labels 7240).val] = .compute (.arithmetic .sub 9 9 3 (labels 7241)))
    (query : host.code[(labels 7241).val] = .query 2 9 8 8 7 (labels 7436))
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (wire : memory.bits 0 = indices.flatMap encLinkIndexBits ++ suffix) (fuel : Nat) :
    host.run (152 * indices.length + fuel) ⟨labels 7208, memory⟩ oracle =
      (lazyEncLinkRows indices suffix memory oracle).bind fun result =>
        (host.run (152 * indices.length + fuel - result.1.2.1)
          ⟨labels result.1.2.2, result.1.1⟩ result.2).map
            (Option.map fun final => (final.1, final.2.1, final.2.2 + result.1.2.1)) := by
  induction indices generalizing memory oracle fuel with
  | nil => simp [lazyEncLinkRows, PMF.map_id]
  | cons index indices ih =>
    rw [List.length_cons, show 152 * (indices.length + 1) + fuel =
      152 + (152 * indices.length + fuel) by omega]
    have row := simulator_encLink_row host attempts labels present constant subtract query
      memory oracle index (indices.flatMap encLinkIndexBits ++ suffix)
      (by simpa only [List.flatMap_cons, List.append_assoc] using wire)
      (152 * indices.length + fuel)
    change host.run (152 + (152 * indices.length + fuel)) _ oracle =
      (LazyOracle.query _ oracle).bind (fun answer =>
        (host.run (152 + (152 * indices.length + fuel) -
          (lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix)
            (answerWords _ answer.1)).2.1)
          ⟨labels (lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix)
            (answerWords _ answer.1)).2.2,
            (lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix)
              (answerWords _ answer.1)).1⟩ answer.2).map
          (Option.map fun final => (final.1, final.2.1, final.2.2 +
            (lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix)
              (answerWords _ answer.1)).2.1))) at row
    rw [row, lazyEncLinkRows, PMF.bind_bind]
    apply PMF.bind_congr
    intro answer _
    let result := lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix)
      (answerWords (.encForward index (BitVec.ofNat 128
        ((encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8).toNat)) answer.1)
    have rowBound : result.2.1 ≤ 152 := lazyEncLinkResult_cost _ _ _ _
    change (host.run (152 + (152 * indices.length + fuel) - result.2.1)
      ⟨labels result.2.2, result.1⟩ answer.2).map _ =
      (if result.2.2 = 7208 then
        (lazyEncLinkRows indices suffix result.1 answer.2).map
          (fun final => ((final.1.1, result.2.1 + final.1.2.1, final.1.2.2), final.2))
      else PMF.pure (result, answer.2)).bind _
    by_cases more : result.2.2 = 7208
    · rw [if_pos more, PMF.bind_map]
      have next := ih result.1 answer.2 (lazyEncLinkResult_bits _ _ _ _) (152 - result.2.1 + fuel)
      have remain : 152 * indices.length + (152 - result.2.1 + fuel) =
          152 + (152 * indices.length + fuel) - result.2.1 := by omega
      rw [remain] at next
      rw [more, next, PMF.map_bind]
      apply PMF.bind_congr
      intro tail supported
      have tailBound := lazyEncLinkRows_cost indices suffix result.1 answer.2 tail supported
      have left : 152 + (152 * indices.length + fuel) - result.2.1 - tail.1.2.1 =
          152 + (152 * indices.length + fuel) - (result.2.1 + tail.1.2.1) := by omega
      simp only [PMF.map_comp, Option.map_map, Function.comp_def, left]
      congr 1
      funext final
      cases final <;> simp only [Option.map_none, Option.map_some]
      change some (_, _, _ + tail.1.2.1 + result.2.1) = _
      congr 3
      omega
    · rw [if_neg more, PMF.pure_bind]

/-- The complete source has one hash request and at most 508 encipher requests. -/
noncomputable def lazyEncLinkSamples
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    PMF ((Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  let saved := executeLinear encLinkSave memory
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
  (LazyOracle.query request oracle).bind fun answer =>
    (lazyEncLinkRows encLinkIndices (memory.bits 0)
      (encLinkScheduled (lazyEncLinkHashReply saved (answerWords request answer.1))) answer.2).map
      fun result => ((result.1.1, 7139 + result.1.2.1, result.1.2.2), result.2)

theorem lazyEncLinkSamples_cost
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (result) (supported : result ∈ (lazyEncLinkSamples memory oracle).support) :
    result.1.2.1 ≤ 84355 := by
  simp only [lazyEncLinkSamples, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, _, supported⟩ := supported
  simp only [PMF.mem_support_map_iff] at supported
  obtain ⟨tail, inside, rfl⟩ := supported
  have bound := lazyEncLinkRows_cost encLinkIndices _ _ _ tail inside
  rw [encLinkIndices_length] at bound
  change 7139 + tail.1.2.1 ≤ 84355
  omega

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The full link source has a fixed reserve for every public oracle history. -/
theorem simulator_encLink_samples [BN254.FieldCertificate]
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (host : Simulator) (labels : Fin 7468 → Fin (host.size + 1))
    (present : ContainsLazyEncLink host labels)
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (fuel : Nat) :
    host.run (84355 + fuel) ⟨labels 0, memory⟩ oracle =
      (lazyEncLinkSamples memory oracle).bind fun result =>
        (host.run (84355 + fuel - result.1.2.1)
          ⟨labels result.1.2.2, result.1.1⟩ result.2).map
            (Option.map fun final => (final.1, final.2.1, final.2.2 + result.1.2.1)) := by
  have privateCode := lazyEncLink_private host labels present
  have start := simulator_encLink_start host 256 labels privateCode
    (present 15 (by decide)) (present 16 (by decide))
    (present 17 (by decide)) (present 18 (by decide)) memory oracle (77216 + fuel)
  change host.run (7139 + (77216 + fuel)) _ oracle = _ at start
  rw [show 84355 + fuel = 7139 + (77216 + fuel) by omega, start,
    lazyEncLinkSamples, PMF.bind_bind]
  apply PMF.bind_congr
  intro answer _
  let ready := encLinkScheduled (lazyEncLinkHashReply (executeLinear encLinkSave memory)
    (answerWords (.hash ((executeLinear encLinkSave memory).registers 8).toNat) answer.1))
  have wire : ready.bits 0 = encLinkIndices.flatMap encLinkIndexBits ++ memory.bits 0 := by
    dsimp only [ready]
    rw [(encLinkScheduled_memory _).2]
    simp only [Function.update_self, lazyEncLinkHashReply, executeLinear, List.foldl_cons,
      List.foldl_nil, LinearInstruction.execute]
    change encLinkIndexWire ++ (executeLinear encLinkSave memory).bits 0 = _
    rw [(encLinkSave_state memory).2.2.2.2.2.2.2.2.2]
    rfl
  have rows := simulator_encLink_rows host 256 labels privateCode
    (present 7239 (by decide)) (present 7240 (by decide)) (present 7241 (by decide))
    encLinkIndices (memory.bits 0) ready answer.2 wire fuel
  rw [encLinkIndices_length] at rows
  change host.run (77216 + fuel) _ answer.2 = _ at rows
  change (host.run (77216 + fuel) ⟨labels 7208, ready⟩ answer.2).map _ = _
  rw [rows, PMF.map_bind, PMF.bind_map]
  apply PMF.bind_congr
  intro tail supported
  have bound := lazyEncLinkRows_cost encLinkIndices (memory.bits 0) ready answer.2 tail supported
  rw [encLinkIndices_length] at bound
  have remaining : 77216 + fuel - tail.1.2.1 =
      7139 + (77216 + fuel) - (7139 + tail.1.2.1) := by omega
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  change PMF.map _ (host.run (77216 + fuel - tail.1.2.1) _ tail.2) =
    PMF.map _ (host.run (7139 + (77216 + fuel) - (7139 + tail.1.2.1)) _ tail.2)
  rw [remaining]
  apply congrArg (fun fn => PMF.map fn (host.run (7139 + (77216 + fuel) - (7139 + tail.1.2.1))
    ⟨labels tail.1.2.2, tail.1.1⟩ tail.2))
  funext final
  cases final <;> simp only [Option.map_none, Option.map_some]
  rename_i final
  change some (final.1, final.2.1, final.2.2 + tail.1.2.1 + 7139) =
    some (final.1, final.2.1, final.2.2 + (7139 + tail.1.2.1))
  rw [Nat.add_assoc, Nat.add_comm tail.1.2.1 7139]

theorem lazyEncForward_fixed
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (index : EncPRF.PermutationIndex) (input : Block)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (answer) (supported : answer ∈ (LazyOracle.query (.encForward index input) oracle).support) :
    answer.2.fixed = oracle.fixed := by
  simp only [LazyOracle.query, PMF.mem_support_map_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

theorem lazyHash_fixed
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (input : Int) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (answer) (supported : answer ∈ (LazyOracle.query (.hash input) oracle).support) :
    answer.2.fixed = oracle.fixed := by
  simp only [LazyOracle.query, PMF.mem_support_map_iff] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Every link row preserves the fixed-key permutation tables. -/
theorem lazyEncLinkRows_fixed
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (final) (supported : final ∈ (lazyEncLinkRows indices suffix memory oracle).support) :
    final.2.fixed = oracle.fixed := by
  induction indices generalizing memory oracle final with
  | nil =>
    simp only [lazyEncLinkRows, PMF.support_pure, Set.mem_singleton_iff] at supported
    subst final
    rfl
  | cons index indices ih =>
    simp only [lazyEncLinkRows, PMF.mem_support_bind_iff] at supported
    obtain ⟨answer, queried, supported⟩ := supported
    have kept := lazyEncForward_fixed _ _ oracle answer queried
    split at supported
    · simp only [PMF.mem_support_map_iff] at supported
      obtain ⟨tail, inside, rfl⟩ := supported
      exact (ih _ _ tail inside).trans kept
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at supported
      subst final
      exact kept

attribute [local irreducible] lazyEncLinkRows

set_option maxHeartbeats 800000 in
/-- The full link preserves the fixed-key permutation tables. -/
theorem lazyEncLinkSamples_fixed
    [DecidableEq Shared.FixedKeyIndex] [DecidableEq EncPRF.PermutationIndex]
    (memory : Memory) (oracle : LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (result : (Memory × Nat × Fin 7468) × LazyOracle.State Shared.FixedKeyIndex EncPRF.PermutationIndex) (supported : result ∈ (lazyEncLinkSamples memory oracle).support) :
    result.2.fixed = oracle.fixed := by
  simp only [lazyEncLinkSamples, PMF.mem_support_bind_iff] at supported
  obtain ⟨answer, queried, supported⟩ := supported
  simp only [PMF.mem_support_map_iff] at supported
  obtain ⟨tail, inside, rfl⟩ := supported
  have rows : tail.2.fixed = answer.2.fixed :=
    lazyEncLinkRows_fixed encLinkIndices _ _ _ tail inside
  have hashed : answer.2.fixed = oracle.fixed :=
    lazyHash_fixed (((executeLinear encLinkSave memory).registers 8).toNat : Int) oracle answer queried
  exact rows.trans hashed

/-- The eager row source uses the same private arithmetic and complete public oracle. -/
noncomputable def eagerEncLinkRows
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory) :
    Memory × Nat × Fin 7468 :=
  match indices with
  | [] => (memory, 0, 7208)
  | index :: rest =>
    let wire := rest.flatMap encLinkIndexBits ++ suffix
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index wire).registers 8).toNat)
    let result := lazyEncLinkResult memory index wire (answerWords request (publicAnswer oracle request))
    if result.2.2 = 7208 then
      let final := eagerEncLinkRows oracle rest suffix result.1
      (final.1, result.2.1 + final.2.1, final.2.2)
    else result

noncomputable def eagerEncLinkSamples
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) (memory : Memory) :
    Memory × Nat × Fin 7468 :=
  let saved := executeLinear encLinkSave memory
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
  let result := eagerEncLinkRows oracle encLinkIndices (memory.bits 0)
    (encLinkScheduled (lazyEncLinkHashReply saved (answerWords request (publicAnswer oracle request))))
  (result.1, 7139 + result.2.1, result.2.2)

end Kriterion.ArgoMAC.ArithmeticSimulator
