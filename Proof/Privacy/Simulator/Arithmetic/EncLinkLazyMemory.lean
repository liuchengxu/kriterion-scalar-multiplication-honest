import Proof.Privacy.Simulator.Arithmetic.EncLinkLazy
import Proof.Privacy.Simulator.Arithmetic.EncLinkTransform
import Proof.Privacy.Simulator.Arithmetic.EncLinkCoordinate
import Proof.Privacy.Simulator.Arithmetic.EncLinkDataMemory
import Proof.Privacy.Simulator.Arithmetic.EncLinkRowsProgram
import Proof.Privacy.Simulator.Arithmetic.EncLinkDataInitialize
import Proof.Privacy.Simulator.Arithmetic.EncLinkPositions
import Proof.Privacy.Simulator.Arithmetic.EncLinkTypedArray

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

attribute [local irreducible] encLinkIndices

/-- The query reply changes registers only. -/
theorem lazyEncLinkReply_state (memory : Memory) (answer : Word × Word) :
    (lazyEncLinkReply memory answer).registers 8 = answer.1 ∧
    (lazyEncLinkReply memory answer).ram = memory.ram ∧
    (lazyEncLinkReply memory answer).bits = memory.bits := by
  simp [lazyEncLinkReply, executeLinear, LinearInstruction.execute]

/-- Each complete row advances its cursor and decreases its count. -/
theorem lazyEncLinkResult_cursors (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (lazyEncLinkResult memory index rest answer).1.ram 32#256 = memory.ram 32#256 + 1 ∧
    (lazyEncLinkResult memory index rest answer).1.ram 33#256 = memory.ram 33#256 + 1 ∧
    (lazyEncLinkResult memory index rest answer).1.ram 38#256 = memory.ram 38#256 - 1 := by
  let before := lazyEncLinkReply (encLinkPrepared memory index rest) answer
  have ram : before.ram = Function.update (Function.update memory.ram 41#256 (memory.ram (memory.ram 32#256)))
      35#256 (memory.ram 35#256 >>> 1) :=
    (lazyEncLinkReply_state _ _).2.1.trans (encLinkPrepared_values memory index rest).2.2.2.1
  have cursor : before.ram 33#256 = memory.ram 33#256 := by rw [ram]; simp
  change (encLinkControlState (executeLinear encLinkFinish before)).1.ram 32#256 = _ ∧
    (encLinkControlState (executeLinear encLinkFinish before)).1.ram 33#256 = _ ∧
    (encLinkControlState (executeLinear encLinkFinish before)).1.ram 38#256 = _
  rw [encLinkControlState_ram, encLinkFinish_counter before (by rw [cursor]; exact countSafe),
    encLinkFinish_ram before (by rw [cursor]; exact inputSafe) (by rw [cursor]; exact countSafe)]
  split <;> simp [ram]

/-- The row returns when its count reaches zero. -/
theorem lazyEncLinkResult_target (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) (countSafe : memory.ram 33#256 ≠ 38#256) :
    (lazyEncLinkResult memory index rest answer).2.2 =
      if memory.ram 38#256 - 1 = 0#256 then 7466 else 7208 := by
  dsimp only [lazyEncLinkResult]
  rw [encLinkControlState_target]
  have ram := (lazyEncLinkReply_state (encLinkPrepared memory index rest) answer).2.1.trans
    (encLinkPrepared_values memory index rest).2.2.2.1
  rw [encLinkFinish_counter _ (by rw [ram]; simpa using countSafe), ram]
  simp

/-- A row preserves each RAM cell outside its label and scratch writes. -/
theorem lazyEncLinkResult_frame (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) (cell : Word)
    (inputSafe : memory.ram 33#256 ≠ 32#256) (countSafe : memory.ram 33#256 ≠ 38#256)
    (outputSeparate : cell ≠ memory.ram 33#256)
    (scratchSeparate : cell ≠ 32#256 ∧ cell ≠ 33#256 ∧ cell ≠ 35#256 ∧ cell ≠ 38#256 ∧ cell ≠ 41#256) :
    (lazyEncLinkResult memory index rest answer).1.ram cell = memory.ram cell := by
  let before := lazyEncLinkReply (encLinkPrepared memory index rest) answer
  have ram : before.ram = Function.update (Function.update memory.ram 41#256 (memory.ram (memory.ram 32#256)))
      35#256 (memory.ram 35#256 >>> 1) :=
    (lazyEncLinkReply_state _ _).2.1.trans (encLinkPrepared_values memory index rest).2.2.2.1
  have cursor : before.ram 33#256 = memory.ram 33#256 := by rw [ram]; simp
  change (encLinkControlState (executeLinear encLinkFinish before)).1.ram cell = _
  rw [encLinkControlState_ram, encLinkFinish_counter before (by rw [cursor]; exact countSafe),
    encLinkFinish_ram before (by rw [cursor]; exact inputSafe) (by rw [cursor]; exact countSafe)]
  split <;> simp [cursor, outputSeparate, scratchSeparate.1, scratchSeparate.2.1,
    scratchSeparate.2.2.1, scratchSeparate.2.2.2.1, scratchSeparate.2.2.2.2, ram]

/-- A row writes the selected label with the public permutation reply and second key. -/
theorem lazyEncLinkResult_output (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word)
    (safe : memory.ram 33#256 ≠ 32#256 ∧ memory.ram 33#256 ≠ 33#256 ∧
      memory.ram 33#256 ≠ 35#256 ∧ memory.ram 33#256 ≠ 38#256) :
    (lazyEncLinkResult memory index rest answer).1.ram (memory.ram 33#256) =
      (answer.1 ^^^ memory.ram 40#256) ^^^ memory.ram (memory.ram 32#256) := by
  let before := lazyEncLinkReply (encLinkPrepared memory index rest) answer
  have ram : before.ram = Function.update (Function.update memory.ram 41#256 (memory.ram (memory.ram 32#256)))
      35#256 (memory.ram 35#256 >>> 1) :=
    (lazyEncLinkReply_state _ _).2.1.trans (encLinkPrepared_values memory index rest).2.2.2.1
  have cursor : before.ram 33#256 = memory.ram 33#256 := by rw [ram]; simp
  have reply : before.registers 8 = answer.1 := (lazyEncLinkReply_state _ _).1
  change (encLinkControlState (executeLinear encLinkFinish before)).1.ram _ = _
  rw [encLinkControlState_ram, encLinkFinish_counter before (by rw [cursor]; exact safe.2.2.2),
    encLinkFinish_ram before (by rw [cursor]; exact safe.1) (by rw [cursor]; exact safe.2.2.2)]
  split <;> simp [ram, cursor, reply, safe.1, safe.2.1, safe.2.2.1, safe.2.2.2]

/-- A nonempty eager loop reaches the return after its exact row count. -/
theorem eagerEncLinkRows_terminal
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (output : Nat) (nonempty : indices ≠ [])
    (count : memory.ram 38#256 = BitVec.ofNat 256 indices.length)
    (cursor : memory.ram 33#256 = BitVec.ofNat 256 output)
    (lower : 256 ≤ output) (upper : output + indices.length < 2 ^ 256)
    (small : indices.length ≤ 508) :
    (eagerEncLinkRows oracle indices suffix memory).2.2 = 7466 := by
  induction indices generalizing memory output with
  | nil => exact False.elim (nonempty rfl)
  | cons index indices ih =>
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128
        ((encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8).toNat)
    let answer := answerWords request (publicAnswer oracle request)
    let result := lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix) answer
    have outputSmall : output < 2 ^ 256 := by omega
    have separate (cell : Nat) (tiny : cell < 256) : memory.ram 33#256 ≠ BitVec.ofNat 256 cell := by
      rw [cursor]
      intro equal
      have values := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt outputSmall,
        Nat.mod_eq_of_lt (show cell < 2 ^ 256 by omega)] at values
      omega
    have cursors := lazyEncLinkResult_cursors memory index (indices.flatMap encLinkIndexBits ++ suffix) answer
      (separate 32 (by decide)) (separate 38 (by decide))
    have nextCount : result.1.ram 38#256 = BitVec.ofNat 256 indices.length := by
      rw [cursors.2.2, count, List.length_cons, BitVec.ofNat_add]
      simp
    have nextCursor : result.1.ram 33#256 = BitVec.ofNat 256 (output + 1) := by
      rw [cursors.2.1, cursor, BitVec.ofNat_add]
      rfl
    have target := lazyEncLinkResult_target memory index (indices.flatMap encLinkIndexBits ++ suffix)
      answer (separate 38 (by decide))
    rw [count, List.length_cons, BitVec.ofNat_add] at target
    simp only [show (1 : Word) = 1#256 from rfl, add_sub_cancel_right] at target
    change result.2.2 = _ at target
    change (if result.2.2 = 7208 then
      let final := eagerEncLinkRows oracle indices suffix result.1
      (final.1, result.2.1 + final.2.1, final.2.2) else result).2.2 = 7466
    by_cases empty : indices = []
    · subst indices
      simp only [List.length_nil, show BitVec.ofNat 256 0 = 0#256 from rfl, if_true] at target
      rw [target, if_neg (by decide)]
      exact target
    · have positive : indices.length ≠ 0 := by
        intro zero
        exact empty (List.length_eq_zero_iff.mp zero)
      have nonzero : BitVec.ofNat 256 indices.length ≠ 0#256 := by
        intro equal
        have values := congrArg BitVec.toNat equal
        have fits : indices.length < 2 ^ 256 := by simp only [List.length_cons] at small; omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, BitVec.toNat_zero] at values
        exact positive values
      rw [if_neg nonzero] at target
      rw [target, if_pos rfl]
      exact ih result.1 (output + 1) empty nextCount nextCursor (by omega) (by
        simp only [List.length_cons] at upper
        omega) (by simp only [List.length_cons] at small; omega)

/-- The hash reply preserves every private RAM cell and bit stack. -/
theorem lazyEncLinkHashReply_memory (memory : Memory) (answer : Word × Word) :
    (lazyEncLinkHashReply memory answer).ram = memory.ram ∧
    (lazyEncLinkHashReply memory answer).bits = memory.bits := by
  simp [lazyEncLinkHashReply, executeLinear, LinearInstruction.execute]

/-- A valid caller reaches the link return within the fixed reserve. -/
theorem eagerEncLinkSamples_terminal
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (output : Nat)
    (cursor : memory.registers 14 = BitVec.ofNat 256 output)
    (lower : 256 ≤ output) (upper : output + 508 < 2 ^ 256) :
    (eagerEncLinkSamples oracle memory).2.2 = 7466 := by
  let saved := executeLinear encLinkSave memory
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
  let ready := encLinkScheduled (lazyEncLinkHashReply saved (answerWords request (publicAnswer oracle request)))
  have data := encLinkSave_state memory
  have ram := (encLinkScheduled_memory
    (lazyEncLinkHashReply saved (answerWords request (publicAnswer oracle request)))).1
  rw [(lazyEncLinkHashReply_memory _ _).1] at ram
  have count : ready.ram 38#256 = BitVec.ofNat 256 encLinkIndices.length := by
    rw [encLinkIndices_length]
    change (encLinkScheduled _).ram 38#256 = _
    rw [ram]
    simpa using data.2.2.2.2.2.2.2.2.1
  have outputCursor : ready.ram 33#256 = BitVec.ofNat 256 output := by
    change (encLinkScheduled _).ram 33#256 = _
    rw [ram]
    simpa using data.2.2.2.2.1.trans cursor
  change (eagerEncLinkRows oracle encLinkIndices (memory.bits 0) ready).2.2 = 7466
  exact eagerEncLinkRows_terminal oracle encLinkIndices (memory.bits 0) ready output
    (by intro empty; have size := encLinkIndices_length; rw [empty] at size; contradiction)
    count outputCursor lower (by simpa only [encLinkIndices_length] using upper)
    (by rw [encLinkIndices_length])

/-- A row shifts the current coordinate and switches to the saved y coordinate at the boundary. -/
theorem lazyEncLinkResult_coordinate (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word)
    (safe : memory.ram 33#256 ≠ 32#256 ∧ memory.ram 33#256 ≠ 35#256 ∧
      memory.ram 33#256 ≠ 36#256 ∧ memory.ram 33#256 ≠ 38#256) :
    (lazyEncLinkResult memory index rest answer).1.ram 35#256 =
      (if memory.ram 38#256 - 1 = 254#256 then memory.ram 36#256 else memory.ram 35#256 >>> 1) ∧
    (lazyEncLinkResult memory index rest answer).1.ram 36#256 = memory.ram 36#256 := by
  let before := lazyEncLinkReply (encLinkPrepared memory index rest) answer
  have ram : before.ram = Function.update (Function.update memory.ram 41#256 (memory.ram (memory.ram 32#256)))
      35#256 (memory.ram 35#256 >>> 1) :=
    (lazyEncLinkReply_state _ _).2.1.trans (encLinkPrepared_values memory index rest).2.2.2.1
  have cursor : before.ram 33#256 = memory.ram 33#256 := by rw [ram]; simp
  change (encLinkControlState (executeLinear encLinkFinish before)).1.ram 35#256 = _ ∧
    (encLinkControlState (executeLinear encLinkFinish before)).1.ram 36#256 = _
  rw [encLinkControlState_ram, encLinkFinish_counter before (by rw [cursor]; exact safe.2.2.2),
    encLinkFinish_ram before (by rw [cursor]; exact safe.1) (by rw [cursor]; exact safe.2.2.2)]
  simp only [ram]
  split <;> simp_all [Function.update_apply, Ne.symm safe.2.1, Ne.symm safe.2.2.1]

/-- Each row retains all source labels and advances the coordinate invariant. -/
theorem lazyEncLinkDataMemory_step (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) (position : Fin 508) (inputBase output : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (secondKey : Block)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y secondKey)
    (counter : memory.ram 38#256 = BitVec.ofNat 256 (508 - position.val))
    (cursor : memory.ram 33#256 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output < 2 ^ 96)
    (separate : ∀ offset, offset < 508 → inputBase + offset ≠ output) :
    EncLinkDataMemory (lazyEncLinkResult memory index rest answer).1
      (position.val + 1) inputBase labels x y secondKey := by
  have safe (cell : Nat) (small : cell < 256) : memory.ram 33#256 ≠ BitVec.ofNat 256 cell := by
    rw [cursor]
    exact encLinkOutput_separate output cell outputLower outputUpper small
  have cursors := lazyEncLinkResult_cursors memory index rest answer
    (safe 32 (by decide)) (safe 38 (by decide))
  have coordinates := lazyEncLinkResult_coordinate memory index rest answer
    ⟨safe 32 (by decide), safe 35 (by decide), safe 36 (by decide), safe 38 (by decide)⟩
  constructor
  · intro offset inside
    have valid : offset < 508 := by simpa only [List.length_ofFn] using inside
    have addressSmall : inputBase + offset < 2 ^ 96 := by omega
    have cellSafe (cell : Nat) (small : cell < 256) :
        BitVec.ofNat 256 (inputBase + offset) ≠ BitVec.ofNat 256 cell :=
      encLinkOutput_separate (inputBase + offset) cell (by omega) addressSmall small
    have distinct : BitVec.ofNat 256 (inputBase + offset) ≠ memory.ram 33#256 := by
      rw [cursor]
      intro equal
      have values := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans addressSmall (by decide : 2 ^ 96 < 2 ^ 256)),
        Nat.mod_eq_of_lt (lt_trans outputUpper (by decide : 2 ^ 96 < 2 ^ 256))] at values
      exact separate offset valid values
    have kept := lazyEncLinkResult_frame memory index rest answer
      (BitVec.ofNat 256 (inputBase + offset)) (safe 32 (by decide)) (safe 38 (by decide)) distinct
      ⟨cellSafe 32 (by decide), cellSafe 33 (by decide), cellSafe 35 (by decide),
        cellSafe 38 (by decide), cellSafe 41 (by decide)⟩
    have source := stored.stored offset inside
    simp only [Nat.zero_add, ← BitVec.ofNat_add] at source ⊢
    rw [kept]
    exact source
  · change (lazyEncLinkResult memory index rest answer).1.ram 32#256 = _
    have currentInput : memory.ram 32#256 = BitVec.ofNat 256 (inputBase + position.val) := stored.inputCursor
    rw [cursors.1, currentInput, BitVec.ofNat_add]
    simp only [Nat.add_assoc, BitVec.ofNat_add, show (1 : Word) = 1#256 from rfl, BitVec.add_assoc]
  · change (lazyEncLinkResult memory index rest answer).1.ram 35#256 = _
    rw [coordinates.1, counter]
    have subtraction : BitVec.ofNat 256 (508 - position.val) - 1 =
        BitVec.ofNat 256 (508 - position.val - 1) := by
      have positive : 1 ≤ 508 - position.val := by have := position.isLt; omega
      simpa only [show (1 : Word) = BitVec.ofNat 256 1 from rfl] using
        BitVec.ofNat_sub_ofNat_of_le (w := 256) (508 - position.val) 1 (by decide) positive
    have active : memory.ram 35#256 = encLinkCoordinateWord (508 - position.val) x y := stored.active
    have saved : memory.ram 36#256 = y.setWidth 256 := stored.saved
    rw [subtraction, active, saved]
    have boundary : BitVec.ofNat 256 (508 - position.val - 1) = 254#256 ↔
        508 - position.val - 1 = 254 := by
      constructor
      · intro equal
        have values := congrArg BitVec.toNat equal
        simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 508 - position.val - 1 < 2 ^ 256 by omega)] using values
      · intro equal; rw [equal]
    simp only [boundary]
    have step := encLinkCoordinateWord_step (508 - position.val) x y
      (by have := position.isLt; omega) (by omega)
    simpa only [Nat.sub_sub] using step
  · exact coordinates.2.trans stored.saved
  · exact (lazyEncLinkResult_frame memory index rest answer 40#256
      (safe 32 (by decide)) (safe 38 (by decide)) (Ne.symm (safe 40 (by decide)))
      (by decide)).trans stored.whitening

/-- The eager loop preserves every cell outside its output array and scratch cells. -/
theorem eagerEncLinkRows_frame
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (output : Nat) (cell : Word)
    (cursor : memory.ram 33#256 = BitVec.ofNat 256 output)
    (lower : 256 ≤ output) (upper : output + indices.length < 2 ^ 96)
    (scratch : cell ≠ 32#256 ∧ cell ≠ 33#256 ∧ cell ≠ 35#256 ∧ cell ≠ 38#256 ∧ cell ≠ 41#256)
    (separate : ∀ offset, offset < indices.length → cell ≠ BitVec.ofNat 256 (output + offset)) :
    (eagerEncLinkRows oracle indices suffix memory).1.ram cell = memory.ram cell := by
  induction indices generalizing memory output with
  | nil => rfl
  | cons index indices ih =>
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128
        ((encLinkPrepared memory index (indices.flatMap encLinkIndexBits ++ suffix)).registers 8).toNat)
    let answer := answerWords request (publicAnswer oracle request)
    let result := lazyEncLinkResult memory index (indices.flatMap encLinkIndexBits ++ suffix) answer
    have safe (value : Nat) (small : value < 256) : memory.ram 33#256 ≠ BitVec.ofNat 256 value := by
      rw [cursor]
      exact encLinkOutput_separate output value lower (by simp only [List.length_cons] at upper; omega) small
    have kept : result.1.ram cell = memory.ram cell :=
      lazyEncLinkResult_frame memory index _ answer cell (safe 32 (by decide)) (safe 38 (by decide))
        (by rw [cursor]; simpa only [Nat.add_zero] using separate 0 (by simp)) scratch
    have cursorStep := (lazyEncLinkResult_cursors memory index
      (indices.flatMap encLinkIndexBits ++ suffix) answer (safe 32 (by decide)) (safe 38 (by decide))).2.1
    have nextCursor : result.1.ram 33#256 = BitVec.ofNat 256 (output + 1) := by
      rw [cursorStep, cursor, BitVec.ofNat_add]
      rfl
    change (if result.2.2 = 7208 then
      let final := eagerEncLinkRows oracle indices suffix result.1
      (final.1, result.2.1 + final.2.1, final.2.2) else result).1.ram cell = _
    split
    · exact (ih result.1 (output + 1) nextCursor (by omega) (by
        simp only [List.length_cons] at upper; omega) (by
          intro offset valid
          have old := separate (offset + 1) (by simpa only [List.length_cons] using Nat.add_lt_add_right valid 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1] using old)).trans kept
    · exact kept

set_option backward.isDefEq.respectTransparency false in
/-- The eager row writes the exact typed EncPRF label. -/
theorem eagerEncLinkResult_label
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (position : Fin 508) (rest : List Bool) (inputBase : Nat)
    (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount) (keys : WhiteningKeys)
    (stored : EncLinkDataMemory memory position.val inputBase labels x y keys.second)
    (first : memory.ram 39#256 = keys.first.setWidth 256)
    (safe : memory.ram 33#256 ≠ 32#256 ∧ memory.ram 33#256 ≠ 33#256 ∧
      memory.ram 33#256 ≠ 35#256 ∧ memory.ram 33#256 ≠ 38#256) :
    let index := encLinkIndexAt position
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward index (BitVec.ofNat 128 ((encLinkPrepared memory index rest).registers 8).toNat)
    (lazyEncLinkResult memory index rest (answerWords request (publicAnswer oracle request))).1.ram
      (memory.ram 33#256) =
        (EncPRF.transformAt oracle.2.1 keys
          ⟨index.1, index.2, encLinkBitAt x y position⟩ (labels position)).setWidth 256 := by
  dsimp only
  rw [lazyEncLinkResult_output memory (encLinkIndexAt position) rest _ safe]
  have selected : memory.ram (memory.ram 32#256) = (labels position).setWidth 256 :=
    encLinkDataMemory_selected memory position inputBase labels x y keys.second stored
  have second : memory.ram 40#256 = keys.second.setWidth 256 := stored.whitening
  have active : memory.ram 35#256 = encLinkCoordinateWord (508 - position.val) x y := stored.active
  have operand : (encLinkPrepared memory (encLinkIndexAt position) rest).registers 8 =
      (xor (encodeBit (encLinkBitAt x y position)) keys.first).setWidth 256 := by
    rw [(encLinkPrepared_values _ _ _).1]
    change (memory.ram 35#256 &&& 1#256) ^^^ memory.ram 39#256 = _
    rw [active, first, encLink_lowBit, encLinkCoordinateWord_bit]
    exact BitVec.setWidth_xor.symm
  rw [operand, second, selected]
  simp only [answerWords, publicAnswer, EncPRF.transformAt, EncPRF.evenMansourPad,
    evenMansour, encrypt, Cryptography.xor, BitVec.toNat_setWidth, BitVec.setWidth_eq,
    BitVec.setWidth_xor]
  rw [← BitVec.setWidth_xor]
  have narrow (value : Block) : BitVec.ofNat 128 (value.setWidth 256).toNat = value := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (lt_trans value.isLt (by decide : 2 ^ 128 < 2 ^ 256)),
      Nat.mod_eq_of_lt value.isLt]
  have widen (value : Block) : BitVec.ofNat 256 value.toNat = value.setWidth 256 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [narrow, widen]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The eager loop stores every typed transformed label in its output array. -/
theorem eagerEncLinkRows_words
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (positions : List (Fin 508)) (position : Nat) (suffix : List Bool)
    (memory : Memory) (inputBase output : Nat) (labels : Fin 508 → Block)
    (x y : BitVec coordinateBitCount) (keys : WhiteningKeys)
    (order : EncLinkConsecutive position positions)
    (remaining : positions.length = 508 - position)
    (stored : EncLinkDataMemory memory position inputBase labels x y keys.second)
    (first : memory.ram 39#256 = keys.first.setWidth 256)
    (counter : memory.ram 38#256 = BitVec.ofNat 256 positions.length)
    (cursor : memory.ram 33#256 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + positions.length < 2 ^ 96)
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < positions.length →
      inputBase + inputOffset ≠ output + outputOffset) :
    WordsAt (eagerEncLinkRows oracle (positions.map encLinkIndexAt) suffix memory).1.ram
      (BitVec.ofNat 256 output) 0
      (positions.map fun pos => (EncPRF.transformAt oracle.2.1 keys
        ⟨(encLinkIndexAt pos).1, (encLinkIndexAt pos).2, encLinkBitAt x y pos⟩ (labels pos)).setWidth 256) := by
  induction positions generalizing position memory output with
  | nil => intro offset inside; simp at inside
  | cons head positions ih =>
    have headValue := encLinkConsecutive_head position head positions order
    have nextOrder := encLinkConsecutive_tail position head positions order
    have safe (cell : Nat) (small : cell < 256) : memory.ram 33#256 ≠ BitVec.ofNat 256 cell := by
      rw [cursor]
      exact encLinkOutput_separate output cell outputLower (by simp only [List.length_cons] at outputUpper; omega) small
    let rest := (positions.map encLinkIndexAt).flatMap encLinkIndexBits ++ suffix
    let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex :=
      .encForward (encLinkIndexAt head) (BitVec.ofNat 128
        ((encLinkPrepared memory (encLinkIndexAt head) rest).registers 8).toNat)
    let answer := answerWords request (publicAnswer oracle request)
    let result := lazyEncLinkResult memory (encLinkIndexAt head) rest answer
    have current : EncLinkDataMemory memory head.val inputBase labels x y keys.second := by
      simpa only [headValue] using stored
    have label := eagerEncLinkResult_label oracle memory head rest inputBase labels x y keys current first
      ⟨safe 32 (by decide), safe 33 (by decide), safe 35 (by decide), safe 38 (by decide)⟩
    change result.1.ram (memory.ram 33#256) = _ at label
    rw [cursor] at label
    have cursors := lazyEncLinkResult_cursors memory (encLinkIndexAt head) rest answer
      (safe 32 (by decide)) (safe 38 (by decide))
    have nextCursor : result.1.ram 33#256 = BitVec.ofNat 256 (output + 1) := by
      rw [cursors.2.1, cursor, BitVec.ofNat_add]
      rfl
    have nextCount : result.1.ram 38#256 = BitVec.ofNat 256 positions.length := by
      rw [cursors.2.2, counter, List.length_cons, BitVec.ofNat_add]
      simp
    have nextFirst : result.1.ram 39#256 = keys.first.setWidth 256 :=
      (lazyEncLinkResult_frame memory (encLinkIndexAt head) rest answer 39#256
        (safe 32 (by decide)) (safe 38 (by decide)) (Ne.symm (safe 39 (by decide))) (by decide)).trans first
    have nextData := lazyEncLinkDataMemory_step memory (encLinkIndexAt head) rest answer head inputBase output
      labels x y keys.second current (by rw [counter, remaining, headValue]) cursor
      inputLower inputUpper outputLower (by simp only [List.length_cons] at outputUpper; omega)
      (by intro offset inside; simpa only [Nat.add_zero] using separate offset inside 0 (by simp))
    have nextStored : EncLinkDataMemory result.1 (position + 1) inputBase labels x y keys.second := by
      simpa only [headValue] using nextData
    have nextRemaining : positions.length = 508 - (position + 1) := by
      have bound := head.isLt
      simp only [List.length_cons] at remaining
      omega
    have target := lazyEncLinkResult_target memory (encLinkIndexAt head) rest answer (safe 38 (by decide))
    rw [counter, List.length_cons, BitVec.ofNat_add] at target
    simp only [show (1 : Word) = 1#256 from rfl, add_sub_cancel_right] at target
    change result.2.2 = _ at target
    change WordsAt (if result.2.2 = 7208 then
      let final := eagerEncLinkRows oracle (positions.map encLinkIndexAt) suffix result.1
      (final.1, result.2.1 + final.2.1, final.2.2) else result).1.ram _ _ _
    by_cases empty : positions = []
    · subst positions
      simp only [List.length_nil, if_true] at target
      rw [target, if_neg (by decide)]
      intro offset inside
      have zero : offset = 0 := by
        simp only [List.map_cons, List.map_nil, List.length_cons, List.length_nil] at inside
        omega
      subst offset
      simpa only [Nat.zero_add, BitVec.add_zero, List.map_cons, List.getElem_cons_zero] using label
    · have positive : positions.length ≠ 0 := by intro zero; exact empty (List.length_eq_zero_iff.mp zero)
      have nonzero : BitVec.ofNat 256 positions.length ≠ 0#256 := by
        intro equal
        have values := congrArg BitVec.toNat equal
        have fits : positions.length < 2 ^ 256 := by simp only [List.length_cons] at remaining; omega
        simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at values
        exact positive values
      rw [if_neg nonzero] at target
      rw [target, if_pos rfl]
      have tailWords := ih (position + 1) result.1 (output + 1) nextOrder nextRemaining nextStored
        nextFirst nextCount nextCursor (by omega) (by simp only [List.length_cons] at outputUpper; omega)
        (by
          intro inputOffset inputInside outputOffset outputInside
          have old := separate inputOffset inputInside (outputOffset + 1) (by
            simpa only [List.length_cons] using Nat.add_lt_add_right outputInside 1)
          simpa only [Nat.add_assoc, Nat.add_comm 1] using old)
      have keptHead : (eagerEncLinkRows oracle (positions.map encLinkIndexAt) suffix result.1).1.ram
          (BitVec.ofNat 256 output) = result.1.ram (BitVec.ofNat 256 output) := by
        apply eagerEncLinkRows_frame oracle (positions.map encLinkIndexAt) suffix result.1 (output + 1)
          (BitVec.ofNat 256 output) nextCursor (by omega) (by
            simp only [List.length_map, List.length_cons] at outputUpper ⊢; omega)
        · have lowerSafe (cell : Nat) (small : cell < 256) :=
            encLinkOutput_separate output cell outputLower (by simp only [List.length_cons] at outputUpper; omega) small
          exact ⟨lowerSafe 32 (by decide), lowerSafe 33 (by decide), lowerSafe 35 (by decide),
            lowerSafe 38 (by decide), lowerSafe 41 (by decide)⟩
        · intro offset inside equal
          have values := congrArg BitVec.toNat equal
          have originalFits : output < 2 ^ 256 := by simp only [List.length_cons] at outputUpper; omega
          have nextFits : output + 1 + offset < 2 ^ 256 := by
            simp only [List.length_map] at inside
            simp only [List.length_cons] at outputUpper
            omega
          simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt originalFits, Nat.mod_eq_of_lt nextFits] at values
          omega
      intro offset inside
      cases offset with
      | zero =>
        simpa only [Nat.zero_add, BitVec.add_zero, List.map_cons, List.getElem_cons_zero] using keptHead.trans label
      | succ offset =>
        have tail := tailWords offset (by
          simp only [List.length_map, List.length_cons] at inside ⊢
          omega)
        simpa only [List.map_cons, List.getElem_cons_succ, Nat.zero_add, Nat.succ_eq_add_one,
          ← BitVec.ofNat_add, Nat.add_assoc, Nat.add_comm 1] using tail

/-- The fixed hash reply initializes both whitening keys in their source order. -/
theorem lazyEncLinkHashReply_keys (memory : Memory) (keys : Block × Block) :
    let ready := encLinkScheduled (lazyEncLinkHashReply memory
      (BitVec.ofNat 256 keys.1.toNat, BitVec.ofNat 256 keys.2.toNat))
    ready.ram 39#256 = keys.1.setWidth 256 ∧ ready.ram 40#256 = keys.2.setWidth 256 := by
  dsimp only
  change (encLinkScheduled _).ram (39 : Word) = _ ∧ (encLinkScheduled _).ram (40 : Word) = _
  rw [(encLinkScheduled_memory _).1]
  simp only [Function.update_self, Function.update_of_ne (by decide : (39 : Word) ≠ 40)]
  have widen (value : Block) : BitVec.ofNat 256 value.toNat = value.setWidth 256 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [widen keys.1, widen keys.2]
  simp [lazyEncLinkHashReply, executeLinear, LinearInstruction.execute, Arithmetic.eval]
  change (((keys.1.setWidth 256 <<< (128 : Nat)) ^^^ keys.2.setWidth 256) >>> (128 : Nat) = keys.1.setWidth 256) ∧
    (((keys.1.setWidth 256 <<< (128 : Nat)) ^^^ keys.2.setWidth 256) &&& BitVec.ofNat 256 (2 ^ 128 - 1) = keys.2.setWidth 256)
  rcases keys with ⟨first, second⟩
  constructor
  · apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index bound
    by_cases small : index < 128
    · simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth, small, bound, show 128 + index < 256 by omega,
        show ¬128 + index < 128 by omega]
    · simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth, small, bound, show ¬128 + index < 256 by omega,
        show ¬128 + index < 128 by omega, BitVec.getLsbD_of_ge _ _ (by omega : 128 ≤ index)]
  · apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro index bound
    have mask : (BitVec.ofNat 256 (2 ^ 128 - 1)).getLsbD index = decide (index < 128) := by
      simp only [BitVec.getLsbD, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by decide : 2 ^ 128 - 1 < 2 ^ 256), Nat.testBit_two_pow_sub_one]
    rw [BitVec.getLsbD_and, mask]
    by_cases small : index < 128
    · simp [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_setWidth, mask, small, bound]
    · simp [BitVec.getLsbD_and, mask, small, BitVec.getLsbD_setWidth,
        BitVec.getLsbD_of_ge _ _ (by omega : 128 ≤ index)]

/-- The private initialization retains the source array and sets the exact loop state. -/
theorem lazyEncLinkInitial_data (memory : Memory) (keys : Block × Block)
    (inputBase : Nat) (labels : Fin 508 → Block) (x y : BitVec coordinateBitCount)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = x.setWidth 256) (inputY : memory.registers 13 = y.setWidth 256)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0
      (List.ofFn fun index => (labels index).setWidth 256)) :
    let ready := encLinkScheduled (lazyEncLinkHashReply (executeLinear encLinkSave memory)
      (BitVec.ofNat 256 keys.1.toNat, BitVec.ofNat 256 keys.2.toNat))
    EncLinkDataMemory ready 0 inputBase labels x y keys.2 ∧
    ready.ram 39#256 = keys.1.setWidth 256 ∧ ready.ram 38#256 = 508#256 ∧
    ready.ram 33#256 = memory.registers 14 := by
  dsimp only
  let saved := executeLinear encLinkSave memory
  let hashed := lazyEncLinkHashReply saved (BitVec.ofNat 256 keys.1.toNat, BitVec.ofNat 256 keys.2.toNat)
  have save := encLinkSave_state memory
  have ram := (encLinkScheduled_memory hashed).1
  rw [(lazyEncLinkHashReply_memory _ _).1] at ram
  have pair := lazyEncLinkHashReply_keys saved keys
  have frame (cell : Nat) (lower : 256 ≤ cell) (upper : cell < 2 ^ 96) :
      (encLinkScheduled hashed).ram (BitVec.ofNat 256 cell) = memory.ram (BitVec.ofNat 256 cell) := by
    have ne40 : BitVec.ofNat 256 cell ≠ (40 : Word) := encLinkOutput_separate cell 40 lower upper (by decide)
    have ne39 : BitVec.ofNat 256 cell ≠ (39 : Word) := encLinkOutput_separate cell 39 lower upper (by decide)
    rw [ram, Function.update_of_ne ne40, Function.update_of_ne ne39]
    exact encLinkSaved_private memory cell lower upper
  refine ⟨?_, pair.1, ?_, ?_⟩
  · constructor
    · intro offset inside
      have bound : offset < 508 := by simpa only [List.length_ofFn] using inside
      rw [Nat.zero_add, ← BitVec.ofNat_add, frame (inputBase + offset) (by omega) (by omega)]
      simpa only [Nat.zero_add, ← BitVec.ofNat_add] using stored offset inside
    · rw [ram]
      simp only [Function.update_of_ne (by decide : (32 : Word) ≠ 40),
        Function.update_of_ne (by decide : (32 : Word) ≠ 39), Nat.add_zero]
      exact save.2.2.2.1.trans inputPointer
    · rw [ram]
      simp only [Function.update_of_ne (by decide : (35 : Word) ≠ 40),
        Function.update_of_ne (by decide : (35 : Word) ≠ 39)]
      simpa [encLinkCoordinateWord] using save.2.2.2.2.2.2.1.trans inputX
    · rw [ram]
      simp only [Function.update_of_ne (by decide : (36 : Word) ≠ 40),
        Function.update_of_ne (by decide : (36 : Word) ≠ 39)]
      exact save.2.2.2.2.2.2.2.1.trans inputY
    · exact pair.2
  · rw [ram]
    simpa using save.2.2.2.2.2.2.2.2.1
  · rw [ram]
    simpa using save.2.2.2.2.1

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The complete eager link stores the exact transformed label array. -/
theorem eagerEncLinkSamples_words
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (inputBase output : Nat) (labels : Fin 508 → Block)
    (x y : BitVec coordinateBitCount)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = x.setWidth 256) (inputY : memory.registers 13 = y.setWidth 256)
    (outputPointer : memory.registers 14 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0
      (List.ofFn fun index => (labels index).setWidth 256))
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset) :
    let pair := oracle.2.2 (memory.registers 8).toNat
    let keys : WhiteningKeys := ⟨pair.1, pair.2⟩
    WordsAt (eagerEncLinkSamples oracle memory).1.ram (BitVec.ofNat 256 output) 0
      ((List.finRange 508).map fun pos => (EncPRF.transformAt oracle.2.1 keys
        ⟨(encLinkIndexAt pos).1, (encLinkIndexAt pos).2, encLinkBitAt x y pos⟩ (labels pos)).setWidth 256) := by
  dsimp only
  let pair := oracle.2.2 (memory.registers 8).toNat
  let ready := encLinkScheduled (lazyEncLinkHashReply (executeLinear encLinkSave memory)
    (BitVec.ofNat 256 pair.1.toNat, BitVec.ofNat 256 pair.2.toNat))
  have data := lazyEncLinkInitial_data memory pair inputBase labels x y
    inputPointer inputX inputY inputLower inputUpper stored
  have word := eagerEncLinkRows_words oracle (List.finRange 508) 0 (memory.bits 0) ready inputBase output labels x y
    ⟨pair.1, pair.2⟩ encLinkPositions_consecutive (by simp) data.1 data.2.1
    (by simpa only [List.length_finRange] using data.2.2.1) (data.2.2.2.trans outputPointer)
    inputLower inputUpper outputLower (by simpa only [List.length_finRange] using outputUpper)
    (by simpa only [List.length_finRange] using separate)
  rw [encLinkPositions_indices] at word
  have source : (eagerEncLinkSamples oracle memory).1 =
      (eagerEncLinkRows oracle encLinkIndices (memory.bits 0) ready).1 := by
    simp only [eagerEncLinkSamples, publicAnswer, answerWords, (encLinkSave_state memory).1]
    rfl
  rw [source]
  exact word

/-- Every link row preserves the other caller bit stacks. -/
theorem lazyEncLinkResult_bits_other (memory : Memory) (index : EncPRF.PermutationIndex)
    (rest : List Bool) (answer : Word × Word) (stack : Fin 4) (other : stack ≠ 0) :
    (lazyEncLinkResult memory index rest answer).1.bits stack = memory.bits stack := by
  dsimp only [lazyEncLinkResult]
  rw [encLinkControlState_bits, encLinkFinish_bits, (lazyEncLinkReply_state _ _).2.2]
  dsimp only [encLinkPrepared]
  rw [(encLinkPrepare_state _).2.2.2.2]
  simp [decodedInput, inputFinal, inputFrame, other]

/-- The eager link loop preserves the other caller bit stacks. -/
theorem eagerEncLinkRows_bits_other
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (indices : List EncPRF.PermutationIndex) (suffix : List Bool) (memory : Memory)
    (stack : Fin 4) (other : stack ≠ 0) :
    (eagerEncLinkRows oracle indices suffix memory).1.bits stack = memory.bits stack := by
  induction indices generalizing memory with
  | nil => rfl
  | cons index indices ih =>
    rw [eagerEncLinkRows]
    split
    · exact (ih _).trans (lazyEncLinkResult_bits_other _ _ _ _ stack other)
    · exact lazyEncLinkResult_bits_other _ _ _ _ stack other

/-- The complete eager link preserves the other caller bit stacks. -/
theorem eagerEncLinkSamples_bits_other
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (stack : Fin 4) (other : stack ≠ 0) :
    (eagerEncLinkSamples oracle memory).1.bits stack = memory.bits stack := by
  dsimp only [eagerEncLinkSamples]
  rw [eagerEncLinkRows_bits_other oracle encLinkIndices (memory.bits 0) _ stack other,
    (encLinkScheduled_memory _).2, Function.update_of_ne other,
    (lazyEncLinkHashReply_memory _ _).2, (encLinkSave_state memory).2.2.2.2.2.2.2.2.2]

/-- The complete eager link preserves caller data outside its output array. -/
theorem eagerEncLinkSamples_frame
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (output cell : Nat)
    (pointer : memory.registers 14 = BitVec.ofNat 256 output)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (lower : 256 ≤ cell) (upper : cell < 2 ^ 96)
    (separate : ∀ offset, offset < 508 → cell ≠ output + offset) :
    (eagerEncLinkSamples oracle memory).1.ram (BitVec.ofNat 256 cell) =
      memory.ram (BitVec.ofNat 256 cell) := by
  let saved := executeLinear encLinkSave memory
  let request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex := .hash (saved.registers 8).toNat
  let hashed := lazyEncLinkHashReply saved (answerWords request (publicAnswer oracle request))
  let ready := encLinkScheduled hashed
  have ram := (encLinkScheduled_memory hashed).1
  rw [(lazyEncLinkHashReply_memory _ _).1] at ram
  have nextCursor : ready.ram 33#256 = BitVec.ofNat 256 output := by
    change (encLinkScheduled hashed).ram 33#256 = _
    rw [ram]
    simpa using (encLinkSave_state memory).2.2.2.2.1.trans pointer
  have safe (scratch : Nat) (small : scratch < 256) :
      BitVec.ofNat 256 cell ≠ BitVec.ofNat 256 scratch :=
    encLinkOutput_separate cell scratch lower upper small
  have kept := eagerEncLinkRows_frame oracle encLinkIndices (memory.bits 0) ready output
    (BitVec.ofNat 256 cell) nextCursor outputLower (by simpa only [encLinkIndices_length] using outputUpper)
    ⟨safe 32 (by decide), safe 33 (by decide), safe 35 (by decide), safe 38 (by decide), safe 41 (by decide)⟩
    (by
      intro offset inside equal
      have values := congrArg BitVec.toNat equal
      have targetFits : output + offset < 2 ^ 256 := by rw [encLinkIndices_length] at inside; omega
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans upper (by decide : 2 ^ 96 < 2 ^ 256)),
        Nat.mod_eq_of_lt targetFits] at values
      exact separate offset (by simpa only [encLinkIndices_length] using inside) values)
  change (eagerEncLinkRows oracle encLinkIndices (memory.bits 0) ready).1.ram _ = _
  rw [kept]
  have ne40 : BitVec.ofNat 256 cell ≠ (40 : Word) := safe 40 (by decide)
  have ne39 : BitVec.ofNat 256 cell ≠ (39 : Word) := safe 39 (by decide)
  change (encLinkScheduled hashed).ram _ = _
  rw [ram, Function.update_of_ne ne40, Function.update_of_ne ne39]
  exact encLinkSaved_private memory cell lower upper

set_option backward.isDefEq.respectTransparency false in
/-- The complete eager link returns the exact typed EncPRF MAC. -/
theorem eagerEncLinkSamples_mac
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (memory : Memory) (inputBase output : Nat) (input : BitInput) (mac : InputMac)
    (inputPointer : memory.registers 11 = BitVec.ofNat 256 inputBase)
    (inputX : memory.registers 12 = input.xBits.setWidth 256)
    (inputY : memory.registers 13 = input.yBits.setWidth 256)
    (outputPointer : memory.registers 14 = BitVec.ofNat 256 output)
    (inputLower : 256 ≤ inputBase) (inputUpper : inputBase + 508 ≤ 2 ^ 96)
    (outputLower : 256 ≤ output) (outputUpper : output + 508 < 2 ^ 96)
    (stored : WordsAt memory.ram (BitVec.ofNat 256 inputBase) 0
      (List.ofFn fun index => (encLinkMacLabels mac index).setWidth 256))
    (separate : ∀ inputOffset, inputOffset < 508 → ∀ outputOffset, outputOffset < 508 →
      inputBase + inputOffset ≠ output + outputOffset) :
    encLinkOutputMac (eagerEncLinkSamples oracle memory).1 output =
      EncPRF.transformMac oracle.2.1 (EncPRF.whiteningKeys oracle.2.2 (memory.registers 8).toNat) input mac := by
  exact encLinkOutputMac_transform _ _ _ _ _ _
    (eagerEncLinkSamples_words oracle memory inputBase output (encLinkMacLabels mac) input.xBits input.yBits
      inputPointer inputX inputY outputPointer inputLower inputUpper outputLower outputUpper stored separate)

end Kriterion.ArgoMAC.ArithmeticSimulator
