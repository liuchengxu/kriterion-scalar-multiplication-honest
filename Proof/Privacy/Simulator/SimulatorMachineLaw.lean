import Proof.Privacy.Simulator.SimulatorOracleProgram
import Proof.Privacy.Simulator.OperationalFamilyLaw
import Proof.Privacy.Simulator.OperationalHashLaw
import Proof.Privacy.Simulator.OperationalCompositionLaw

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open OperationalOracle
namespace SimulatorMachine

/-- The sparse family uses the exact fixed-key and EncPRF indices. -/
abbrev OracleIndex := Pipeline.FixedKeyIndex ⊕ EncPRF.PermutationIndex

/-- The block conversion preserves the exact 128-bit value. -/
def blockFin : Block ≃ Fin (2 ^ 128) := BitVec.equivFin.toEquiv

/-- The hash conversion packs two 128-bit values into one bounded integer. -/
def hashFin : (Block × Block) ≃ Fin (2 ^ 256) :=
  ((Equiv.prodCongr blockFin blockFin).trans finProdFinEquiv).trans
    (finCongr (by norm_num : 2 ^ 128 * 2 ^ 128 = 2 ^ 256))

/-- This conversion changes only the finite representation of a permutation. -/
def blockPermutation (π : Equiv.Perm (Fin (2 ^ 128))) : Equiv.Perm Block :=
  blockFin.trans (π.trans blockFin.symm)

/-- The sparse state keeps the original transcript and collision metadata. -/
structure Metadata where
  fixedTranscript : List (PermutationRecord Pipeline.FixedKeyIndex Block)
  encTranscript : List (PermutationRecord EncPRF.PermutationIndex Block)
  hashTranscript : List HashRecord
  commitments : List LabelCommitment
  linking : Option LinkingState
  bad : Bool

/-- The oracle data contains only sparse families and a sparse hash table. -/
abbrev OracleData := FamilyState OracleIndex (2 ^ 128) × HashTable BaseField (2 ^ 256)

/-- A completion pairs each sparse oracle with its conditional eager oracle. -/
abbrev OracleCompletion :=
  (OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128))) ×
    (HashTable BaseField (2 ^ 256) × (BaseField → Fin (2 ^ 256)))

/-- This function applies each deferred swap in the completed family. -/
def visible (family : OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128)))
    (index : OracleIndex) : Equiv.Perm Block :=
  blockPermutation ((family index).1.denote (family index).2)

/-- The decoder supplies the exact oracle representations in the original simulator. -/
def decode (metadata : Metadata) (complete : OracleCompletion) : SimulatorState where
  fixedOracle := ⟨fun index => visible complete.1 (.inl index)⟩
  encOracle := ⟨fun index => visible complete.1 (.inr index)⟩
  hashOracle := fun input => hashFin.symm (complete.2.2 input)
  fixedTranscript := metadata.fixedTranscript
  encTranscript := metadata.encTranscript
  hashTranscript := metadata.hashTranscript
  commitments := metadata.commitments
  linking := metadata.linking
  bad := metadata.bad

/-- The complete sparse simulator state contains no full random oracle. -/
structure SparseState where
  oracles : OracleData
  metadata : Metadata

/-- The lower oracle separates the permutation family from the hash table. -/
abbrev lowerSpec := sumSpec (familySpec OracleIndex (2 ^ 128)) (hashSpec BaseField (2 ^ 256))

/-- The lower eager state retains all base permutations and deferred swaps. -/
abbrev lowerEager := sumEager (familyEager (Index := OracleIndex) (size := 2 ^ 128))
  (hashEager (Key := BaseField) (size := 2 ^ 256))

/-- The lower sampled handler has one bounded draw per request. -/
noncomputable abbrev lowerSampled := sumSampled (familySampled (Index := OracleIndex) (size := 2 ^ 128))
  (hashSampled (Key := BaseField) (size := 2 ^ 256) (by norm_num))

/-- The lower completion kernel samples the two independent oracle components. -/
noncomputable def lowerCompletion (oracles : OracleData) : PMF OracleCompletion :=
  productKernel familyCompletion (hashCompletion (by norm_num : 0 < 2 ^ 256)) oracles

/-- The executable lower operation touches only the selected sparse oracle. -/
def lowerDraw (query : lowerSpec.Query) (oracles : OracleData) :
    Draw (lowerSpec.Answer query × OracleData) :=
  match query with
  | .inl request => (familyDraw request oracles.1).map (fun answer => (answer.1, answer.2, oracles.2))
  | .inr input => (oracles.2.query (by norm_num) input).map (fun answer => (answer.1, oracles.1, answer.2))

/-- The lower operation has the product handler's exact law. -/
theorem lowerDraw_distribution (query : lowerSpec.Query) (oracles : OracleData) :
    (lowerDraw query oracles).distribution = lowerSampled query oracles := by
  cases query <;> simp only [lowerDraw, Draw.map_distribution, familyDraw_distribution,
    lowerSampled, sumSampled, hashSampled]

/-- The lower oracle supplies the full conditional state law for each request. -/
theorem lower_step (query : lowerSpec.Query) (oracles : OracleData) :
    (lowerCompletion oracles).map (lowerEager query) =
      (lowerSampled query oracles).bind (fun answer =>
        (lowerCompletion answer.2).map (fun completed => (answer.1, completed))) :=
  productKernel_step familyEager (hashEager (Key := BaseField) (size := 2 ^ 256))
    familySampled (hashSampled (Key := BaseField) (size := 2 ^ 256) (by norm_num))
    familyCompletion (hashCompletion (Key := BaseField) (size := 2 ^ 256) (by norm_num))
    family_step (hash_step (Key := BaseField) (size := 2 ^ 256) (by norm_num)) query oracles

/-- Each simulator request selects its exact lower oracle operation. -/
def lowerRequest : spec.Query → lowerSpec.Query
  | .read (.fixedForward index input) => .inl (.inl index, .forward (blockFin input))
  | .read (.fixedInverse index output) => .inl (.inl index, .inverse (blockFin output))
  | .read (.encForward index input) => .inl (.inr index, .forward (blockFin input))
  | .read (.encInverse index output) => .inl (.inr index, .inverse (blockFin output))
  | .read (.hash input) => .inr input
  | .program command => .inl (.inl command.1, .program (blockFin command.2.1) (blockFin command.2.2))

/-- The answer conversion preserves each original public oracle answer. -/
def lowerAnswer : (request : spec.Query) → lowerSpec.Answer (lowerRequest request) → spec.Answer request
  | .read (.fixedForward _ _), value => blockFin.symm value
  | .read (.fixedInverse _ _), value => blockFin.symm value
  | .read (.encForward _ _), value => blockFin.symm value
  | .read (.encInverse _ _), value => blockFin.symm value
  | .read (.hash _), value => hashFin.symm value
  | .program _, _ => ()

/-- A successful programming request records the original transcript entry. -/
def Metadata.program (metadata : Metadata) (command : FixedCommand) : Metadata :=
  { metadata with fixedTranscript :=
      PermutationRecord.mk .program .simulator command.1 command.2.1 command.2.2 :: metadata.fixedTranscript }

/-- A failed programming request records the original bad flag. -/
def Metadata.markBad (metadata : Metadata) : Metadata := { metadata with bad := true }

/-- A successful lower operation changes only the required transcript metadata. -/
def afterMetadata : spec.Query → Metadata → Metadata
  | .read _, metadata => metadata
  | .program command, metadata => metadata.program command

/-- The sparse handler uses the original freshness branch and collision flag. -/
def sparseDraw (request : spec.Query) (state : SparseState) : Draw (spec.Answer request × SparseState) :=
  match request with
  | .read query => (lowerDraw (lowerRequest (.read query)) state.oracles).map
      (fun answer => (lowerAnswer (.read query) answer.1, { state with oracles := answer.2 }))
  | .program command =>
      if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2 then
        (lowerDraw (lowerRequest (.program command)) state.oracles).map (fun answer =>
          ((), { oracles := answer.2, metadata := state.metadata.program command }))
      else .pure ((), { state with metadata := state.metadata.markBad })

/-- The sampled handler interprets the executable bounded draw. -/
noncomputable def sparseHandler (request : spec.Query) (state : SparseState) :
    PMF (spec.Answer request × SparseState) := (sparseDraw request state).distribution

/-- The simulator completion kernel retains the original metadata. -/
noncomputable def completion (state : SparseState) : PMF SimulatorState :=
  (lowerCompletion state.oracles).map (decode state.metadata)

/-- An external read records the original adversary query and answer. -/
def Metadata.record : (query : Garbling.OracleQuery) → Garbling.OracleAnswer query → Metadata → Metadata
  | .fixedForward index input, output, metadata =>
      { metadata with fixedTranscript :=
          PermutationRecord.mk .forward .adversary index input output :: metadata.fixedTranscript }
  | .fixedInverse index output, input, metadata =>
      { metadata with fixedTranscript :=
          PermutationRecord.mk .inverse .adversary index input output :: metadata.fixedTranscript }
  | .encForward index input, output, metadata =>
      { metadata with encTranscript :=
          PermutationRecord.mk .forward .adversary index input output :: metadata.encTranscript }
  | .encInverse index output, input, metadata =>
      { metadata with encTranscript :=
          PermutationRecord.mk .inverse .adversary index input output :: metadata.encTranscript }
  | .hash input, output, metadata =>
      { metadata with hashTranscript := {input, output} :: metadata.hashTranscript }

/-- The external sparse operation also records the public query transcript. -/
def externalDraw (query : Garbling.OracleQuery) (state : SparseState) :
    Draw (Garbling.OracleAnswer query × SparseState) :=
  (sparseDraw (.read query) state).map (fun answer =>
    (answer.1, { answer.2 with metadata := answer.2.metadata.record query answer.1 }))

/-- This specification permits internal and external operations on the same oracle state. -/
abbrev combinedSpec := sumSpec spec Garbling.oracleSpec

/-- The eager combined handler uses the original internal and adversary handlers. -/
def combinedEager : OracleHandler combinedSpec SimulatorState
  | .inl request, state => handler request state
  | .inr query, state => idealOracleHandler query state

/-- The executable combined operation shares the same sparse state across both request types. -/
def combinedDraw (query : combinedSpec.Query) (state : SparseState) :
    Draw (combinedSpec.Answer query × SparseState) :=
  match query with
  | .inl request => sparseDraw request state
  | .inr request => externalDraw request state

/-- The combined probability law interprets the same executable bounded draw. -/
noncomputable def combinedHandler (query : combinedSpec.Query) (state : SparseState) :
    PMF (combinedSpec.Answer query × SparseState) := (combinedDraw query state).distribution

/-- Converting a swap preserves its action on every value. -/
theorem blockPermutation_swap (π : Equiv.Perm (Fin (2 ^ 128))) (input target : Block) :
    blockPermutation (π.trans (Equiv.swap (π (blockFin input)) (blockFin target))) =
      (blockPermutation π).trans (Equiv.swap ((blockPermutation π) input) target) := by
  apply Equiv.ext
  intro value
  simp only [blockPermutation, Equiv.trans_apply]
  by_cases first : π (blockFin value) = π (blockFin input)
  · have same : value = input := blockFin.injective (π.injective first)
    subst value
    simp
  · by_cases second : π (blockFin value) = blockFin target
    · rw [second, Equiv.swap_apply_right, Equiv.symm_apply_apply, Equiv.swap_apply_right]
    · have first' : blockFin.symm (π (blockFin value)) ≠ blockFin.symm (π (blockFin input)) :=
        fun equal => first (blockFin.symm.injective equal)
      have second' : blockFin.symm (π (blockFin value)) ≠ target :=
        fun equal => second (blockFin.symm_apply_eq.mp equal)
      rw [Equiv.swap_apply_of_ne_of_ne first second,
        Equiv.swap_apply_of_ne_of_ne first' second']

/-- A local state update changes only the selected visible permutation. -/
theorem visible_update
    (family : OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128)))
    (index : OracleIndex) (next : ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128))) :
    visible (Function.update family index next) =
      Function.update (visible family) index (blockPermutation (next.1.denote next.2)) := by
  funext current
  by_cases same : current = index
  · subst current
    simp only [visible, Function.update_self]
  · simp only [visible, Function.update_of_ne same]

/-- A forward read does not change the completed visible oracle. -/
theorem visible_forward
    (family : OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128)))
    (index : OracleIndex) (input : Fin (2 ^ 128)) :
    visible (familyEager (index, .forward input) family).2 = visible family := by
  simp only [familyEager, indexedEager, programEager, visible_update,
    ProgrammedPermutation.denote]
  exact Function.update_eq_self _ _

/-- An inverse read does not change the completed visible oracle. -/
theorem visible_inverse
    (family : OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128)))
    (index : OracleIndex) (output : Fin (2 ^ 128)) :
    visible (familyEager (index, .inverse output) family).2 = visible family := by
  simp only [familyEager, indexedEager, programEager, visible_update,
    ProgrammedPermutation.denote]
  exact Function.update_eq_self _ _

/-- A programming request performs the original visible output swap. -/
theorem visible_program
    (family : OracleIndex → ProgrammedPermutation (2 ^ 128) × Equiv.Perm (Fin (2 ^ 128)))
    (index : OracleIndex) (input target : Block) :
    visible (familyEager (index, .program (blockFin input) (blockFin target)) family).2 =
      Function.update (visible family) index
        ((visible family index).trans (Equiv.swap (visible family index input) target)) := by
  simp only [familyEager, indexedEager, programEager, visible_update]
  rw [ProgrammedPermutation.afterProgram_exact, blockPermutation_swap]
  rfl

/-- The decoder preserves all three-phase internal read answers and oracle states. -/
theorem decode_read (metadata : Metadata) (complete : OracleCompletion) (query : Garbling.OracleQuery) :
    let answer := lowerEager (lowerRequest (.read query)) complete
    (lowerAnswer (.read query) answer.1, decode metadata answer.2) =
      handler (.read query) (decode metadata complete) := by
  cases query with
  | fixedForward index input =>
      apply Prod.ext
      · rfl
      · change decode metadata ((familyEager (.inl index, .forward (blockFin input)) complete.1).2, complete.2) = _
        unfold decode
        rw [visible_forward]
        rfl
  | fixedInverse index output =>
      apply Prod.ext
      · rfl
      · change decode metadata ((familyEager (.inl index, .inverse (blockFin output)) complete.1).2, complete.2) = _
        unfold decode
        rw [visible_inverse]
        rfl
  | encForward index input =>
      apply Prod.ext
      · rfl
      · change decode metadata ((familyEager (.inr index, .forward (blockFin input)) complete.1).2, complete.2) = _
        unfold decode
        rw [visible_forward]
        rfl
  | encInverse index output =>
      apply Prod.ext
      · rfl
      · change decode metadata ((familyEager (.inr index, .inverse (blockFin output)) complete.1).2, complete.2) = _
        unfold decode
        rw [visible_inverse]
        rfl
  | hash input => rfl

/-- Successful lower programming gives the original programmed state and transcript. -/
theorem decode_program (metadata : Metadata) (complete : OracleCompletion) (command : FixedCommand) :
    decode (metadata.program command) (lowerEager (lowerRequest (.program command)) complete).2 =
      programFixed (decode metadata complete) command.1 command.2.1 command.2.2 := by
  change decode (metadata.program command)
    ((familyEager (.inl command.1, .program (blockFin command.2.1) (blockFin command.2.2)) complete.1).2,
      complete.2) = _
  unfold decode
  rw [visible_program]
  unfold programFixed programPermutation Metadata.program
  congr 1
  · apply congrArg PermutationOracle.mk
    funext index
    by_cases same : index = command.1
    · subst index
      simp only [Function.update_self, ite_true]
    · have different : (Sum.inl index : OracleIndex) ≠ .inl command.1 :=
        fun equal => same (Sum.inl.inj equal)
      rw [Function.update_of_ne different, if_neg same]

/-- A failed programming request changes only the original collision flag. -/
theorem decode_markBad (metadata : Metadata) (complete : OracleCompletion) :
    decode metadata.markBad complete = markBad (decode metadata complete) := rfl

/-- The sparse internal handler preserves the full completed simulator law. -/
theorem sparse_step (request : spec.Query) (state : SparseState) :
    (completion state).map (handler request) =
      (sparseHandler request state).bind (fun answer =>
        (completion answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  cases request with
  | read query =>
      have law := congrArg
        (fun distribution : PMF (lowerSpec.Answer (lowerRequest (.read query)) × OracleCompletion) =>
          distribution.map (fun answer =>
            (lowerAnswer (.read query) answer.1, decode state.metadata answer.2)))
        (lower_step (lowerRequest (.read query)) state.oracles)
      rw [← lowerDraw_distribution (lowerRequest (.read query)) state.oracles] at law
      simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at law
      rw [funext (fun complete => decode_read state.metadata complete query)] at law
      simpa only [completion, sparseHandler, sparseDraw, Draw.map_distribution,
        PMF.bind_map, PMF.map_comp, Function.comp_def] using law
  | program command =>
      by_cases fresh : freshPermutationPairCheck state.metadata.fixedTranscript
          command.1 command.2.1 command.2.2 = true
      · have law := congrArg
          (fun distribution : PMF (lowerSpec.Answer (lowerRequest (.program command)) × OracleCompletion) =>
            distribution.map (fun answer => ((), decode (state.metadata.program command) answer.2)))
          (lower_step (lowerRequest (.program command)) state.oracles)
        rw [← lowerDraw_distribution (lowerRequest (.program command)) state.oracles] at law
        simp only [PMF.map_comp, PMF.map_bind, Function.comp_def, decode_program] at law
        have eager (complete : OracleCompletion) :
            handler (.program command) (decode state.metadata complete) =
              ((), programFixed (decode state.metadata complete) command.1 command.2.1 command.2.2) := by
          change ((), if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2
            then programFixed (decode state.metadata complete) command.1 command.2.1 command.2.2
            else markBad (decode state.metadata complete)) = _
          rw [if_pos fresh]
        simp only [completion, PMF.map_comp, Function.comp_def]
        simp_rw [eager]
        simpa only [completion, sparseHandler, sparseDraw, if_pos fresh,
          Draw.map_distribution, PMF.bind_map, PMF.map_comp, Function.comp_def] using law
      · have eager (complete : OracleCompletion) :
            handler (.program command) (decode state.metadata complete) =
              ((), decode state.metadata.markBad complete) := by
          change ((), if freshPermutationPairCheck state.metadata.fixedTranscript command.1 command.2.1 command.2.2
            then programFixed (decode state.metadata complete) command.1 command.2.1 command.2.2
            else markBad (decode state.metadata complete)) = _
          rw [if_neg fresh]
          rfl
        simp only [completion, sparseHandler, sparseDraw, if_neg fresh, Draw.distribution,
          PMF.pure_bind, PMF.map_comp, Function.comp_def]
        simp_rw [eager]

/-- The internal simulator may adapt every later request to its earlier answers. -/
theorem sparse_adaptive_joint {Result : Type} {budget : Nat}
    (program : OracleProgram spec Result budget) (state : SparseState) :
    (completion state).bind (fun eagerState => program.run handler eagerState) =
      (runSampled sparseHandler program state).bind (fun output =>
        (completion output.2).map (fun eagerState => (output.1, eagerState))) :=
  adaptive_joint_law handler sparseHandler completion sparse_step program state

/-- This operation records a supplied oracle answer in the eager transcript. -/
def recordEager : (query : Garbling.OracleQuery) → Garbling.OracleAnswer query → SimulatorState → SimulatorState
  | .fixedForward index input, output, state =>
      recordFixed state (PermutationRecord.mk .forward .adversary index input output)
  | .fixedInverse index output, input, state =>
      recordFixed state (PermutationRecord.mk .inverse .adversary index input output)
  | .encForward index input, output, state =>
      recordEnc state (PermutationRecord.mk .forward .adversary index input output)
  | .encInverse index output, input, state =>
      recordEnc state (PermutationRecord.mk .inverse .adversary index input output)
  | .hash input, output, state => recordHash state {input, output}

/-- The sparse and eager transcript updates agree exactly. -/
theorem decode_record (metadata : Metadata) (complete : OracleCompletion)
    (query : Garbling.OracleQuery) (answer : Garbling.OracleAnswer query) :
    decode (metadata.record query answer) complete = recordEager query answer (decode metadata complete) := by
  cases query <;> rfl

/-- Recording an internal read gives the original adversary handler. -/
theorem recorded_read (query : Garbling.OracleQuery) (state : SimulatorState) :
    ((handler (.read query) state).1,
      recordEager query (handler (.read query) state).1 (handler (.read query) state).2) =
      idealOracleHandler query state := by
  cases query <;> rfl

/-- The external sparse handler also preserves the full joint law and recorded history. -/
theorem external_step (query : Garbling.OracleQuery) (state : SparseState) :
    (completion state).map (idealOracleHandler query) =
      (externalDraw query state).distribution.bind (fun answer =>
        (completion answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  have law := congrArg
    (fun distribution : PMF (Garbling.OracleAnswer query × SimulatorState) =>
      distribution.map (fun answer => (answer.1, recordEager query answer.1 answer.2)))
    (sparse_step (.read query) state)
  simp only [PMF.map_comp, PMF.map_bind, Function.comp_def] at law
  cases query <;>
    simpa only [externalDraw, Draw.map_distribution, sparseHandler, completion,
      PMF.bind_map, PMF.map_comp, Function.comp_def, decode_record,
      handler, idealOracleHandler, oracleHandlerFor, recordEager] using law

/-- Internal and external operations preserve one shared complete simulator law. -/
theorem combined_step (query : combinedSpec.Query) (state : SparseState) :
    (completion state).map (combinedEager query) =
      (combinedHandler query state).bind (fun answer =>
        (completion answer.2).map (fun eagerState => (answer.1, eagerState))) := by
  cases query with
  | inl request => exact sparse_step request state
  | inr request => exact external_step request state

/-- The joint law covers every adaptive interleaving of adversary and simulator operations. -/
theorem combined_adaptive_joint {Result : Type} {budget : Nat}
    (program : OracleProgram combinedSpec Result budget) (state : SparseState) :
    (completion state).bind (fun eagerState => program.run combinedEager eagerState) =
      (runSampled combinedHandler program state).bind (fun output =>
        (completion output.2).map (fun eagerState => (output.1, eagerState))) :=
  adaptive_joint_law combinedEager combinedHandler completion combined_step program state

end SimulatorMachine
end Kriterion.ArgoMAC.Security
