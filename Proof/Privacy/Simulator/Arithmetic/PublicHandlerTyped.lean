import Proof.Privacy.Simulator.Arithmetic.PublicHandlerBits

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The typed value uses one low block for permutations and both packed blocks for hashes. -/
noncomputable def publicAnswerValue {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (value : Word) : request.Answer :=
  match request with
  | .fixedForward _ _ | .fixedInverse _ _ | .encForward _ _ | .encInverse _ _ => BitVec.ofNat 128 value.toNat
  | .hash _ => Security.SimulatorMachine.hashFin.symm value.toFin

/-- The source reply rejects a cutoff result before it exposes an answer. -/
noncomputable def publicReplyValue {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (memory : Memory) : Option request.Answer :=
  if memory.registers 7 = 0#256 then none else some (publicAnswerValue request (memory.registers 8))

/-- The forward source applies its overlay before it exposes the typed answer. -/
noncomputable def publicForwardReplyValue {FixedIndex EncIndex : Type}
    (request : PublicQuery FixedIndex EncIndex) (count : Nat) (memory : Memory) : Option request.Answer :=
  if memory.registers 7 = 0#256 then none
  else some (publicAnswerValue request ((overlayForwardScan count memory).1.registers 8))

/-- Every permutation serializer returns its typed source value. -/
theorem publicBlock_value {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (memory : Memory) (empty : memory.bits 3 = []) :
    answer request ((executeLinear (wordOutput 128) memory).bits 3) =
      some (publicAnswerValue request (memory.registers 8)) := by
  cases request with
  | fixedForward index value => simp [publicAnswerValue, answer, blockOutput_words memory empty]; rfl
  | fixedInverse index value => simp [publicAnswerValue, answer, blockOutput_words memory empty]; rfl
  | encForward index value => simp [publicAnswerValue, answer, blockOutput_words memory empty]; rfl
  | encInverse index value => simp [publicAnswerValue, answer, blockOutput_words memory empty]; rfl
  | hash input => exact (notHash input rfl).elim

/-- The complete forward tail has no parser failure except its explicit cutoff failure. -/
theorem publicForwardTail_answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (count : Nat) (memory : Memory) (empty : memory.bits 3 = []) :
    answer request ((publicForwardTail count memory).1.bits 3) = publicForwardReplyValue request count memory := by
  unfold publicForwardTail publicForwardReplyValue
  split
  · exact empty ▸ publicHandler_abortAnswer request
  · have emptyScan : (overlayForwardScan count memory).1.bits 3 = [] :=
      (congrFun (overlayForward_data count memory).2.1 3).trans empty
    exact publicBlock_value request notHash (overlayForwardScan count memory).1 emptyScan

/-- The complete inverse tail has no parser failure except its explicit cutoff failure. -/
theorem publicInverseTail_answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (notHash : ∀ input, request ≠ .hash input) (memory : Memory) (empty : memory.bits 3 = []) :
    answer request ((publicInverseTail memory).1.bits 3) = publicReplyValue request memory := by
  unfold publicInverseTail publicReplyValue
  split
  · exact empty ▸ publicHandler_abortAnswer request
  · exact publicBlock_value request notHash memory empty

/-- The complete hash tail returns both typed blocks in the protocol order. -/
theorem publicHashTail_answer {FixedIndex EncIndex : Type} (input : BN254.BaseField)
    (memory : Memory) (empty : memory.bits 3 = []) :
    answer (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) input)
      ((publicHashTail memory).1.bits 3) =
        publicReplyValue (PublicQuery.hash (FixedIndex := FixedIndex) (EncIndex := EncIndex) input) memory := by
  unfold publicHashTail publicReplyValue
  split
  · exact empty ▸ publicHandler_abortAnswer _
  · simp only [publicAnswerValue]
    rw [hashOutput_answer (FixedIndex := FixedIndex) (EncIndex := EncIndex) input memory empty]
    rfl

/-- Agreement on supported inputs gives equality of the observed source laws. -/
theorem publicReply_map {Input Output : Type} (source : PMF Input) (left right : Input → Output)
    (same : ∀ value ∈ source.support, left value = right value) : source.map left = source.map right := by
  change source.bind _ = source.bind _
  apply Security.ThreePhase.bind_eq_on_support
  intro value supported
  exact congrArg PMF.pure (same value supported)

/-- The source reply law contains no wire encoding or parser computation. -/
noncomputable def publicHandlerReplies (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : PMF (Option request.Answer) :=
  let initial := publicInputMemory memory request rest
  match request with
  | .fixedForward index value =>
      (storedForwardSamples attempts count initial).map fun result =>
        publicForwardReplyValue (.fixedForward index value) overlayCount result.1
  | .encForward index value =>
      (storedForwardSamples attempts count initial).map fun result =>
        publicForwardReplyValue (.encForward index value) overlayCount result.1
  | .fixedInverse index value =>
      (storedInverseSamples attempts count (publicInversePrepared overlayCount initial)).map fun result =>
        publicReplyValue (.fixedInverse index value) result.1
  | .encInverse index value =>
      (storedInverseSamples attempts count (publicInversePrepared overlayCount initial)).map fun result =>
        publicReplyValue (.encInverse index value) result.1
  | .hash input => (hashHandlerSamples count initial).map fun result => publicReplyValue (.hash input) result.1

/-- The complete source emits exactly its typed replies under the actual answer parser. -/
theorem publicHandlerSamples_answers (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (empty : memory.bits 3 = []) :
    (publicHandlerSamples attempts count overlayCount memory request rest).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      publicHandlerReplies attempts count overlayCount memory request rest := by
  have outputEmpty : (publicInputMemory memory request rest).bits 3 = [] :=
    (publicInputMemory_output memory request rest).trans empty
  cases request with
  | fixedForward index value =>
      simp only [publicHandlerSamples, publicHandlerReplies, publicHandlerKind, publicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicForwardTail_answer (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value) (by intro input; simp) overlayCount result.1
        ((congrFun (storedForwardSamples_bits attempts count _ result.1 result.2 supported) 3).trans outputEmpty)
  | encForward index value =>
      simp only [publicHandlerSamples, publicHandlerReplies, publicHandlerKind, publicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicForwardTail_answer (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value) (by intro input; simp) overlayCount result.1
        ((congrFun (storedForwardSamples_bits attempts count _ result.1 result.2 supported) 3).trans outputEmpty)
  | fixedInverse index value =>
      simp only [publicHandlerSamples, publicHandlerReplies, publicHandlerKind, publicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicInverseTail_answer (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value) (by intro input; simp) result.1
        ((congrFun (storedInverseSamples_bits attempts count _ result.1 result.2 supported) 3).trans
          ((congrFun (publicInversePrepared_bits overlayCount _) 3).trans outputEmpty))
  | encInverse index value =>
      simp only [publicHandlerSamples, publicHandlerReplies, publicHandlerKind, publicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicInverseTail_answer (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value) (by intro input; simp) result.1
        ((congrFun (storedInverseSamples_bits attempts count _ result.1 result.2 supported) 3).trans
          ((congrFun (publicInversePrepared_bits overlayCount _) 3).trans outputEmpty))
  | hash input =>
      simp only [publicHandlerSamples, publicHandlerReplies, publicHandlerKind, publicBranchSamples,
        PMF.map_comp, Function.comp_def, Option.map_some, Option.bind_some]
      apply publicReply_map
      intro result supported
      exact publicHashTail_answer input result.1
        ((congrFun (hashHandlerSamples_bits count _ result.1 result.2 supported) 3).trans outputEmpty)

/-- The actual public machine returns exactly the typed sparse-source reply law. -/
theorem publicHandler_answers [BN254.FieldCertificate] (attempts count overlayCount : Nat) (memory : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : memory.bits 0 = query request ++ rest) (empty : memory.bits 3 = [])
    (attemptFits : attempts < 2 ^ 256) (tableFits : count < 2 ^ 256) (overlayFits : overlayCount < 2 ^ 256)
    (counts : PublicBranchCounts (publicHandlerKind request) attempts count overlayCount
      (publicInputMemory memory request rest)) :
    (run (publicHandler attempts) (publicHandlerReserve attempts count overlayCount memory request rest) ⟨0, memory⟩).map
      (fun result => result.bind fun result => answer request (result.1.memory.bits 3)) =
      publicHandlerReplies attempts count overlayCount memory request rest := by
  rw [publicHandler_run attempts count overlayCount memory request rest wire attemptFits tableFits overlayFits counts]
  exact publicHandlerSamples_answers attempts count overlayCount memory request rest empty

end Kriterion.ArgoMAC.ArithmeticSimulator
