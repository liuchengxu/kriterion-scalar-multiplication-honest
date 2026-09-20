import Proof.Privacy.Simulator.Arithmetic.RecordedPublicJoint

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle
open Security.SharedSimulatorMachine GarbledCircuit.SimulatorProtocol
noncomputable section
set_option maxRecDepth 4096
attribute [local irreducible] sharedPhysicalIndex

/-- The joint public source has the complete shared cutoff marginal. -/
theorem recordedPublicJoint_source [BN254.FieldCertificate] (attempts : Nat) (memory : Memory)
    (state : SharedOracleSource) (request : SharedQuery) (rest : List Bool)
    (represented : OracleFamilyMemory memory.ram state.family) (capacity : OracleFamilyFits state.family)
    (room : ∀ oracle, 2 * ((state.family.permutations oracle).base.used + 1) ≤ 2 ^ 110)
    (empty : memory.bits 3 = [])
    (stable : RecordedPublicReplyStable (publicHandlerKind request) attempts
      (publicSourceCount state request) (publicSourceOverlay state request)
      (recordedPublicInputMemory memory request rest)) :
    (recordedPublicJoint attempts memory state request rest).map Prod.snd =
      sharedSourceCutoff attempts (.inr request) state := by
  apply recordedPublicJoint_source_of_replies
  rw [recordedPublicHandlerSamples_answers _ _ _ _ _ _ empty stable]
  have stored := recordedPublicInputMemory_family memory request rest state.family represented capacity
  have values := recordedPublicInputMemory_values memory request rest
  cases request with
  | fixedForward index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have indexWord : (recordedPublicInputMemory memory (.fixedForward index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : (recordedPublicInputMemory memory (.fixedForward index value) rest).registers 8 =
          BitVec.ofNat 256 (blockFin value).val := values.1
      have law := programmedForwardReplies_typed (PublicQuery.fixedForward (EncIndex := EncPRF.PermutationIndex) index value) attempts
        (recordedPublicInputMemory memory (.fixedForward index value) rest) oracle.castSucc
        (state.family.permutations oracle) (blockFin value) (stored.permutations oracle)
        indexWord operand (room oracle) (capacity.overlay oracle)
      simp only [recordedPublicHandlerReplies, publicSourceCount, publicSourceOverlay, publicSourceOracle,
        sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def] at law ⊢
      refine law.trans ?_
      congr 1
      funext result
      cases result with
      | none => rfl
      | some result =>
          dsimp only [Option.map]
          apply congrArg some
          apply BitVec.eq_of_toNat_eq
          have bound : result.1.val < 2 ^ 256 := lt_trans result.1.isLt (by decide)
          simp only [publicAnswerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
          exact Nat.mod_eq_of_lt result.1.isLt
  | encForward index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have indexWord : (recordedPublicInputMemory memory (.encForward index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : (recordedPublicInputMemory memory (.encForward index value) rest).registers 8 =
          BitVec.ofNat 256 (blockFin value).val := values.1
      have law := programmedForwardReplies_typed (PublicQuery.encForward (FixedIndex := Shared.FixedKeyIndex) index value) attempts
        (recordedPublicInputMemory memory (.encForward index value) rest) oracle.castSucc
        (state.family.permutations oracle) (blockFin value) (stored.permutations oracle)
        indexWord operand (room oracle) (capacity.overlay oracle)
      simp only [recordedPublicHandlerReplies, publicSourceCount, publicSourceOverlay, publicSourceOracle,
        sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def] at law ⊢
      refine law.trans ?_
      congr 1
      funext result
      cases result with
      | none => rfl
      | some result =>
          dsimp only [Option.map]
          apply congrArg some
          apply BitVec.eq_of_toNat_eq
          have bound : result.1.val < 2 ^ 256 := lt_trans result.1.isLt (by decide)
          simp only [publicAnswerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
          exact Nat.mod_eq_of_lt result.1.isLt
  | fixedInverse index value =>
      let oracle := sharedPhysicalIndex (.inl index)
      have indexWord : (recordedPublicInputMemory memory (.fixedInverse index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : (recordedPublicInputMemory memory (.fixedInverse index value) rest).registers 8 =
          BitVec.ofNat 256 (blockFin value).val := values.1
      have law := programmedInverseReplies_typed (PublicQuery.fixedInverse (EncIndex := EncPRF.PermutationIndex) index value) attempts
        (recordedPublicInputMemory memory (.fixedInverse index value) rest) oracle.castSucc
        (state.family.permutations oracle) (blockFin value) (stored.permutations oracle)
        indexWord operand ((Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (room oracle)) (capacity.overlay oracle)
      simp only [recordedPublicHandlerReplies, publicSourceCount, publicSourceOverlay, publicSourceOracle,
        sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def] at law ⊢
      refine law.trans ?_
      congr 1
      funext result
      cases result with
      | none => rfl
      | some result =>
          dsimp only [Option.map]
          apply congrArg some
          apply BitVec.eq_of_toNat_eq
          have bound : result.1.val < 2 ^ 256 := lt_trans result.1.isLt (by decide)
          simp only [publicAnswerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
          exact Nat.mod_eq_of_lt result.1.isLt
  | encInverse index value =>
      let oracle := sharedPhysicalIndex (.inr index)
      have indexWord : (recordedPublicInputMemory memory (.encInverse index value) rest).registers 9 =
          BitVec.ofNat 256 oracle.val := by
        rw [values.2.1]
        simp [queryOperands, oracle, sharedPhysicalIndex_fixed, sharedPhysicalIndex_enc, Nat.add_comm]
      have operand : (recordedPublicInputMemory memory (.encInverse index value) rest).registers 8 =
          BitVec.ofNat 256 (blockFin value).val := values.1
      have law := programmedInverseReplies_typed (PublicQuery.encInverse (FixedIndex := Shared.FixedKeyIndex) index value) attempts
        (recordedPublicInputMemory memory (.encInverse index value) rest) oracle.castSucc
        (state.family.permutations oracle) (blockFin value) (stored.permutations oracle)
        indexWord operand ((Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (room oracle)) (capacity.overlay oracle)
      simp only [recordedPublicHandlerReplies, publicSourceCount, publicSourceOverlay, publicSourceOracle,
        sharedSourceCutoff, sharedSourceExactQuery, Bool.false_eq_true, if_false,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, familyDraw, lowerAnswer, namedAnswer,
        drawCutoffLaw_map, PMF.map_comp, Option.map_map, Function.comp_def] at law ⊢
      refine law.trans ?_
      congr 1
      funext result
      cases result with
      | none => rfl
      | some result =>
          dsimp only [Option.map]
          apply congrArg some
          apply BitVec.eq_of_toNat_eq
          have bound : result.1.val < 2 ^ 256 := lt_trans result.1.isLt (by decide)
          simp only [publicAnswerValue, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
          exact Nat.mod_eq_of_lt result.1.isLt
  | hash key =>
      have law := hashReplies_typed state.family.hash key
        (recordedPublicInputMemory memory (.hash key) rest) 15748 stored.hash values.2.1 values.1
        (by have := capacity.hash; omega)
      simp only [recordedPublicHandlerReplies, publicSourceCount, publicSourceOverlay,
        sharedSourceCutoff, sharedSourceExactQuery, if_true, sharedCombinedSourceHandler,
        sharedCombinedSourceDraw, sharedExternalSourceDraw, sharedInternalSourceDraw, lowerRequest,
        physicalRequest, oracleFamilyDraw, lowerAnswer, namedAnswer, Draw.map_distribution,
        PMF.map_comp, Function.comp_def, Option.map_some] at law ⊢
      refine law.trans ?_
      congr 1

end
end Kriterion.ArgoMAC.ArithmeticSimulator
