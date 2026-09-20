import Proof.Privacy.Source.SharedGateSourceSupport
import Proof.Privacy.Source.SharedNonfixedSourceMass

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- The shared nonfixed transcript determines every recorded encryption answer. -/
theorem sharedNonfixed_encReference
    (oracle : PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex)
    (history : List (Sigma sharedRealOracleSpec.Answer))
    (compatible : SharedNonFixedTranscriptCompatible oracle history) :
    PermutationTranscriptMatches oracle.2.1 (encOracleTranscriptRecords (sharedLegacyTranscript history)) := by
  have matchesCons (record : PermutationRecord EncPRF.PermutationIndex Block) (tail) :
      PermutationTranscriptMatches oracle.2.1 (record :: tail) ↔
        oracle.2.1.permutation record.index record.domain = record.range ∧
          PermutationTranscriptMatches oracle.2.1 tail := by
    simp [PermutationTranscriptMatches]
  induction history with
  | nil => simp [sharedLegacyTranscript, encOracleTranscriptRecords, PermutationTranscriptMatches]
  | cons entry tail ih =>
      rcases entry with ⟨query, answer⟩
      cases query <;>
        simp only [SharedNonFixedTranscriptCompatible] at compatible <;>
        simp only [sharedLegacyTranscript, List.map_cons, sharedLegacyEntry, encOracleTranscriptRecords]
      · exact ih compatible
      · exact ih compatible
      · exact matchesCons _ _ |>.mpr ⟨compatible.1, ih compatible.2⟩
      · apply (matchesCons _ _).mpr
        exact ⟨by rw [← compatible.1, Equiv.apply_symm_apply], ih compatible.2⟩
      · exact ih compatible.2

/-- A supported source output supplies both phase references and the complete encryption reference. -/
theorem sharedGateSourcePhases_references {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table) (data : GarblingOracleData)
    (view : AffineInput → SelectedGateView) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data).support) :
    output.2.2.2.1.input = BitInput.ofAffine output.2.1.1 ∧
      data.inputMacKey.encodeAffine output.2.1.1 = output.2.2.2.1.inputMac ∧
      OracleTranscriptCompatible idealOracleHandler (sharedInitialSourceOracle data) output.2.2.1 ∧
      (∃ final : Shared.Simulator.OracleState,
        OracleTranscriptCompatible idealOracleHandler final output.2.2.2.2.2) ∧
      PermutationTranscriptMatches data.encPRFOracle
        (encOracleTranscriptRecords (sharedLegacyTranscript (output.2.2.1 ++ output.2.2.2.2.2))) := by
  obtain ⟨selected, first, last⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  have firstCompatible := (sharedGateSourceChoose_final adversary parameter auxiliary table data selected first).2
  have nonfixed := sharedGateSourceObserve_nonfixed adversary parameter auxiliary table data selected first
    (view selected.1) output last
  have enc := sharedNonfixed_encReference _ _ nonfixed
  simp only [sharedGateSourceObserve, PMF.mem_support_map_iff] at last
  obtain ⟨result, supported, rfl⟩ := last
  exact ⟨rfl, rfl, firstCompatible,
    ⟨_, runOracleProgramWithTranscript_compatible idealOracleHandler _ _ result supported⟩, enc⟩

end
end Kriterion.ArgoMAC.Security
