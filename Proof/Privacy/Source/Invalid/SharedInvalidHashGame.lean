import Proof.Privacy.Source.Invalid.SharedInvalidHashBound
import Proof.Privacy.Source.SharedGateSourceSupport

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- This shared continuation starts after the selected curve program. -/
def sharedCurveSourceSuffix {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (data : GarblingOracleData) (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (oracle : Shared.Simulator.OracleState) : PMF (SharedFullGateTranscript adversary.State) :=
  (runOracleProgramWithTranscript idealOracleHandler
    (adversary.decide parameter table (sourceInputLabels data selected.1) auxiliary selected.2.1) oracle).map fun decided =>
      (table, (selected.1, selected.2.1), selected.2.2.2, sourceInputLabels data selected.1, decided.1, decided.2.2)

/-- The shared prefix obeys the first adaptive query budget. -/
theorem sharedGateSourceChoose_length_le {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table) (data : GarblingOracleData)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (member : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary table data).support) :
    selected.2.2.2.length ≤ adversary.firstQueryBudget parameter := by
  simp only [sharedGateSourceChoose, PMF.mem_support_map_iff] at member
  obtain ⟨result, supported, rfl⟩ := member
  exact runOracleProgramWithTranscript_length_le idealOracleHandler _ _ result supported

/-- The actual shared suffix and its supported prefix obey the complete query budget. -/
theorem sharedCurveSourceSuffix_length_le {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (data : GarblingOracleData) (table : Pipeline.Table)
    (selected : AffineInput × (adversary.State × Shared.Simulator.OracleState × List (Sigma sharedRealOracleSpec.Answer)))
    (chosen : selected ∈ (sharedGateSourceChoose adversary parameter auxiliary table data).support)
    (oracle : Shared.Simulator.OracleState) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ (sharedCurveSourceSuffix adversary parameter auxiliary data table selected oracle).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  have bound := sharedGateSourceChoose_length_le adversary parameter auxiliary table data selected chosen
  simp only [sharedCurveSourceSuffix, PMF.mem_support_map_iff] at member
  obtain ⟨result, supported, rfl⟩ := member
  exact (List.length_append ..).trans_le
    (Nat.add_le_add bound (runOracleProgramWithTranscript_length_le idealOracleHandler _ _ result supported))

/-- The actual shared invalid game pays one field-sized exception per query and one for the mask. -/
theorem sharedInvalidHashGame_mass_le [FieldCertificate] {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (data : GarblingOracleData)
    (rows : FieldMacToECMac.Rows) (sparse : ∀ row, FieldMacToECMac.SparseRow (rows.get row)) :
    (((PMF.uniformOfFintype BaseField).bind fun bridge =>
      (PMF.uniformOfFintype NonZeroBase).bind fun mask =>
        sharedInvalidCurveMaskRun bridge mask.value rows data.inputMacKey (fun selected => selected.2.1)
          (fun table => sharedGateSourceChoose adversary parameter auxiliary table data)
          (fun table selected bridge oracle =>
            (sharedCurveSourceSuffix adversary parameter auxiliary data table selected oracle).map (Prod.mk bridge))).toOuterMeasure
              (sharedInvalidHashEvent (fun output => output.2.2.1 ++ output.2.2.2.2.2))).toReal ≤
      ((adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter : Nat) + 1 : ℝ) / baseFieldModulus := by
  exact sharedInvalidMaskedHash_mass_le rows sparse data.inputMacKey (fun selected => selected.2.1)
    (fun table => sharedGateSourceChoose adversary parameter auxiliary table data)
    (sharedCurveSourceSuffix adversary parameter auxiliary data)
    (fun output => output.2.2.1 ++ output.2.2.2.2.2) _
    (fun table selected chosen oracle output member =>
      sharedCurveSourceSuffix_length_le adversary parameter auxiliary data table selected chosen oracle output member)

end
end Kriterion.ArgoMAC.Security
