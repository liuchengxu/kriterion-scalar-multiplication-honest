import Proof.Privacy.Source.Invalid.SharedInvalidHashGame

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- Both actual shared source phases obey the complete adversary query budget. -/
theorem sharedGateSourcePhases_length_le {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table Garbling.Labels Aux)
    (parameter : Nat) (auxiliary : Aux) (table : Pipeline.Table) (data : GarblingOracleData)
    (view : AffineInput → SelectedGateView) (output : SharedFullGateTranscript adversary.State)
    (member : output ∈ ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data).support) :
    (output.2.2.1 ++ output.2.2.2.2.2).length ≤
      adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter := by
  obtain ⟨selected, first, last⟩ := (PMF.mem_support_bind_iff _ _ _).mp member
  exact sharedCurveSourceSuffix_length_le adversary parameter auxiliary data table selected first _ output last

end
end Kriterion.ArgoMAC.Security
