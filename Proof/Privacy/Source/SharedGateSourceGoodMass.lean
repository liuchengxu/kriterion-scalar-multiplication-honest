import Proof.Privacy.Source.SharedGateSourceSupport
import Proof.Privacy.Source.PrefixGoodExpansion

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The shared continuation fixes every guard that depends on its input and prefix. -/
theorem sharedGateSourceGood_mass {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (bad : AffineInput → List (Sigma sharedRealOracleSpec.Answer) → Prop)
    (output : SharedFullGateTranscript adversary.State) :
    sourceGoodMass (sharedGateSourceChoose adversary parameter auxiliary table data)
      (fun selected => sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data)
      {selected | bad selected.1 selected.2.2.2} output =
    if bad output.2.1.1 output.2.2.1 then 0 else
      ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
        sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data) output := by
  apply sourceGoodMass_guard_eq
  intro selected member
  have tag := sharedGateSourceObserve_tag adversary parameter auxiliary table data selected
    (view selected.1) output member
  have input := congrArg (fun value => value.2.1.1) tag
  have history := congrArg (fun value => value.2.2.1) tag
  dsimp only at input history
  rw [input, history]
  rfl

/-- An incompatible nonfixed transcript has zero shared source mass. -/
theorem sharedGateSourcePhases_nonfixed_zero {Aux : Type}
    (adversary : GarbledCircuit.AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.Table
      Garbling.Labels Aux) (parameter : Nat) (auxiliary : Aux)
    (table : Pipeline.Table) (data : GarblingOracleData) (view : AffineInput → SelectedGateView)
    (output : SharedFullGateTranscript adversary.State)
    (incompatible : ¬ SharedNonFixedTranscriptCompatible
      (Shared.restrictOracle data.fixedKeyOracle, data.encPRFOracle, data.hashOracle)
      (output.2.2.1 ++ output.2.2.2.2.2)) :
    ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data) output = 0 := by
  by_contra nonzero
  have supported : output ∈ ((sharedGateSourceChoose adversary parameter auxiliary table data).bind fun selected =>
      sharedGateSourceObserve adversary parameter auxiliary table selected (view selected.1) data).support := nonzero
  obtain ⟨selected, first, last⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  exact incompatible (sharedGateSourceObserve_nonfixed adversary parameter auxiliary table data selected
    first (view selected.1) output last)

end
end Kriterion.ArgoMAC.Security
