import Proof.Privacy.Source.SharedFullSourceTape
import Proof.Privacy.Source.RetainedSourceTransport
import Proof.Privacy.Simulator.SharedGameDistribution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section

/-- This source separates retained rows from the actual shared offline coin. -/
abbrev SharedPrivateSource [FieldCertificate] [GroupCertificate] :=
  RetainedRowCoin × (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) × SimulatorSampling.OfflineCoin

/-- The source split preserves exactly three fixed permutations in every public bucket. -/
def sharedRetainedSimulatorSourceEquiv [FieldCertificate] [GroupCertificate] :
    (SharedMaskRetainedTape × PublicSample) ≃ SharedPrivateSource where
  toFun source :=
    ((source.1.val.1, source.1.val.2.1, source.1.val.2.2.1.2),
      (Shared.restrictOracle source.1.val.2.2.2.fixedKeyOracle,
        source.1.val.2.2.2.encPRFOracle, source.1.val.2.2.2.hashOracle),
      source.2, source.1.val.2.2.2.inputMacKey, source.1.val.2.2.1.1)
  invFun source :=
    (⟨(source.1.1, source.1.2.1, (source.2.2.2.2, source.1.2.2),
      ⟨Shared.expandOracle source.2.1.1, source.2.2.2.1, source.2.1.2.1, source.2.1.2.2⟩), by
        simp only [Shared.restrict_expand]⟩, source.2.2.1)
  left_inv source := by
    rcases source with ⟨⟨⟨offsets, rhos, ⟨bridge, mask⟩, ⟨fixed, key, enc, hash⟩⟩, shared⟩, sample⟩
    apply Prod.ext
    · apply Subtype.ext
      change (offsets, rhos, (bridge, mask),
        (⟨Shared.expandOracle (Shared.restrictOracle fixed), key, enc, hash⟩ : GarblingOracleData)) = _
      change Shared.expandOracle (Shared.restrictOracle fixed) = fixed at shared
      rw [shared]
    · rfl
  right_inv source := by
    rcases source with ⟨⟨offsets, rhos, mask⟩, ⟨fixed, enc, hash⟩, sample, key, bridge⟩
    change ((offsets, rhos, mask),
      (Shared.restrictOracle (Shared.expandOracle fixed), enc, hash), sample, key, bridge) = _
    rw [Shared.restrict_expand]

/-- The source split has the exact uniform law on the constrained shared tape. -/
theorem map_uniform_sharedRetainedSimulatorSource [FieldCertificate] [GroupCertificate]
    [Fintype (SharedMaskRetainedTape × PublicSample)] [Nonempty (SharedMaskRetainedTape × PublicSample)]
    [Fintype SharedPrivateSource] [Nonempty SharedPrivateSource] :
    (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).map sharedRetainedSimulatorSourceEquiv =
      PMF.uniformOfFintype SharedPrivateSource :=
  map_uniformOfFintype_equivBetween sharedRetainedSimulatorSourceEquiv

/-- The retained tape gives the exact actual shared simulator state. -/
def sharedSourceInitialState [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape) (sample : PublicSample) : Shared.Simulator.State :=
  Shared.Simulator.initialState (sample, retained.val.2.2.2.inputMacKey, retained.val.2.2.1.1)
    (Shared.restrictOracle retained.val.2.2.2.fixedKeyOracle,
      retained.val.2.2.2.encPRFOracle, retained.val.2.2.2.hashOracle)

/-- The exact source equivalence preserves the whole private shared state. -/
theorem sharedRetainedSimulatorSource_state [FieldCertificate] [GroupCertificate]
    (retained : SharedMaskRetainedTape) (sample : PublicSample) :
    let split := sharedRetainedSimulatorSourceEquiv (retained, sample)
    sharedSourceInitialState retained sample = Shared.Simulator.initialState split.2.2 split.2.1 := rfl

attribute [local instance] publicInputMacKeyFintype
local instance sharedSourceInputKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩
local instance sharedSourceSampleNonempty : Nonempty PublicSample := ⟨defaultSimulatorCoin.tableSample⟩
local instance sharedSourceOracleNonempty : Nonempty (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) :=
  ⟨(⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))⟩

/-- The independent retained row coins disappear from the exact actual shared offline tape. -/
theorem sharedRetainedSource_initialState_law [FieldCertificate] [GroupCertificate]
    [Fintype SharedMaskRetainedTape] [Nonempty SharedMaskRetainedTape]
    [Fintype RetainedRowCoin] [Nonempty RetainedRowCoin]
    (parameter : Nat) (topology : Garbling.Topology) :
    (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).map
      (fun source => sharedSourceInitialState source.1 source.2) = Shared.Simulator.tape parameter topology := by
  have offline : SimulatorSampling.offline.law = PMF.uniformOfFintype SimulatorSampling.OfflineCoin :=
    SimulatorSampling.offline_uniform
  have marginal := congrArg (fun distribution : PMF SharedPrivateSource => distribution.map Prod.snd)
    map_uniform_sharedRetainedSimulatorSource
  rw [PMF.map_comp, map_uniform_prod_snd] at marginal
  have stateLaw := congrArg (fun distribution => distribution.map
    (fun pair : (PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) × SimulatorSampling.OfflineCoin =>
      Shared.Simulator.initialState pair.2 pair.1)) marginal
  rw [PMF.map_comp] at stateLaw
  change (PMF.uniformOfFintype (SharedMaskRetainedTape × PublicSample)).map
    (fun source => sharedSourceInitialState source.1 source.2) =
    (PMF.uniformOfFintype ((PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex) × SimulatorSampling.OfflineCoin)).map
      (fun pair => Shared.Simulator.initialState pair.2 pair.1) at stateLaw
  rw [stateLaw, uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  simp only [PMF.map]
  rw [PMF.bind_comm]
  simp only [Shared.Simulator.tape, offline, PMF.map, Function.comp_def]

end
end Kriterion.ArgoMAC.Security
