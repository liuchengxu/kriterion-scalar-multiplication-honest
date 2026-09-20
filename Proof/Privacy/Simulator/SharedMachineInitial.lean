import Proof.Privacy.Simulator.SharedMachineLaw
import Proof.Privacy.Distribution.PublicSample

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
open OperationalOracle
namespace SharedSimulatorMachine
noncomputable section

abbrev SharedOracleCoin := PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex

def defaultSharedOracleCoin : SharedOracleCoin :=
  (⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))

/-- The initial sparse state has no stored oracle answers or output swaps. -/
def initial (metadata : Metadata) : SparseState := {
  oracles := (fun _ => ProgrammedPermutation.empty (2 ^ 128), [])
  metadata
}

/-- This function combines the original eager oracle coin with fixed metadata. -/
def withOracles (metadata : Metadata) (coin : SharedOracleCoin) : SharedState where
  fixedOracle := coin.1
  encOracle := coin.2.1
  hashOracle := coin.2.2
  fixedTranscript := metadata.fixedTranscript
  encTranscript := metadata.encTranscript
  hashTranscript := metadata.hashTranscript
  commitments := metadata.commitments
  linking := metadata.linking
  bad := metadata.bad

/-- The permutation conversion is a bijection between the exact finite representations. -/
def blockPermEquiv : Equiv.Perm (Fin (2 ^ 128)) ≃ Equiv.Perm Block where
  toFun := blockPermutation
  invFun π := blockFin.symm.trans (π.trans blockFin)
  left_inv π := by
    apply Equiv.ext
    intro value
    simp only [blockPermutation, Equiv.trans_apply, Equiv.apply_symm_apply]
  right_inv π := by
    apply Equiv.ext
    intro value
    simp only [blockPermutation, Equiv.trans_apply, Equiv.symm_apply_apply]

/-- The finite family and packed hash function are exactly the original oracle coin. -/
def oracleCoinEquiv :
    ((OracleIndex → Equiv.Perm (Fin (2 ^ 128))) × (BaseField → Fin (2 ^ 256))) ≃ SharedOracleCoin where
  toFun sample :=
    (⟨fun index => blockPermEquiv (sample.1 (.inl index))⟩,
      ⟨fun index => blockPermEquiv (sample.1 (.inr index))⟩,
      fun input => hashFin.symm (sample.2 input))
  invFun coin :=
    (fun index => match index with
      | .inl index => blockPermEquiv.symm (coin.1.permutation index)
      | .inr index => blockPermEquiv.symm (coin.2.1.permutation index),
      fun input => hashFin (coin.2.2 input))
  left_inv sample := by
    apply Prod.ext
    · funext index
      cases index <;> simp only [Equiv.symm_apply_apply]
    · funext input
      exact hashFin.apply_symm_apply _
  right_inv coin := by
    rcases coin with ⟨fixed, enc, hash⟩
    dsimp only
    congr 2
    funext input
    exact hashFin.symm_apply_apply _

/-- The decoded completion depends only on the visible oracle family and hash function. -/
theorem decode_as_oracleCoin (metadata : Metadata) (complete : OracleCompletion) :
    decode metadata complete = withOracles metadata
      (oracleCoinEquiv ((fun index => (complete.1 index).1.denote (complete.1 index).2), complete.2.2)) := rfl

/-- The empty sparse completion has the exact uniform oracle-coin distribution. -/
theorem initial_completion (metadata : Metadata) :
    let : Nonempty SharedOracleCoin := ⟨defaultSharedOracleCoin⟩
    completion (initial metadata) =
      (PMF.uniformOfFintype SharedOracleCoin).map (withOracles metadata) := by
  let : Nonempty SharedOracleCoin := ⟨defaultSharedOracleCoin⟩
  let family : PMF (OracleIndex → Equiv.Perm (Fin (2 ^ 128))) := PMF.uniformOfFintype _
  let hash : PMF (BaseField → Fin (2 ^ 256)) := PMF.uniformOfFintype _
  have familyLaw := family_initial_denote (Index := OracleIndex) (2 ^ 128)
  have hashLaw := congrArg
    (fun distribution : PMF (HashTable BaseField (2 ^ 256) × (BaseField → Fin (2 ^ 256))) =>
      distribution.map Prod.snd)
    (hash_initial (Key := BaseField) (size := 2 ^ 256) (by norm_num))
  simp only [PMF.map_comp, Function.comp_def] at hashLaw
  have combined := congrArg
    (fun distribution : PMF (OracleIndex → Equiv.Perm (Fin (2 ^ 128))) =>
      distribution.bind (fun permutations => hash.map (fun hash => (permutations, hash)))) familyLaw
  simp only [PMF.bind_map, Function.comp_def] at combined
  have before : completion (initial metadata) =
      (family.bind (fun permutations => hash.map (fun hash => (permutations, hash)))).map
        (fun sample => withOracles metadata (oracleCoinEquiv sample)) := by
    unfold completion initial lowerCompletion productKernel
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, decode_as_oracleCoin]
    have mapped := congrArg
      (fun distribution : PMF ((OracleIndex → Equiv.Perm (Fin (2 ^ 128))) × (BaseField → Fin (2 ^ 256))) =>
        distribution.map (fun sample => withOracles metadata (oracleCoinEquiv sample))) combined
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at mapped
    apply Eq.trans ?_ mapped
    congr 1
    funext completeFamily
    have mappedHash := congrArg
      (fun distribution : PMF (BaseField → Fin (2 ^ 256)) => distribution.map
        (fun hash => withOracles metadata
          (oracleCoinEquiv ((fun index => (completeFamily index).1.denote (completeFamily index).2), hash)))) hashLaw
    simpa only [PMF.map_comp, Function.comp_def, hash] using mappedHash
  rw [before, uniform_product]
  have law := congrArg (fun distribution : PMF SharedOracleCoin =>
    distribution.map (withOracles metadata)) (uniform_equiv oracleCoinEquiv)
  simpa only [PMF.map_comp, Function.comp_def] using law

end
end SharedSimulatorMachine
end Kriterion.ArgoMAC.Security
