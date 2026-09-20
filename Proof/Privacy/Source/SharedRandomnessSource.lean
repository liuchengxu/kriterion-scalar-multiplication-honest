import Proof.SharedOracle
import Proof.Privacy.Source.ActualKeyMass
import Solution

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography
noncomputable section
local instance sharedRandomSourceInputKeyFintype : Fintype InputMacKey := publicInputMacKeyFintype
local instance sharedRandomSourceInputKeyNonempty : Nonempty InputMacKey := ⟨defaultSimulatorCoin.inputKey⟩

/-- The shared tape separates its three-slot oracle, input key, and remaining data. -/
def sharedGarblingOracleKeyEquiv : Shared.Randomness ≃
    ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey) × GarblingSourceRest where
  toFun randomness := ((Shared.restrictOracle randomness.val.fixedKeyOracle, randomness.val.inputMacKey),
    (garblingOracleKeyEquiv randomness.val).2)
  invFun sample := ⟨garblingOracleKeyEquiv.symm
    ((Shared.expandOracle sample.1.1, sample.1.2), sample.2), by
      change Shared.expandOracle (Shared.restrictOracle (Shared.expandOracle sample.1.1)) =
        Shared.expandOracle sample.1.1
      rw [Shared.restrict_expand]⟩
  left_inv randomness := by
    apply Subtype.ext
    apply garblingOracleKeyEquiv.injective
    change ((Shared.expandOracle (Shared.restrictOracle randomness.val.fixedKeyOracle),
      randomness.val.inputMacKey), (garblingOracleKeyEquiv randomness.val).2) =
        garblingOracleKeyEquiv randomness.val
    rw [randomness.property]
    rfl
  right_inv sample := by
    rcases sample with ⟨⟨oracle, key⟩, rest⟩
    change ((Shared.restrictOracle (Shared.expandOracle oracle), key), rest) = ((oracle, key), rest)
    rw [Shared.restrict_expand]

/-- The actual shared uniform tape samples the remaining data before its oracle and key. -/
theorem sharedRandomTape_oracleKey [Fintype Block] (witness : Shared.Randomness) (parameter : Nat) :
    letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
    uniformRandomTape Shared.Randomness witness parameter =
      (PMF.uniformOfFintype GarblingSourceRest).bind fun rest =>
        (PMF.uniformOfFintype ((PermutationOracle Shared.FixedKeyIndex Block) × InputMacKey)).map
          (fun sample => sharedGarblingOracleKeyEquiv.symm (sample, rest)) := by
  letI : Nonempty GarblingSourceRest := ⟨(sharedGarblingOracleKeyEquiv witness).2⟩
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  rw [uniformRandomTape, uniformTape_eq]
  rw [← map_uniformOfFintype_equivBetween sharedGarblingOracleKeyEquiv.symm,
    uniform_prod_eq_bind, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]

end
end Kriterion.ArgoMAC.Security
