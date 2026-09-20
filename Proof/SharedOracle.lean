import Construction.SharedGarbling
import Proof.Privacy.Distribution.Distribution

namespace Kriterion.ArgoMAC.Shared
open BN254 Cryptography

noncomputable instance : Fintype Randomness := Fintype.ofFinite _

/-- The tape receives three independent fixed permutations per bucket.
The encryption permutations and the hash oracle remain independent. -/
theorem oracleUniform (witness : Randomness) :
    Assumptions.StandardAssumptions FixedKeyIndex EncPRF.PermutationIndex
      Randomness witness evaluationOracle := by
  classical
  let assemble (tape : Randomness) (oracle : PublicOracle FixedKeyIndex EncPRF.PermutationIndex) :
      Randomness := ⟨{tape.val with
        fixedKeyOracle := expandOracle oracle.1
        encPRFOracle := oracle.2.1
        hashOracle := oracle.2.2}, by simp⟩
  let normalize (tape : Randomness) : Randomness :=
    assemble tape (⟨fun _ => Equiv.refl Block⟩, ⟨fun _ => Equiv.refl Block⟩, fun _ => (0, 0))
  let Rest := {tape : Randomness // normalize tape = tape}
  let : Fintype Rest := Fintype.ofFinite Rest
  let : Nonempty Rest := ⟨⟨normalize witness, rfl⟩⟩
  let : Nonempty Randomness := ⟨witness⟩
  let split : Randomness ≃ (PublicOracle FixedKeyIndex EncPRF.PermutationIndex) × Rest := {
    toFun := fun tape => (evaluationOracle tape, ⟨normalize tape, rfl⟩)
    invFun := fun pair => assemble pair.2.val pair.1
    left_inv := fun tape => by
      apply Subtype.ext
      dsimp only [assemble, normalize, evaluationOracle]
      rw [tape.property]
    right_inv := fun pair => by
      rcases pair with ⟨⟨fixed, enc, hash⟩, ⟨tape, equal⟩⟩
      apply Prod.ext
      · simp only [evaluationOracle, assemble, restrict_expand]
      · apply Subtype.ext
        exact equal
  }
  rw [Assumptions.StandardAssumptions, uniformTape_eq]
  have mapped := congrArg (PMF.map Prod.fst) (Security.uniform_map_equiv split)
  rw [Security.uniform_map_fst] at mapped
  simpa only [PMF.map_comp, Function.comp_def, split, Equiv.coe_fn_mk] using mapped

end Kriterion.ArgoMAC.Shared
