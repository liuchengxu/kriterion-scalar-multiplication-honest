import Solution
import Construction
import Construction.OraclePrograms
import Proof
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptiveGame

-- The kernel re-checks the whole bundle, and the expensive step in it is a
-- type-level comparison around `scheme`/`encoding`: the later fields of
-- `Solution` apply `encoding` to the value `scheme` returns, so the kernel must
-- see through `scheme` to compare the two forms, once per field. Any comparison
-- that is not syntactic ends in `Wire.encoding`, whose `encode` walks 91 rows of
-- 8,065-byte adaptors, and that reduction is what the build pays for.
--
-- Both forms are therefore pinned to the challenge's own terms instead of
-- raising a budget:
--   * `scheme` is `Shared.packedProgramScheme`, a constant declared with the
--     challenge's `scheme` type, rather than a lambda. A lambda leaves a beta
--     redex in the type of every later field, which is not syntactic.
--   * `ciphertextSize` is `Shared.packedProgramSchemeCiphertextSize`, stated
--     over that same constant.
-- With those two this file checks in milliseconds (`type checking 1.44ms` over
-- the whole file) at the DEFAULT heartbeat budget, so it carries no `set_option`
-- at all. The revision-15 port of the same bundle needed `maxHeartbeats
-- 4000000` and 8m12s to check the declaration below; the 200,000 default cut it
-- off after about 34 s.

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The submission uses 91 digits and three shared permutation slots. -/
def solution : Kriterion.Solution := {
  FixedIndex := Shared.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Shared.PrivateCoins
  randomnessFinite := inferInstance
  randomness := Shared.privateCoins (Shared.Randomness.ofLegacy (Seed.randomness 0))
  Public := Pipeline.PackedTable
  EncodingKey := InputMacKey
  encoding := Wire.encoding
  ciphertextBytes := 8887896
  garbleQueries := Shared.garbleQueries
  evaluateQueries := Shared.evaluateQueries
  garbleProgram := fun field group => @Shared.packedGarbleProgram field group
  evaluateProgram := fun field group => @Shared.packedEvaluateProgram field group
  garbleProgramCorrect := fun field group => @Shared.packedGarbleProgram_correct field group
  evaluateProgramCorrect := fun field group => @Shared.packedEvaluateProgram_correct field group
  scheme := Shared.packedProgramScheme
  ciphertextSize := Shared.packedProgramSchemeCiphertextSize
  lamportCompatible := fun field group => @Shared.packedProgramLamportCompatible field group
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @Shared.packedProgramPerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    let := field
    let := group
    let : Fintype Shared.PrivateCoins := Fintype.ofFinite _
    have fixed : (Fintype.ofFinite Shared.FixedKeyIndex) =
        (inferInstance : Fintype Shared.FixedKeyIndex) := Subsingleton.elim _ _
    have enc : (Fintype.ofFinite EncPRF.PermutationIndex) =
        (inferInstance : Fintype EncPRF.PermutationIndex) := Subsingleton.elim _ _
    have fixedEq : (Classical.decEq Shared.FixedKeyIndex) =
        (inferInstance : DecidableEq Shared.FixedKeyIndex) := Subsingleton.elim _ _
    have encEq : (Classical.decEq EncPRF.PermutationIndex) =
        (inferInstance : DecidableEq EncPRF.PermutationIndex) := Subsingleton.elim _ _
    rw [fixed, enc, fixedEq, encEq]
    exact ArithmeticSimulator.lazyCompiledAdaptivePrivacy
      (Shared.Randomness.ofLegacy (Seed.randomness 0))
}

end Submission
