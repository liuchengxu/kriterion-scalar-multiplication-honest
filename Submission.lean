import Solution
import Construction
import Construction.OraclePrograms
import Proof
import Proof.Privacy.Simulator.Arithmetic.CompiledAdaptiveGame

-- The transmitted encoding is a 91-row structure whose `encode` walks the whole
-- table. Unfolding it during elaboration is never needed: its length is proved
-- where it is defined. `irreducible` binds the elaborator only; the kernel still
-- checks every term this file produces.
attribute [local irreducible] Kriterion.ArgoMAC.Wire.encoding

set_option maxRecDepth 4096

-- The kernel re-checks the whole bundle, and the expensive step in it is a
-- type-level comparison around `scheme`/`encoding`: the later fields of
-- `Solution` apply `encoding` to the value `scheme` returns, so the kernel must
-- see through `packedProgramCircuit` to compare the two forms, once per mention.
-- That cost is additive across the fields. `irreducible` above is already in
-- force and does not help, because it binds the elaborator and not the kernel.
-- Measured on the revision-15 port of this same bundle: `type checking took
-- 489s` at 4,000,000 heartbeats, while the 200,000 default stops it after about
-- 34 s. This file is built from scratch by the platform, so the budget has to
-- live here.
set_option maxHeartbeats 4000000

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
  scheme := fun field group => @Shared.packedProgramCircuit field group
  ciphertextSize := fun field group => @Shared.packedProgramCiphertextSize field group
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
