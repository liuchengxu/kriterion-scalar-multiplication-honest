import Solution
import Construction
import Proof

-- The transmitted encoding is a 91-row structure whose `encode` walks the whole
-- table. Unfolding it during elaboration is never needed: its length is proved
-- where it is defined. `irreducible` binds the elaborator only; the kernel still
-- checks every term this file produces.
attribute [local irreducible] Kriterion.ArgoMAC.Wire.encoding

set_option maxRecDepth 4096

-- The kernel re-checks the whole bundle, and the expensive step in it is a
-- type-level comparison around `scheme`/`encoding`: the later fields of
-- `Solution` apply `encoding` to the value `scheme` returns, so the kernel must
-- see through `packedCircuit` to compare the two forms, once per mention. That
-- cost is additive across the fields and is nobody's `rfl`: stubbing all nine
-- proof fields in a scratch copy still needs more than 100,000 heartbeats, while
-- stubbing `scheme` as well drops the check to 2 s. `irreducible` above is
-- already in force and does not help, because it binds the elaborator and not
-- the kernel. Measured: `type checking took 489s` at 4,000,000 heartbeats; the
-- 200,000 default stops it after about 34 s. This file is built from scratch by
-- the platform, so the budget has to live here.
set_option maxHeartbeats 4000000

namespace Submission
open Kriterion Kriterion.BN254 Kriterion.ArgoMAC

/-- The submission uses 91 digits and three shared permutation slots. -/
def solution : Kriterion.Solution := {
  FixedIndex := Shared.FixedKeyIndex
  EncIndex := EncPRF.PermutationIndex
  fixedFinite := inferInstance
  encFinite := inferInstance
  Randomness := Shared.Randomness
  randomnessFinite := inferInstance
  randomness := Shared.Randomness.ofLegacy (Seed.randomness 0)
  Public := Pipeline.PackedTable
  EncodingKey := Garbling.EncodingKey
  State := Shared.Simulator.State
  encoding := Wire.encoding
  ciphertextBytes := 8887896
  evaluationOracle := Shared.evaluationOracle
  oracleUniform := by
    convert Shared.oracleUniform (Shared.Randomness.ofLegacy (Seed.randomness 0)) using 1
  scheme := fun f g => @Shared.packedCircuit f g
  ciphertextSize := fun field group => @Shared.packedCiphertextSize field group
  lamportCompatible := fun field group => @Shared.packedCompatible field group
  idealOracle := Security.circuitSimulatorOracleHandler
  idealView := Security.CircuitSimulatorState.view
  functionCorrect := fun _ _ _ _ => rfl
  perfectCorrectness := fun field group => @Shared.packedPerfectCorrectness field group
  adaptivePrivacy := by
    intro field group
    letI := field
    letI := group
    convert ArithmeticSimulator.compiledAdaptivePrivacy (Aux := Unit)
      (Shared.Randomness.ofLegacy (Seed.randomness 0)) using 1
    rfl
}

end Submission
