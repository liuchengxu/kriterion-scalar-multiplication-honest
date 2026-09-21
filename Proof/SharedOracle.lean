import Construction.OraclePrograms
import Proof.Privacy.Simulator.PublicOracleLaw
import Solution
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
  let : Fintype PrivateCoins := Fintype.ofFinite _
  let : Nonempty PrivateCoins := ⟨privateCoins witness⟩
  let : Nonempty Randomness := ⟨witness⟩
  let split := splitCoins.trans (Equiv.prodComm _ _)
  rw [Assumptions.StandardAssumptions, uniformTape_eq]
  have mapped := congrArg (PMF.map Prod.fst) (Security.uniform_map_equiv split)
  rw [Security.uniform_map_fst] at mapped
  simpa only [PMF.map_comp, Function.comp_def, split, splitCoins, Equiv.trans_apply, Equiv.prodComm_apply, Equiv.coe_fn_mk, Prod.swap_prod_mk] using mapped

end Kriterion.ArgoMAC.Shared

namespace Kriterion.ArgoMAC.Security.OperationalOracle
open Cryptography GarbledCircuit
noncomputable section

set_option maxRecDepth 4096 in
/-- The transmitted form of the same game: the garble program publishes the packed
table and the adversary reads the packed table. -/
theorem packed_shared_lazy_real [BN254.FieldCertificate] [BN254.GroupCertificate]
    [Fintype Shared.PrivateCoins] {Aux : Type}
    (adversary : AdaptiveAdversary (publicOracleSpec Shared.FixedKeyIndex EncPRF.PermutationIndex)
      BN254.AffineInput Pipeline.PackedTable LamportSignature Aux)
    (parameter : Nat) (scalar : BN254.NonZeroScalar) (auxiliary : Aux) (witness : Shared.Randomness) :
    lazyRealGame (uniformRandomTape Shared.PrivateCoins (Shared.privateCoins witness))
      (fun p c r => (Shared.packedGarbleProgram p c r).toOracleProgram) Shared.packedProgramCircuit.encode
      adversary parameter scalar auxiliary =
    realGame Shared.packedCircuit (uniformRandomTape Shared.Randomness witness)
      (publicHandler Shared.evaluationOracle) adversary parameter scalar auxiliary := by
  classical
  letI : Nonempty Shared.Randomness := ⟨witness⟩
  letI : Nonempty Shared.PrivateCoins := ⟨Shared.privateCoins witness⟩
  rw [lazy_real_uniform]
  simp only [uniformRandomTape, uniformTape_eq, Shared.packedGarbleProgram_correct, realGame,
    GarbledCircuit.mapPublic]
  let experiment (tape : Shared.Randomness) : PMF Bool :=
    let garbled := Shared.packedCircuit.garble parameter scalar tape
    ((adversary.chooseInput parameter garbled.1 auxiliary).run
      (publicHandler Shared.evaluationOracle) tape).bind fun selected =>
      ((adversary.decide parameter garbled.1 (Shared.packedCircuit.encode garbled.2 selected.1.1)
        auxiliary selected.1.2).run (publicHandler Shared.evaluationOracle) selected.2).map Prod.fst
  have split := congrArg (fun distribution : PMF Shared.Randomness => distribution.bind experiment)
    (uniform_equiv Shared.splitCoins.symm)
  rw [PMF.bind_map] at split
  change _ = (PMF.uniformOfFintype Shared.Randomness).bind experiment
  rw [← split, ← uniform_product (A := Shared.PrivateCoins)
    (B := PublicOracle Shared.FixedKeyIndex EncPRF.PermutationIndex), PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def]
  apply PMF.bind_congr
  intro coins _
  apply PMF.bind_congr
  intro oracle _
  dsimp only [experiment]
  rw [public_run_tape (project := Shared.evaluationOracle)]
  simp only [PMF.bind_map, Function.comp_def]
  simp only [Shared.splitCoins, Equiv.coe_fn_symm_mk, Shared.evaluationOracle,
    Shared.replaceOracle, Shared.restrict_expand]
  apply PMF.bind_congr
  intro selected reached
  have stable : selected.2 = oracle := by
    have member : selected ∈ ((adversary.chooseInput parameter
        (Shared.packedProgramCircuit.garble parameter scalar (coins, oracle)).1 auxiliary).run
          (publicHandler id) oracle).support := reached
    rw [public_run_tape (project := id), PMF.support_map] at member
    obtain ⟨value, _, equal⟩ := member
    exact (congrArg Prod.snd equal).symm
  rw [public_run_tape (project := Shared.evaluationOracle), stable]
  simp only [PMF.map_comp, Function.comp_def]
  rfl


end
end Kriterion.ArgoMAC.Security.OperationalOracle
