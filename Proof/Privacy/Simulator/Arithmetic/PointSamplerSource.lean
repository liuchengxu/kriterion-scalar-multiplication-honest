import Proof.Privacy.Simulator.Arithmetic.RuntimeSampler
import Proof.Privacy.Simulator.OperationalSimulator
import Proof.Privacy.Simulator.SimulatorTotalSampling

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The scalar modulus has a positive canonical runtime-range encoding. -/
theorem runtimeRange_scalar :
    runtimeRange (BitVec.ofNat 256 BN254.scalarFieldModulus) = BN254.scalarFieldModulus := by
  have fits : BN254.scalarFieldModulus < 2 ^ 256 := by decide
  have nonzero : BitVec.ofNat 256 BN254.scalarFieldModulus ≠ 0#256 := by decide
  simp only [runtimeRange, if_neg nonzero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The total source point sampler applies the point algorithm to its total scalar draw. -/
theorem point_total_source [BN254.FieldCertificate] (attempts : Nat) :
    (Security.SimulatorSampling.point.total attempts).law =
      (Security.BoundedIntegerSampling.totalInteger BN254.scalarFieldModulus (by decide) attempts).law.map
        (fun value => Security.samplePoint (Security.SimulatorSampling.scalarEquiv value)) := by
  simp only [Security.SimulatorSampling.point, Security.SimulatorSampling.scalar,
    Security.SimulatorSampling.Code.map, Security.SimulatorSampling.Code.total,
    Security.BoundedIntegerSampling.BitCode.bind_law, Security.BoundedIntegerSampling.BitCode.law,
    PMF.bind_bind, PMF.pure_bind, PMF.map, Function.comp_def]

/-- The runtime scalar memory gives the exact total source point distribution. -/
theorem pointSamplerMemory_source [BN254.FieldCertificate] [BN254.GroupCertificate]
    (attempts : Nat) (base : Memory) :
    (runtimeSamplerMemory (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts base).map
      (fun result => ((trialValue result.1).getD 0).toNat • Security.standardGenerator) =
      (Security.SimulatorSampling.point.total attempts).law := by
  have projected := congrArg
    (PMF.map fun value : Option Word => (value.getD 0).toNat • Security.standardGenerator)
    (runtimeSamplerMemory_source (BitVec.ofNat 256 BN254.scalarFieldModulus) attempts base)
  rw [runtimeRange_scalar] at projected
  simp only [PMF.map_comp, Function.comp_def] at projected
  rw [projected, point_total_source]
  simp only [Security.BoundedIntegerSampling.totalInteger,
    Security.BoundedIntegerSampling.BitCode.bind_law, Security.BoundedIntegerSampling.BitCode.law,
    PMF.map_bind, PMF.pure_map]
  change (Security.BoundedIntegerSampling.cutoff BN254.scalarFieldModulus attempts).law.map _ =
    (Security.BoundedIntegerSampling.cutoff BN254.scalarFieldModulus attempts).law.map _
  apply congrArg (fun f => PMF.map f
    (Security.BoundedIntegerSampling.cutoff BN254.scalarFieldModulus attempts).law)
  funext value
  cases value with
  | none =>
      simp only [Option.map_none, Option.getD_none, BitVec.toNat_ofNat, Nat.zero_mod, zero_nsmul,
        Security.samplePoint_eq_smul, Security.SimulatorSampling.scalarEquiv, Equiv.coe_fn_mk,
        Nat.cast_zero, zero_smul]
      change (0 : BN254.Point) = (0 : BN254.ScalarField) • Security.standardGenerator
      exact (zero_smul BN254.ScalarField (Security.standardGenerator : BN254.Point)).symm
  | some value =>
      have fits : value.val < 2 ^ 256 := lt_trans value.isLt (by decide : BN254.scalarFieldModulus < 2 ^ 256)
      simp only [Option.map_some, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits,
        Security.samplePoint_eq_smul, Security.SimulatorSampling.scalarEquiv, Equiv.coe_fn_mk,
        Nat.cast_smul_eq_nsmul]

end Kriterion.ArgoMAC.ArithmeticSimulator
