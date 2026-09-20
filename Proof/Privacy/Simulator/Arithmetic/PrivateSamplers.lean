import Proof.Privacy.Simulator.Arithmetic.TotalSampler
import Proof.Privacy.Simulator.OperationalSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

private theorem word_add_zero (value : Word) : value + 0 = value := BitVec.add_zero value

/-- Total private sampling preserves deterministic source maps. -/
theorem totalCode_map_law {A B : Type} {count : Nat} (attempts : Nat)
    (source : Security.SimulatorSampling.Code A count) (transform : A → B) :
    ((source.map transform).total attempts).law = (source.total attempts).law.map transform := by
  simp only [Security.SimulatorSampling.Code.map, Security.SimulatorSampling.Code.total,
    Security.BoundedIntegerSampling.BitCode.bind_law, Security.BoundedIntegerSampling.BitCode.law,
    PMF.map, Function.comp_def]

/-- The canonical range gives the exact total integer law. -/
theorem totalSamplerMemory_nat_source [BN254.FieldCertificate] (size attempts : Nat) (offset : Word) (base : Memory)
    (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    (totalSamplerMemory (BitVec.ofNat 256 size) attempts offset base).map (fun result => result.1.registers 0) =
      (Security.BoundedIntegerSampling.totalInteger size positive attempts).law.map
        (fun value => BitVec.ofNat 256 value.val + offset) := by
  have source := totalSamplerMemory_source (BitVec.ofNat 256 size) attempts offset base
  have transport (first second : Nat) (firstPositive : 0 < first) (secondPositive : 0 < second)
      (same : first = second) :
      (Security.BoundedIntegerSampling.totalInteger first firstPositive attempts).law.map
        (fun value => BitVec.ofNat 256 value.val + offset) =
      (Security.BoundedIntegerSampling.totalInteger second secondPositive attempts).law.map
        (fun value => BitVec.ofNat 256 value.val + offset) := by
    cases same
    rfl
  exact source.trans (transport _ _ _ _ (runtimeRange_nat size positive bounded))

/-- The field sampler returns the canonical word representation of the total source field draw. -/
theorem fieldSamplerMemory_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (totalSamplerMemory (BitVec.ofNat 256 BN254.baseFieldModulus) attempts 0 base).map
      (fun result => result.1.registers 0) =
      (Security.SimulatorSampling.field.total attempts).law.map (fun value => BitVec.ofNat 256 value.val) := by
  rw [totalSamplerMemory_nat_source BN254.baseFieldModulus attempts 0 base (by decide) (by decide)]
  simp only [Security.SimulatorSampling.field, totalCode_map_law,
    Security.SimulatorSampling.Code.total, PMF.map_comp, Function.comp_def]
  apply congrArg (fun f => PMF.map f
    (Security.BoundedIntegerSampling.totalInteger BN254.baseFieldModulus (by decide) attempts).law)
  funext value
  simp only [Security.baseFieldFinEquiv, Equiv.coe_fn_mk, ZMod.val_natCast,
    Nat.mod_eq_of_lt value.isLt, word_add_zero]

/-- The scale sampler returns a canonical nonzero field word, including fallback value one. -/
theorem scaleSamplerMemory_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (totalSamplerMemory (BitVec.ofNat 256 (BN254.baseFieldModulus - 1)) attempts 1 base).map
      (fun result => result.1.registers 0) =
      (Security.SimulatorSampling.scale.total attempts).law.map (fun value => BitVec.ofNat 256 value.value.val) := by
  rw [totalSamplerMemory_nat_source (BN254.baseFieldModulus - 1) attempts 1 base (by decide) (by decide)]
  simp only [Security.SimulatorSampling.scale, totalCode_map_law,
    Security.SimulatorSampling.Code.total, PMF.map_comp, Function.comp_def]
  apply congrArg (fun f => PMF.map f
    (Security.BoundedIntegerSampling.totalInteger (BN254.baseFieldModulus - 1) (by decide) attempts).law)
  funext value
  have bounded : value.val + 1 < BN254.baseFieldModulus := by have h := value.isLt; omega
  simp only [Security.SimulatorSampling.nonzeroEquiv, Equiv.coe_fn_mk, ZMod.val_natCast,
    Nat.mod_eq_of_lt bounded, BitVec.ofNat_add]
  rfl

/-- The quotient sampler returns the exact finite hash-lift source draw. -/
theorem quotientSamplerMemory_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (totalSamplerMemory (BitVec.ofNat 256 Security.hashLiftQuotientCount) attempts 0 base).map
      (fun result => result.1.registers 0) =
      (Security.SimulatorSampling.quotient.total attempts).law.map (fun value => BitVec.ofNat 256 value.val) := by
  have positive : 0 < Security.hashLiftQuotientCount := by
    set_option exponentiation.threshold 400 in decide
  have bounded : Security.hashLiftQuotientCount ≤ 2 ^ 256 := Security.SimulatorSampling.quotient_drawSizeLe
  rw [totalSamplerMemory_nat_source Security.hashLiftQuotientCount attempts 0 base positive bounded]
  simp only [Security.SimulatorSampling.quotient, Security.SimulatorSampling.Code.total, word_add_zero]

/-- The bit sampler returns the source block in the low bits of one machine word. -/
theorem bitsSamplerMemory_source [BN254.FieldCertificate] (width attempts : Nat) (base : Memory)
    (fits : width ≤ 256) :
    (totalSamplerMemory (BitVec.ofNat 256 (2 ^ width)) attempts 0 base).map
      (fun result => result.1.registers 0) =
      ((Security.SimulatorSampling.bits width).total attempts).law.map (fun value => value.setWidth 256) := by
  rw [totalSamplerMemory_nat_source (2 ^ width) attempts 0 base (Nat.two_pow_pos width)
    (Nat.pow_le_pow_right (by decide) fits)]
  simp only [Security.SimulatorSampling.bits, totalCode_map_law,
    Security.SimulatorSampling.Code.total, PMF.map_comp, Function.comp_def]
  apply congrArg (fun f => PMF.map f
    (Security.BoundedIntegerSampling.totalInteger (2 ^ width) (Nat.two_pow_pos width) attempts).law)
  funext value
  simp only [word_add_zero]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth, BitVec.equivFin]

end Kriterion.ArgoMAC.ArithmeticSimulator
