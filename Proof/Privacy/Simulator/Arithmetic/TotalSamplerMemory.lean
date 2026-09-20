import Proof.Privacy.Simulator.Arithmetic.TotalSamplerBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- A positive range at most one word has an exact runtime encoding. -/
theorem runtimeRange_nat (size : Nat) (positive : 0 < size) (bounded : size ≤ 2 ^ 256) :
    runtimeRange (BitVec.ofNat 256 size) = size := by
  by_cases full : size = 2 ^ 256
  · subst size
    have zero : BitVec.ofNat 256 (2 ^ 256) = 0#256 := by decide
    simp only [runtimeRange, zero, if_pos rfl, if_true]
  · have fits : size < 2 ^ 256 := lt_of_le_of_ne bounded full
    have nonzero : BitVec.ofNat 256 size ≠ 0#256 := by
      intro equal
      have natural := congrArg BitVec.toNat equal
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits] at natural
      change size = 0 at natural
      omega
    simp only [runtimeRange, if_neg nonzero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]

/-- The total result law matches the source integer sampler, including its fallback. -/
theorem totalSamplerMemory_source [BN254.FieldCertificate] (bound : Word) (attempts : Nat) (offset : Word) (base : Memory) :
    (totalSamplerMemory bound attempts offset base).map (fun result => result.1.registers 0) =
      (Security.BoundedIntegerSampling.totalInteger (runtimeRange bound) (runtimeRange_bounds bound).1 attempts).law.map
        (fun value => BitVec.ofNat 256 value.val + offset) := by
  have projected := congrArg (PMF.map fun value : Option Word => value.getD 0 + offset)
    (runtimeSamplerMemory_source bound attempts
      {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)})
  simp only [PMF.map_comp, Function.comp_def] at projected
  rw [totalSamplerMemory, PMF.map_comp]
  simp only [Function.comp_def, totalSamplerFinal_value]
  rw [projected]
  simp only [Security.BoundedIntegerSampling.totalInteger,
    Security.BoundedIntegerSampling.BitCode.bind_law, Security.BoundedIntegerSampling.BitCode.law,
    PMF.map_bind, PMF.pure_map]
  change (Security.BoundedIntegerSampling.cutoff (runtimeRange bound) attempts).law.map _ =
    (Security.BoundedIntegerSampling.cutoff (runtimeRange bound) attempts).law.map _
  apply congrArg (fun f => PMF.map f (Security.BoundedIntegerSampling.cutoff (runtimeRange bound) attempts).law)
  funext value
  cases value <;> rfl

/-- The total sampler preserves caller stacks and RAM. -/
theorem totalSamplerMemory_data (bound : Word) (attempts : Nat) (offset : Word)
    (base final : Memory) (cost : Nat) (supported : (final, cost) ∈ (totalSamplerMemory bound attempts offset base).support) :
    final.bits = base.bits ∧ final.ram = base.ram := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  exact runtimeSamplerMemory_data bound attempts
    {base with registers := Function.update base.registers 4 (BitVec.ofNat 256 attempts)} memory spent member

/-- The total sampler preserves registers eight through fifteen. -/
theorem totalSamplerMemory_caller (bound : Word) (attempts : Nat) (offset : Word)
    (base final : Memory) (cost : Nat) (register : Register) (caller : 8 ≤ register.val)
    (supported : (final, cost) ∈ (totalSamplerMemory bound attempts offset base).support) :
    final.registers register = base.registers register := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have different (target : Register) (localRegister : target.val < 8) : register ≠ target := by
    intro equal
    have values := congrArg Fin.val equal
    omega
  have retained := runtimeSamplerMemory_caller bound attempts _ memory spent register caller member
  dsimp only [totalSamplerFinal]
  rw [Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 6 (by decide))]
  split
  · rw [Function.update_of_ne (different 0 (by decide))]
    simpa only [Function.update_of_ne (different 4 (by decide))] using retained
  · simpa only [Function.update_of_ne (different 4 (by decide))] using retained

/-- The total sampler preserves the runtime-range register. -/
theorem totalSamplerMemory_range (bound : Word) (attempts : Nat) (offset : Word)
    (base final : Memory) (cost : Nat) (range : base.registers 5 = bound)
    (supported : (final, cost) ∈ (totalSamplerMemory bound attempts offset base).support) :
    final.registers 5 = bound := by
  obtain ⟨⟨memory, spent⟩, member, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
  have retained := runtimeSamplerMemory_range bound attempts _ memory spent (by simpa using range) member
  dsimp only [totalSamplerFinal]
  rw [Function.update_of_ne (by decide : (5 : Register) ≠ 0),
    Function.update_of_ne (by decide : (5 : Register) ≠ 6)]
  split
  · rw [Function.update_of_ne (by decide : (5 : Register) ≠ 0)]
    exact retained
  · exact retained

end Kriterion.ArgoMAC.ArithmeticSimulator
