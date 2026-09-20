import Proof.Privacy.Simulator.Arithmetic.OnlineInputPrefix

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- The zero-coordinate block has seven labels and one return label. -/
def onlineZeroLabels (index : Nat) : Fin 98 :=
  if inside : index < 7 then ⟨90 + index, by omega⟩ else 97

/-- The reader contains the complete zero-coordinate block. -/
theorem onlineInput_zeroContains : ContainsLinear onlineInput onlineInputZero onlineZeroLabels := by
  intro index valid
  have small : index < 7 := valid
  interval_cases index <;> simp [onlineInput, onlineInputZero, onlineZeroLabels, LinearInstruction.emit]

/-- The null path writes zero to both unused output coordinates. -/
def onlineNullMemory (base : Memory) (x y tag : Nat) (rest : List Bool) : Memory :=
  executeLinear onlineInputZero (onlineBranchMemory (onlineTaggedMemory base x y tag rest))

/-- The null path returns after it stores the two zero coordinates. -/
theorem onlineInput_nullPrefix [BN254.FieldCertificate] (base : Memory)
    (x y tag : Nat) (rest : List Bool) (tagFits : tag < 4) (notAffine : tag ≠ 1)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 tag ++ rest) :
    runPrefix onlineInput 3607 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨97, onlineNullMemory base x y tag rest⟩, 3607)) := by
  let tagged := onlineTaggedMemory base x y tag rest
  have readTag := onlineInput_taggedPrefix base x y tag rest wire
  have tagValue : tagged.registers 0 = BitVec.ofNat 256 tag := by
    simp [tagged, onlineTaggedMemory, onlineReadStored, onlineStored, decodedInput_values,
      Nat.mod_eq_of_lt tagFits]
  have tagNe : tagged.registers 0 ≠ 1 := by
    rw [tagValue]
    intro equal
    have values := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at values
    have small : tag < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt small] at values
    exact notAffine values
  have branch := onlineInput_branch tagged
  rw [if_neg tagNe] at branch
  have zeros := linear_prefix onlineInput onlineInputZero onlineZeroLabels
    onlineInput_zeroContains (onlineBranchMemory tagged)
  change runPrefix onlineInput 7 ⟨90, onlineBranchMemory tagged⟩ =
    PMF.pure (some (false, ⟨97, onlineNullMemory base x y tag rest⟩, 7)) at zeros
  change runPrefix onlineInput (3597 + (3 + 7)) ⟨0, base⟩ = _
  rw [prefix_add, readTag, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [zeros]
  simp [PMF.pure_map]

/-- The affine reader charges its final halt. -/
theorem onlineInput_affineRun [BN254.FieldCertificate] (base : Memory)
    (x y outX outY : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 1 ++
      bits 254 outX ++ bits 254 outY ++ rest) :
    run onlineInput 7175 ⟨0, base⟩ =
      PMF.pure (some (⟨97, onlineAffineMemory base x y outX outY rest⟩, 7175)) := by
  rw [show 7175 = 7174 + 1 by decide, run_after_prefix,
    onlineInput_affinePrefix base x y outX outY rest wire, PMF.pure_bind]
  simp [run, step, onlineInput, PMF.pure_map]

/-- The null reader charges its final halt. -/
theorem onlineInput_nullRun [BN254.FieldCertificate] (base : Memory)
    (x y tag : Nat) (rest : List Bool) (tagFits : tag < 4) (notAffine : tag ≠ 1)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 tag ++ rest) :
    run onlineInput 3608 ⟨0, base⟩ =
      PMF.pure (some (⟨97, onlineNullMemory base x y tag rest⟩, 3608)) := by
  rw [show 3608 = 3607 + 1 by decide, run_after_prefix,
    onlineInput_nullPrefix base x y tag rest tagFits notAffine wire, PMF.pure_bind]
  simp [run, step, onlineInput, PMF.pure_map]

end Kriterion.ArgoMAC.ArithmeticSimulator
