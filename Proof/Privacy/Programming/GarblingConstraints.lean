import Proof.Privacy.Distribution.PublicDistribution

namespace Kriterion.ArgoMAC.Security

open BN254 Cryptography

noncomputable section

/-- A prescribed full hash lift fixes the three actual permutation answers. -/
theorem fixedHashLift_eq_iff (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (lift : FullHashLift) :
    fixedDaviesMeyerHashLift location window label oracle = lift ↔
      ∀ slot, oracle.permutation (fixedKeyIndex location window (.hash slot))
        (gateInput location label) = fullHashLiftBlockEquiv lift slot ^^^ (gateInput location label) := by
  rw [fixedDaviesMeyerHashLift_eq, Equiv.symm_apply_eq, funext_iff]
  apply forall_congr'
  intro slot
  constructor
  · intro equal
    have shifted := congrArg (fun value => value ^^^ (gateInput location label)) equal
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using shifted
  · intro equal
    rw [equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- A prescribed complete pad fixes the two actual permutation answers. -/
theorem fixedPadLift_eq_iff (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (pad : BitAdaptor.Ciphertext) :
    BitAdaptor.padBytes (Pipeline.fixedKeyPermutations oracle location window) (gateInput location label) = pad ↔
      ∀ slot, oracle.permutation (fixedKeyIndex location window (.pad slot))
        (gateInput location label) = ciphertextBlockEquiv pad slot ^^^ (gateInput location label) := by
  rw [← BitVec.equivFin.injective.eq_iff]
  change fixedDaviesMeyerPadLift location window label oracle = BitVec.equivFin pad ↔ _
  rw [fixedDaviesMeyerPadLift_eq, Equiv.symm_apply_eq, funext_iff]
  apply forall_congr'
  intro slot
  constructor
  · intro equal
    have shifted := congrArg (fun value => value ^^^ (gateInput location label)) equal
    change _ = ciphertextBlockEquiv pad slot ^^^ (gateInput location label) at shifted
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using shifted
  · intro equal
    rw [equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rfl

/-- A prescribed hash lift fixes the actual field mask. -/
theorem fixedHashToField_of_lift (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (label : Block)
    (lift : FullHashLift)
    (equal : fixedDaviesMeyerHashLift location window label oracle = lift) :
    (Pipeline.fixedKeyGate oracle location window).hashToField label = (lift.val : BaseField) := by
  exact congrArg (fun value : FullHashLift => (value.val : BaseField)) equal

/-- The real garbler table and full hash lift are exactly five permutation constraints. -/
theorem bitAdaptorGarble_eq_iff (oracle : PermutationOracle Pipeline.FixedKeyIndex Block)
    (location : Pipeline.FixedKeyLocation) (window : Nat) (key : BitAdaptor.Key)
    (slope : BaseField) (lift : FullHashLift) (table : BitAdaptor.Table) :
    (fixedDaviesMeyerHashLift location window key.falseLabel oracle = lift ∧
      (BitAdaptor.garble (Pipeline.fixedKeyGate oracle location window) slope key).1 = table) ↔
    (∀ slot, oracle.permutation (fixedKeyIndex location window (.hash slot))
      (gateInput location key.falseLabel) = fullHashLiftBlockEquiv lift slot ^^^ (gateInput location key.falseLabel)) ∧
    (∀ slot, oracle.permutation (fixedKeyIndex location window (.pad slot))
      (gateInput location key.trueLabel) =
        targetPadBlocks table (slope + (lift.val : BaseField)) slot ^^^ (gateInput location key.trueLabel)) := by
  rw [← fixedHashLift_eq_iff]
  apply and_congr_right
  intro hashEqual
  have fieldEqual := fixedHashToField_of_lift oracle location window key.falseLabel lift hashEqual
  have tableEq : (BitAdaptor.garble (Pipeline.fixedKeyGate oracle location window) slope key).1 = table ↔
      BitAdaptor.padBytes (Pipeline.fixedKeyPermutations oracle location window) (gateInput location key.trueLabel) =
        table.trueRow ^^^ BitAdaptor.fieldBytes (slope + (lift.val : BaseField)) := by
    have tableExt : ∀ first second : BitAdaptor.Table,
        first = second ↔ first.trueRow = second.trueRow := by
      intro first second
      cases first
      cases second
      simp
    rw [tableExt]
    change _ ^^^ BitAdaptor.fieldBytes
      (slope + (Pipeline.fixedKeyGate oracle location window).hashToField key.falseLabel) = _ ↔ _
    rw [fieldEqual]
    change BitAdaptor.padBytes (Pipeline.fixedKeyPermutations oracle location window)
      (gateInput location key.trueLabel) ^^^ BitAdaptor.fieldBytes (slope + (lift.val : BaseField)) =
        table.trueRow ↔ _
    constructor
    · intro equal
      have shifted := congrArg
        (fun value => value ^^^ BitAdaptor.fieldBytes (slope + (lift.val : BaseField))) equal
      simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using shifted
    · intro equal
      rw [equal, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rw [tableEq, fixedPadLift_eq_iff]
  rfl

end

end Kriterion.ArgoMAC.Security
