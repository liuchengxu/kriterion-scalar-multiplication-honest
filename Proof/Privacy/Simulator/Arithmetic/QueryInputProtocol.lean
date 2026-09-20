import Proof.Privacy.Simulator.Arithmetic.QueryInputFixed
import Proof.Privacy.Simulator.Arithmetic.QueryInputEnc
import Proof.Privacy.Simulator.Arithmetic.QueryInputHash

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The encryption interface has 508 independent public permutations. -/
theorem encPermutationIndex_count : Fintype.card EncPRF.PermutationIndex = 508 := by
  have coordinate : Fintype.card EncPRF.Coordinate = 2 := by decide
  simp [EncPRF.PermutationIndex, coordinateBitCount, coordinate]

theorem fixedIndexWidth : Nat.size 15240 = 14 := by decide
theorem encIndexWidth : Nat.size 508 = 9 := by decide

/-- The query result uses the protocol's canonical index enumeration. -/
noncomputable def queryOperands : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex →
    Word × Word × Word
  | .fixedForward index value => (BitVec.ofNat 256 value.toNat,
      BitVec.ofNat 256 (Fintype.equivFin Shared.FixedKeyIndex index).val, BitVec.ofNat 256 0)
  | .fixedInverse index value => (BitVec.ofNat 256 value.toNat,
      BitVec.ofNat 256 (Fintype.equivFin Shared.FixedKeyIndex index).val, BitVec.ofNat 256 1)
  | .encForward index value => (BitVec.ofNat 256 value.toNat,
      BitVec.ofNat 256 ((Fintype.equivFin EncPRF.PermutationIndex index).val + 15240), BitVec.ofNat 256 2)
  | .encInverse index value => (BitVec.ofNat 256 value.toNat,
      BitVec.ofNat 256 ((Fintype.equivFin EncPRF.PermutationIndex index).val + 15240), BitVec.ofNat 256 3)
  | .hash value => (BitVec.ofNat 256 value.val, 15748, 4)

/-- The query family determines the exact reader cost. -/
def queryInputCost : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex → Nat
  | .fixedForward _ _ | .fixedInverse _ _ => 1042
  | .encForward _ _ | .encInverse _ _ => 1011
  | .hash _ => 1822

/-- The fixed machine decodes every canonical public query and retains permanent RAM. -/
theorem queryInput_protocol [BN254.FieldCertificate] (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : base.bits 0 = GarbledCircuit.SimulatorProtocol.query request ++ rest) :
    (run queryInput (queryInputCost request) ⟨0, base⟩).map (Option.map fun result =>
      (result.1.memory.registers 8, result.1.memory.registers 9,
        result.1.memory.registers 10, result.1.memory.bits 0, result.1.memory.ram, result.2)) =
      PMF.pure (some ((queryOperands request).1, (queryOperands request).2.1,
        (queryOperands request).2.2, rest, base.ram, queryInputCost request)) := by
  cases request with
  | fixedForward index value =>
      have indexBound : (Fintype.equivFin Shared.FixedKeyIndex index).val < 15240 := by
        simpa only [sharedFixedKeyIndex_count] using (Fintype.equivFin Shared.FixedKeyIndex index).isLt
      simpa only [queryInputCost, queryOperands] using queryInput_fixedSource base 0
        (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide) indexBound
        value.isLt (by simpa only [GarbledCircuit.SimulatorProtocol.query, sharedFixedKeyIndex_count,
          fixedIndexWidth,
          List.append_assoc] using wire)
  | fixedInverse index value =>
      have indexBound : (Fintype.equivFin Shared.FixedKeyIndex index).val < 15240 := by
        simpa only [sharedFixedKeyIndex_count] using (Fintype.equivFin Shared.FixedKeyIndex index).isLt
      simpa only [queryInputCost, queryOperands] using queryInput_fixedSource base 1
        (Fintype.equivFin Shared.FixedKeyIndex index).val value.toNat rest (by decide) indexBound
        value.isLt (by simpa only [GarbledCircuit.SimulatorProtocol.query, sharedFixedKeyIndex_count,
          fixedIndexWidth,
          List.append_assoc] using wire)
  | encForward index value =>
      have indexBound : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
        simpa only [encPermutationIndex_count] using (Fintype.equivFin EncPRF.PermutationIndex index).isLt
      simpa only [queryInputCost, queryOperands] using queryInput_encSource base 2
        (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) (by decide)
        indexBound value.isLt (by simpa only [GarbledCircuit.SimulatorProtocol.query, encPermutationIndex_count,
          encIndexWidth,
          List.append_assoc] using wire)
  | encInverse index value =>
      have indexBound : (Fintype.equivFin EncPRF.PermutationIndex index).val < 508 := by
        simpa only [encPermutationIndex_count] using (Fintype.equivFin EncPRF.PermutationIndex index).isLt
      simpa only [queryInputCost, queryOperands] using queryInput_encSource base 3
        (Fintype.equivFin EncPRF.PermutationIndex index).val value.toNat rest (by decide) (by decide)
        indexBound value.isLt (by simpa only [GarbledCircuit.SimulatorProtocol.query, encPermutationIndex_count,
          encIndexWidth,
          List.append_assoc] using wire)
  | hash value =>
      simpa only [queryInputCost, queryOperands] using queryInput_hashSource base value.val rest
        (lt_trans value.val_lt (by decide : BN254.baseFieldModulus < 2 ^ 254))
        (by simpa [GarbledCircuit.SimulatorProtocol.query, List.append_assoc] using wire)

/-- Every query fits 1919 units including the 97-entry reader table. -/
theorem queryInput_budget (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    queryInput.size + 1 + queryInputCost request ≤ 1919 := by
  cases request <;> norm_num [queryInputCost, show queryInput.size = 96 from rfl]

end Kriterion.ArgoMAC.ArithmeticSimulator
