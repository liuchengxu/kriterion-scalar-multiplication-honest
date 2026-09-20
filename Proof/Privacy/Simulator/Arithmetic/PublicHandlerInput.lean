import Proof.Privacy.Simulator.Arithmetic.PublicHandlerDispatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The canonical query selects its matching public handler entry. -/
def publicInputLabel : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex → Fin 1772
  | .fixedForward _ _ | .encForward _ _ => 102
  | .fixedInverse _ _ | .encInverse _ _ => 299
  | .hash _ => 542

/-- The public input source includes the canonical reader and fixed dispatcher. -/
noncomputable def publicInputMemory (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : Memory :=
  publicDispatchMemory (queryInputMemory base request rest)

/-- The input prefix charges the reader without its standalone halt and the dispatcher. -/
def publicInputCost : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex → Nat
  | .fixedForward _ _ | .fixedInverse _ _ => 1047
  | .encForward _ _ | .encInverse _ _ => 1016
  | .hash _ => 1824

/-- The decoded query tag selects the matching fixed branch. -/
theorem publicInput_dispatch (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    publicDispatchLabel (queryInputMemory base request rest) = publicInputLabel request ∧
    queryInputCost request - 1 + publicDispatchCost (queryInputMemory base request rest) = publicInputCost request := by
  have tag := (queryInputMemory_values base request rest).2.2.1
  unfold publicDispatchLabel publicDispatchCost
  rw [tag]
  cases request <;> simp [queryOperands, publicInputLabel, queryInputCost, publicInputCost]

/-- The complete input prefix accepts every canonical public query and preserves unused fuel. -/
theorem publicHandler_input [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : base.bits 0 = query request ++ rest) :
    run (publicHandler attempts) (publicInputCost request + fuel) ⟨0, base⟩ =
      (run (publicHandler attempts) fuel ⟨publicInputLabel request, publicInputMemory base request rest⟩).map
        (Option.map fun result => (result.1, result.2 + publicInputCost request)) := by
  have routed := publicInput_dispatch base request rest
  rw [← routed.2, Nat.add_assoc]
  have parsed := queryInputBlock_continue (publicHandler attempts) publicQueryLabels
    (publicHandler_query attempts) base request rest wire
    (publicDispatchCost (queryInputMemory base request rest) + fuel)
  change run (publicHandler attempts) _ ⟨0, base⟩ = _ at parsed
  rw [parsed]
  change (run (publicHandler attempts) _ ⟨96, queryInputMemory base request rest⟩).map _ = _
  rw [publicHandler_dispatchContinue]
  simp [PMF.map_comp, Option.map_map, Function.comp_def, routed.1,
    publicInputMemory, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The compiled input prefix returns the request operand, oracle index, and unchanged RAM. -/
theorem publicInputMemory_values (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    (publicInputMemory base request rest).registers 8 = (queryOperands request).1 ∧
    (publicInputMemory base request rest).registers 9 = (queryOperands request).2.1 ∧
    (publicInputMemory base request rest).registers 10 = (queryOperands request).2.2 ∧
    (publicInputMemory base request rest).bits 0 = rest ∧
    (publicInputMemory base request rest).ram = base.ram := by
  have decoded := queryInputMemory_values base request rest
  have preserved := publicDispatchMemory_data (queryInputMemory base request rest)
  exact ⟨preserved.1.trans decoded.1, preserved.2.1.trans decoded.2.1,
    preserved.2.2.1.trans decoded.2.2.1,
    (congrFun preserved.2.2.2.2 0).trans decoded.2.2.2.1,
    preserved.2.2.2.1.trans decoded.2.2.2.2⟩

/-- The canonical reader and dispatcher use at most 1824 instructions. -/
theorem publicInputCost_bound (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) :
    publicInputCost request ≤ 1824 := by cases request <;> simp [publicInputCost]

end Kriterion.ArgoMAC.ArithmeticSimulator
