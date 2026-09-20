import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerOutputCode
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerInput

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol

/-- The input source saves the external request before dispatch. -/
noncomputable def recordedPublicInputMemory (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) : Memory :=
  publicDispatchMemory (executeLinear publicHistorySave (queryInputMemory base request rest))

/-- The saved request selects the same branch and dispatch cost. -/
theorem recordedPublicInput_dispatch (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool) :
    let saved := executeLinear publicHistorySave (queryInputMemory base request rest)
    publicDispatchLabel saved = publicInputLabel request ∧
    queryInputCost request - 1 + publicDispatchCost saved = publicInputCost request := by
  have tag := (publicHistorySave_state (queryInputMemory base request rest)).2.2.2.2
  have decoded := (queryInputMemory_values base request rest).2.2.1
  dsimp only
  unfold publicDispatchLabel publicDispatchCost
  rw [tag, decoded]
  cases request <;> simp [queryOperands, publicInputLabel, queryInputCost, publicInputCost]

/-- The saved request reaches its public handler with an exact four-instruction surcharge. -/
theorem recordedPublicHandler_input [BN254.FieldCertificate] (attempts fuel : Nat) (base : Memory)
    (request : PublicQuery Shared.FixedKeyIndex EncPRF.PermutationIndex) (rest : List Bool)
    (wire : base.bits 0 = query request ++ rest) :
    run (recordedPublicHandler attempts) (publicInputCost request + 4 + fuel) ⟨0, base⟩ =
      (run (recordedPublicHandler attempts) fuel
        ⟨recordedPublicCore (publicInputLabel request), recordedPublicInputMemory base request rest⟩).map
          (Option.map fun result => (result.1, result.2 + (publicInputCost request + 4))) := by
  let saved := executeLinear publicHistorySave (queryInputMemory base request rest)
  have routed := recordedPublicInput_dispatch base request rest
  have parsed := queryInputBlock_continue (recordedPublicHandler attempts)
    (recordedPublicRedirect ∘ publicQueryLabels) (recordedPublicHandler_query attempts)
    base request rest wire (4 + (publicDispatchCost saved + fuel))
  change run (recordedPublicHandler attempts) _ ⟨0, base⟩ = _ at parsed
  have save := linear_continue (recordedPublicHandler attempts) publicHistorySave recordedPublicSaveLabels
    (recordedPublicHandler_save attempts) (queryInputMemory base request rest) (publicDispatchCost saved + fuel)
  change run (recordedPublicHandler attempts) (4 + (publicDispatchCost saved + fuel))
    ⟨1772, queryInputMemory base request rest⟩ = _ at save
  have dispatch := publicDispatchHost (recordedPublicHandler attempts)
    (recordedPublicCore ∘ publicDispatchLabels) (recordedPublicHandler_dispatch attempts) saved
  have dispatch' : runPrefix (recordedPublicHandler attempts) (publicDispatchCost saved) ⟨96, saved⟩ =
      PMF.pure (some (false, ⟨recordedPublicCore (publicDispatchLabel saved), publicDispatchMemory saved⟩,
        publicDispatchCost saved)) := by
    have labelsEq : (if saved.registers 10 = 4#256 then
        (recordedPublicCore ∘ publicDispatchLabels) 6
        else if saved.registers 10 &&& 1#256 = 0#256 then
          (recordedPublicCore ∘ publicDispatchLabels) 7
          else (recordedPublicCore ∘ publicDispatchLabels) 8) =
        recordedPublicCore (publicDispatchLabel saved) := by
      by_cases hash : saved.registers 10 = 4#256
      · simp [publicDispatchLabel, hash, publicDispatchLabels]
      · by_cases even : saved.registers 10 &&& 1#256 = 0#256 <;>
          simp [publicDispatchLabel, hash, even, publicDispatchLabels]
    exact dispatch.trans (by congr 5)
  have continued : run (recordedPublicHandler attempts) (publicDispatchCost saved + fuel) ⟨96, saved⟩ =
      (run (recordedPublicHandler attempts) fuel
        ⟨recordedPublicCore (publicDispatchLabel saved), publicDispatchMemory saved⟩).map
          (Option.map fun result => (result.1, result.2 + publicDispatchCost saved)) := by
    rw [run_after_prefix, dispatch', PMF.pure_bind]
  have cost : publicInputCost request + 4 + fuel =
      queryInputCost request - 1 + (4 + (publicDispatchCost saved + fuel)) := by
    have := routed.2
    change queryInputCost request - 1 + publicDispatchCost saved = _ at this
    omega
  rw [cost, parsed]
  change (run (recordedPublicHandler attempts) _ ⟨1772, queryInputMemory base request rest⟩).map _ = _
  rw [save]
  change ((run (recordedPublicHandler attempts) _ ⟨96, saved⟩).map _).map _ = _
  rw [continued]
  simp only [PMF.map_comp, Option.map_map, Function.comp_def]
  have route : publicDispatchLabel saved = publicInputLabel request := routed.1
  rw [route]
  congr 1
  funext result
  congr 1
  funext value
  congr 1
  have := routed.2
  change queryInputCost request - 1 + publicDispatchCost saved = _ at this
  change value.2 + publicDispatchCost saved + 4 + (queryInputCost request - 1) = _
  omega

end Kriterion.ArgoMAC.ArithmeticSimulator
