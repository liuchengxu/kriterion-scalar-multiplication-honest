import Proof.Privacy.Simulator.Arithmetic.GateSlotPrivate
import Proof.Privacy.Simulator.Arithmetic.GateDriverSource
import Proof.Privacy.Simulator.Arithmetic.CutoffMapBind

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine Security.OperationalOracle Security.SharedSimulatorMachine
noncomputable section

abbrev GateJointResult := (Fin 1036 × Memory × Nat) × SharedOracleSource

/-- The normal coupled return restores the saved caller pointers. -/
def gateRestoreCoupled (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  PMF.pure (some ((1034, executeLinear gateDirectiveRestore memory, 10), state))

/-- A successful slot continues with its exact instruction count. -/
def gateContinueCoupled (attempts : Nat) (gate : GateCode) (slot : Fin 3) (command : SharedCommand)
    (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  bindCutoff (gateDriverSlotCoupledSamples attempts gate slot memory state command) fun result =>
    (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2))

/-- The third coupled slot returns through the normal caller restoration. -/
def gateThirdCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 2 (commands 2) gateRestoreCoupled memory state

/-- The coupled test selects the same saved third-slot flag as the machine. -/
def gateTestCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  let tested := executeLinear gateDriverTest memory
  (if tested.registers 1 = 0 then gateThirdCoupled attempts gate commands tested state else gateRestoreCoupled tested state).map
    (Option.map fun result => ((result.1.1, result.1.2.1, 5 + result.1.2.2), result.2))

/-- The second coupled slot reaches the saved slot-count test. -/
def gateSecondCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 1 (commands 1) (gateTestCoupled attempts gate commands) memory state

/-- The coupled body executes both required slots and the optional third slot. -/
def gateBodyCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  gateContinueCoupled attempts gate 0 (commands 0) (gateSecondCoupled attempts gate commands) memory state

/-- The complete joint driver charges its deterministic preparation instructions. -/
def gateDriverCoupled (attempts : Nat) (gate : GateCode) (commands : Fin 3 → SharedCommand)
    (memory : Memory) (state : SharedOracleSource) : PMF (Option GateJointResult) :=
  (gateBodyCoupled attempts gate commands (gateDriverPrepared gate memory) state).map
    (Option.map fun result => ((result.1.1, result.1.2.1, gateDriverPrefixCost gate memory + result.1.2.2), result.2))

/-- The source marginal composes each successful slot with its typed continuation. -/
theorem gateContinueCoupled_source [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (command : SharedCommand) (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (target : SharedOracleSource → PMF (Option (Unit × SharedOracleSource)))
    (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110)
    (law : ∀ result updated, some ((), (result, updated)) ∈
      (gateDriverSlotCoupledSamples attempts gate slot memory state command).support →
      (next result.2.1 updated).map (Option.map fun tail => ((), tail.2)) = target updated) :
    (gateContinueCoupled attempts gate slot command next memory state).map (Option.map fun result => ((), result.2)) =
      bindCutoff (sharedSourceCutoff attempts (.inl (.program command)) state) (fun result => target result.2) := by
  unfold gateContinueCoupled
  have projected := cutoff_map_bind (gateDriverSlotCoupledSamples attempts gate slot memory state command)
    (fun result => (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2)))
    (fun result => (result.1, result.2.2)) (fun result => ((), result.2))
    (fun result => target result.2) (by
      rintro ⟨value, result, updated⟩ supported
      cases value
      simpa only [PMF.map_comp, Option.map_map, Function.comp_def] using law result updated supported)
  rw [projected]
  congr 1
  have base := represented.counts.1 (sharedPhysicalIndex (.inl command.1))
  exact gateDriverSlotCoupledSamples_source attempts gate slot memory state command represented.family represented.capacity
    stored.index stored.operand (by omega)

/-- The machine marginal composes each accepted slot with its actual continuation. -/
theorem gateContinueCoupled_machine [BN254.FieldCertificate] (attempts limit : Nat) (gate : GateCode) (slot : Fin 3)
    (command : SharedCommand) (next : Memory → SharedOracleSource → PMF (Option GateJointResult))
    (target : Memory → PMF (Fin 1036 × Memory × Nat))
    (memory : Memory) (state : SharedOracleSource)
    (represented : SharedSourceMemory memory state limit) (stored : GateCommandMemory gate slot memory command)
    (room : 256 + 2 * (limit + 1) < 2 ^ 110) (attemptFits : attempts < 2 ^ 256)
    (law : ∀ result updated, some ((), (result, updated)) ∈
      (gateDriverSlotCoupledSamples attempts gate slot memory state command).support →
      (next result.2.1 updated).map (Option.map Prod.fst) =
        (target result.2.1).map (fun tail => if tail.1 = 1035 then none else some tail)) :
    (gateContinueCoupled attempts gate slot command next memory state).map (Option.map Prod.fst) =
      ((gateDriverSlotSamples attempts gate slot memory).bind (gateDriverAfterSlot target)).map
        (fun result => if result.1 = 1035 then none else some result) := by
  let charged (result : Fin 305 × Memory × Nat) := (target result.2.1).map
    (fun tail => if tail.1 = 1035 then none else some (tail.1, tail.2.1, result.2.2 + tail.2.2))
  have projected := cutoff_map_bind (gateDriverSlotCoupledSamples attempts gate slot memory state command)
    (fun result => (next result.2.1.2.1 result.2.2).map (Option.map fun tail =>
      ((tail.1.1, tail.1.2.1, result.2.1.2.2 + tail.1.2.2), tail.2)))
    (fun result => (result.1, result.2.1)) Prod.fst
    (fun result => charged result.2) (by
      rintro ⟨value, result, updated⟩ supported
      cases value
      have mapped := congrArg (PMF.map (Option.map fun tail : Fin 1036 × Memory × Nat =>
        (tail.1, tail.2.1, result.2.2 + tail.2.2))) (law result updated supported)
      simp only [PMF.map_comp, Option.map_map, Function.comp_def] at mapped ⊢
      rw [mapped]
      apply congrArg (fun f => PMF.map f (target result.2.1))
      funext tail
      split <;> rfl)
  change (bindCutoff _ _).map _ = _
  rw [projected, gateDriverSlotCoupledSamples_machine attempts gate slot memory state command represented.family
    represented.capacity represented.history stored.index stored.operand stored.target (represented.historyFits room)]
  simp only [bindCutoff, PMF.bind_map, PMF.map_bind]
  apply Security.ThreePhase.bind_eq_on_support
  intro result supported
  have labels := (gateDriverSlotSamples_cost attempts limit gate slot memory result attemptFits
    (gateDriverSlotReady_of_source attempts limit gate slot memory state command represented stored room) supported).2
  rcases labels with normal | failed
  · simp only [normal, show (300 : Fin 305) ≠ 304 by decide, ↓reduceIte, gateDriverAfterSlot, PMF.map_comp, Function.comp_def]
    rfl
  · simp only [failed, ↓reduceIte, gateDriverAfterSlot, show (304 : Fin 305) ≠ 300 by decide, PMF.pure_map, Function.comp_def]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
