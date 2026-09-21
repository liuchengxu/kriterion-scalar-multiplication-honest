import Proof.Privacy.Simulator.Arithmetic.GateDriverCompose

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The normal source restores the saved caller pointers. -/
noncomputable def gateRestoreSamples (memory : Memory) : PMF (Fin 1036 × Memory × Nat) :=
  PMF.pure (1034, executeLinear gateDirectiveRestore memory, 10)

noncomputable def gateThirdSamples (attempts : Nat) (gate : GateCode) (memory : Memory) :
    PMF (Fin 1036 × Memory × Nat) :=
  (gateDriverSlotSamples attempts gate 2 memory).bind (gateDriverAfterSlot gateRestoreSamples)

/-- The source selects the third slot from the saved slot count. -/
noncomputable def gateTestSamples (attempts : Nat) (gate : GateCode) (memory : Memory) :
    PMF (Fin 1036 × Memory × Nat) :=
  let tested := executeLinear gateDriverTest memory
  (if tested.registers 1 = 0 then gateThirdSamples attempts gate tested else gateRestoreSamples tested).map
    fun result => (result.1, result.2.1, 5 + result.2.2)

noncomputable def gateSecondSamples (attempts : Nat) (gate : GateCode) (memory : Memory) :
    PMF (Fin 1036 × Memory × Nat) :=
  (gateDriverSlotSamples attempts gate 1 memory).bind (gateDriverAfterSlot (gateTestSamples attempts gate))

noncomputable def gateBodySamples (attempts : Nat) (gate : GateCode) (memory : Memory) :
    PMF (Fin 1036 × Memory × Nat) :=
  (gateDriverSlotSamples attempts gate 0 memory).bind (gateDriverAfterSlot (gateSecondSamples attempts gate))

/-- The complete gate source includes its deterministic preparation charge. -/
noncomputable def gateDriverSamples (attempts : Nat) (gate : GateCode) (memory : Memory) :
    PMF (Fin 1036 × Memory × Nat) :=
  (gateBodySamples attempts gate (gateDriverPrepared gate memory)).map
    fun result => (result.1, result.2.1, gateDriverPrefixCost gate memory + result.2.2)

def GateTestReady (attempts limit : Nat) (gate : GateCode) (memory : Memory) : Prop :=
  (executeLinear gateDriverTest memory).registers 1 = 0 →
    GateDriverSlotReady attempts limit gate 2 (executeLinear gateDriverTest memory)

def GateSecondReady (attempts limit : Nat) (gate : GateCode) (memory : Memory) : Prop :=
  GateDriverSlotReady attempts limit gate 1 memory ∧
  ∀ result ∈ (gateDriverSlotSamples attempts gate 1 memory).support, result.1 = 300 →
    GateTestReady attempts limit gate result.2.1

def GateBodyReady (attempts limit : Nat) (gate : GateCode) (memory : Memory) : Prop :=
  GateDriverSlotReady attempts limit gate 0 memory ∧
  ∀ result ∈ (gateDriverSlotSamples attempts gate 0 memory).support, result.1 = 300 →
    GateSecondReady attempts limit gate result.2.1

def GateDriverReady (attempts limit : Nat) (gate : GateCode) (memory : Memory) : Prop :=
  GateBodyReady attempts limit gate (gateDriverPrepared gate memory)

def gateSlotBudget (attempts limit : Nat) : Nat := 8 + checkedSlotRunBudget attempts limit

def gateDriverRunBudget (attempts limit : Nat) : Nat := 3 * gateSlotBudget attempts limit + 84

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The slot source uses the same private loads and the fixed fresh-pair operation. -/
noncomputable def lazyGateSlot {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (gate : GateCode) (slot : Fin 3)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) :
    Option (Memory × LazyOracle.State FixedIndex EncIndex) :=
  let ready := executeLinear (gateSlotLoad (gate.oracle slot) slot) memory
  match queryFromRegisters 0 (ready.registers 9) (ready.registers 8) with
  | none => none
  | some request => (LazyOracle.program request
      (answerFromWords request (ready.ram (14#256)) (ready.registers 2)) oracle).map fun updated =>
      ({ ready with registers := Function.update (Function.update ready.registers 0 14) 1 (ready.ram (14#256)) }, updated)

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

set_option backward.isDefEq.respectTransparency false in
/-- The slot pays for eight private loads and three fresh-program instructions. -/
theorem lazyGateSlot_continue [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (slot : Fin 3) (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    host.run (11 + fuel) ⟨labels (gateDriverSlotLoadLabels slot 0), memory⟩ oracle =
      match lazyGateSlot gate slot memory oracle with
      | none => PMF.pure none
      | some result => (host.run fuel ⟨labels (lazyGateProgramLabels slot 3), result.1⟩ result.2).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 11)) := by
  let ready := executeLinear (gateSlotLoad (gate.oracle slot) slot) memory
  have loads : ContainsLinear host.arithmetic (gateSlotLoad (gate.oracle slot) slot)
      (labels ∘ gateDriverSlotLoadLabels slot) := by
    fin_cases slot
    · exact lazyGateDriverBlock_load0 host gate labels present
    · exact lazyGateDriverBlock_load1 host gate labels present
    · exact lazyGateDriverBlock_load2 host gate labels present
  have loaded := linear_continue host.arithmetic (gateSlotLoad (gate.oracle slot) slot)
    (labels ∘ gateDriverSlotLoadLabels slot) loads memory (3 + fuel)
  have same : gateDriverSlotLoadLabels slot 8 = lazyGateProgramLabels slot 0 := by
    fin_cases slot <;> rfl
  change run host.arithmetic (8 + (3 + fuel)) ⟨labels (gateDriverSlotLoadLabels slot 0), memory⟩ =
    (run host.arithmetic (3 + fuel) ⟨labels (gateDriverSlotLoadLabels slot 8), ready⟩).map _ at loaded
  rw [same] at loaded
  have moved := Simulator.run_prefix host 8 (3 + fuel) _ _ oracle loaded
  have code := lazyGateDriverBlock_program host gate labels present slot
  have programmed := simulator_program_slot host (labels ∘ lazyGateProgramLabels slot)
    code.1 code.2.1 code.2.2 ready oracle fuel
  simp only [Function.comp_apply] at programmed
  rw [show 11 + fuel = 8 + (3 + fuel) by omega, moved, programmed]
  unfold lazyGateSlot
  change _ = match (match queryFromRegisters 0 (ready.registers 9) (ready.registers 8) with
    | none => none
    | some request => (LazyOracle.program request
        (answerFromWords request (ready.ram (14#256)) (ready.registers 2)) oracle).map fun updated =>
        ({ ready with registers := Function.update (Function.update ready.registers 0 14) 1 (ready.ram (14#256)) }, updated)) with
      | none => PMF.pure none
      | some result => _
  cases decoded : queryFromRegisters (FixedIndex := FixedIndex) (EncIndex := EncIndex)
    0 (ready.registers 9) (ready.registers 8) with
  | none => simp [decoded, PMF.pure_map]
  | some request =>
      cases installed : LazyOracle.program request
        (answerFromWords request (ready.ram (14#256)) (ready.registers 2)) oracle <;>
        simp [decoded, installed, PMF.pure_map, PMF.map_comp, Option.map_map,
          Function.comp_def, Nat.add_assoc]

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The gate source keeps only private arithmetic and fresh oracle programming. -/
noncomputable def lazyGateDriverResult {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (gate : GateCode)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) :
    Option (Memory × LazyOracle.State FixedIndex EncIndex × Nat) := do
  let first ← lazyGateSlot gate 0 (gateDriverPrepared gate memory) oracle
  let second ← lazyGateSlot gate 1 first.1 first.2
  let tested := executeLinear gateDriverTest second.1
  if tested.registers 1 = 0 then
    let third ← lazyGateSlot gate 2 tested second.2
    pure (executeLinear gateDirectiveRestore third.1, third.2, gateDriverPrefixCost gate memory + 48)
  else
    pure (executeLinear gateDirectiveRestore tested, second.2, gateDriverPrefixCost gate memory + 37)

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- The gate restores its caller pointers with ten charged private instructions. -/
theorem lazyGateRestore_continue [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    host.run (10 + fuel) ⟨labels 1024, memory⟩ oracle =
      (host.run fuel ⟨labels 1034, executeLinear gateDirectiveRestore memory⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 10)) := by
  apply Simulator.run_prefix host 10 fuel _ _ oracle
  exact linear_continue host.arithmetic gateDirectiveRestore (labels ∘ gateDriverRestoreLabels)
    (lazyGateDriverBlock_restore host gate labels present) memory fuel

set_option backward.isDefEq.respectTransparency false in
/-- The slot-count test costs five private instructions. -/
theorem lazyGateTest_continue [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    let tested := executeLinear gateDriverTest memory
    host.run (5 + fuel) ⟨labels 706, memory⟩ oracle =
      (host.run fuel ⟨if tested.registers 1 = 0 then labels 711 else labels 1024, tested⟩ oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + 5)) := by
  dsimp only
  apply Simulator.run_prefix host 5 fuel _ _ oracle
  have testedBlock := linear_continue host.arithmetic gateDriverTest (labels ∘ gateDriverTestLabels)
    (lazyGateDriverBlock_test host gate labels present) memory (fuel + 1)
  change run host.arithmetic (4 + (fuel + 1)) ⟨labels 706, memory⟩ =
    (run host.arithmetic (fuel + 1) ⟨labels 710, executeLinear gateDriverTest memory⟩).map _ at testedBlock
  have selected : host.code[(labels 710).val] = .compute (.branch 1 (labels 711) (labels 1024)) := by
    simpa [lazyGateInstruction, gateDriver, relocateSimulator, relocate] using present 710 (by decide)
  have branch : host.arithmetic.code[(labels 710).val] = .branch 1 (labels 711) (labels 1024) := by
    simp [Simulator.arithmetic, selected]
  rw [show 5 + fuel = 4 + (fuel + 1) by omega, testedBlock, run]
  simp [step, branch, PMF.pure_bind, PMF.map_comp, Option.map_map, Function.comp_def, Nat.add_assoc,
    show gateDriverTest.length = 4 from rfl]

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

/-- A successful slot changes only its target scratch cell and temporary registers. -/
theorem lazyGateSlot_memory {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (gate : GateCode) (slot : Fin 3)
    (memory result : Memory) (oracle updated : LazyOracle.State FixedIndex EncIndex)
    (success : lazyGateSlot gate slot memory oracle = some (result, updated)) :
    result.ram = Function.update memory.ram 14 (memory.ram (BitVec.ofNat 256 (17 + slot.val))) ∧
      result.bits = memory.bits ∧
      ∀ register : Register, 11 ≤ register.val → result.registers register = memory.registers register := by
  unfold lazyGateSlot at success
  dsimp only at success
  split at success
  · simp at success
  · obtain ⟨next, _, equal⟩ := Option.map_eq_some_iff.mp success
    cases equal
    have load := gateSlotLoad_values (gate.oracle slot) slot memory
    refine ⟨load.2.2.2.1, load.2.2.2.2, ?_⟩
    intro register large
    have first : register ≠ 0 := by intro same; subst register; simp at large
    have second : register ≠ 1 := by intro same; subst register; simp at large
    simp only [Function.update_of_ne second, Function.update_of_ne first]
    exact gateSlotLoad_caller (gate.oracle slot) slot memory register large

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography Cryptography.BoundedMachine

set_option backward.isDefEq.respectTransparency false in
theorem lazyGateDriverBlock_continue [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (host : Simulator) (gate : GateCode)
    (labels : Fin 1036 → Fin (host.size + 1)) (present : ContainsLazyGateDriver host gate labels)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (fuel : Nat) :
    host.run (117 + fuel) ⟨labels 0, memory⟩ oracle =
      match lazyGateDriverResult gate memory oracle with
      | none => PMF.pure none
      | some result => (host.run (117 + fuel - result.2.2) ⟨labels 1034, result.1⟩ result.2.1).map
          (Option.map fun final => (final.1, final.2.1, final.2.2 + result.2.2)) := by
  have bounded := gateDriverPrefixCost_bound gate memory
  let cost := gateDriverPrefixCost gate memory
  let ready := gateDriverPrepared gate memory
  have enough : cost ≤ 117 + fuel := by dsimp [cost]; omega
  have prelude := lazyGateDriverBlock_prefix host gate labels present memory oracle (117 + fuel - cost)
  rw [show gateDriverPrefixCost gate memory + (117 + fuel - cost) = 117 + fuel by dsimp [cost]; omega] at prelude
  rw [prelude]
  have firstRun := lazyGateSlot_continue host gate labels present 0 ready oracle (106 + fuel - cost)
  change host.run (11 + (106 + fuel - cost)) ⟨labels 80, ready⟩ oracle = _ at firstRun
  rw [show 117 + fuel - cost = 11 + (106 + fuel - cost) by dsimp [cost]; omega, firstRun]
  unfold lazyGateDriverResult
  change _ = match (lazyGateSlot gate 0 ready oracle).bind (fun first =>
    (lazyGateSlot gate 1 first.1 first.2).bind (fun second =>
      let tested := executeLinear gateDriverTest second.1
      if tested.registers 1 = 0 then
        (lazyGateSlot gate 2 tested second.2).bind (fun third => some
          (executeLinear gateDirectiveRestore third.1, third.2, cost + 48))
      else some (executeLinear gateDirectiveRestore tested, second.2, cost + 37))) with
      | none => PMF.pure none
      | some result => _
  cases firstEq : lazyGateSlot gate 0 ready oracle with
  | none => simp [firstEq, PMF.pure_map]
  | some first =>
    simp only [firstEq, Option.bind_some, show lazyGateProgramLabels 0 3 = 393 from rfl]
    have secondRun := lazyGateSlot_continue host gate labels present 1 first.1 first.2 (95 + fuel - cost)
    change host.run (11 + (95 + fuel - cost)) ⟨labels 393, first.1⟩ first.2 = _ at secondRun
    rw [show 106 + fuel - cost = 11 + (95 + fuel - cost) by dsimp [cost]; omega, secondRun]
    cases secondEq : lazyGateSlot gate 1 first.1 first.2 with
    | none => simp [secondEq, PMF.pure_map]
    | some second =>
      simp only [secondEq, Option.bind_some, show lazyGateProgramLabels 1 3 = 706 from rfl]
      have testedRun := lazyGateTest_continue host gate labels present second.1 second.2 (90 + fuel - cost)
      rw [show 95 + fuel - cost = 5 + (90 + fuel - cost) by dsimp [cost]; omega, testedRun]
      let tested := executeLinear gateDriverTest second.1
      by_cases takeThird : tested.registers 1 = 0
      · simp only [show (executeLinear gateDriverTest second.1).registers 1 = 0 from takeThird, if_pos]
        have thirdRun := lazyGateSlot_continue host gate labels present 2 tested second.2 (79 + fuel - cost)
        change host.run (11 + (79 + fuel - cost)) ⟨labels 711, tested⟩ second.2 = _ at thirdRun
        rw [show 90 + fuel - cost = 11 + (79 + fuel - cost) by dsimp [cost]; omega, thirdRun]
        cases thirdEq : lazyGateSlot gate 2 tested second.2 with
        | none => simp [thirdEq, tested, PMF.pure_map]
        | some third =>
          simp only [thirdEq, Option.bind_some, show lazyGateProgramLabels 2 3 = 1024 from rfl]
          rw [show 79 + fuel - cost = 10 + (69 + fuel - cost) by dsimp [cost]; omega,
            lazyGateRestore_continue host gate labels present third.1 third.2 (69 + fuel - cost)]
          have remaining : 117 + fuel - (cost + 48) = 69 + fuel - cost := by omega
          rw [remaining]
          simp [PMF.map_comp, Option.map_map, Function.comp_def, cost,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      · simp only [show ¬ (executeLinear gateDriverTest second.1).registers 1 = 0 from takeThird, if_false]
        rw [show 90 + fuel - cost = 10 + (80 + fuel - cost) by dsimp [cost]; omega,
          lazyGateRestore_continue host gate labels present tested second.2 (80 + fuel - cost)]
        have remaining : 117 + fuel - (cost + 37) = 80 + fuel - cost := by omega
        rw [remaining]
        simp [PMF.map_comp, Option.map_map, Function.comp_def, cost, ready, tested,
          remaining, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


/-- Each successful gate uses at most 117 instructions. -/
theorem lazyGateDriverResult_cost {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (gate : GateCode)
    (memory : Memory) (oracle : LazyOracle.State FixedIndex EncIndex) (result)
    (success : lazyGateDriverResult gate memory oracle = some result) : result.2.2 ≤ 117 := by
  have bound := gateDriverPrefixCost_bound gate memory
  unfold lazyGateDriverResult at success
  dsimp only [Bind.bind] at success
  simp only [Option.bind_eq_some_iff] at success
  obtain ⟨first, _, second, _, success⟩ := success
  split at success
  · obtain ⟨third, _, success⟩ := Option.bind_eq_some_iff.mp success
    cases success
    dsimp only
    omega
  · cases success
    dsimp only
    omega

end Kriterion.ArgoMAC.ArithmeticSimulator
