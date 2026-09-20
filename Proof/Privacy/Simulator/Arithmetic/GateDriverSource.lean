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
