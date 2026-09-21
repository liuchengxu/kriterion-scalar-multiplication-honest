import Construction.Simulator.GateLoop
import Proof.Privacy.Simulator.Arithmetic.GateDriverCost

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Every gate keeps its exact fixed instruction table and return labels. -/
theorem gateLoop_contains {count : Nat} (plan : Vector GateCode count) (attempts : Nat)
    (fits : 1036 * count + 1 < 2 ^ 256) (index : Fin count) :
    ContainsGateDriver (gateLoop plan attempts fits) attempts plan[index] (gateLoopLabels index) := by
  intro pc normal cutoff
  have i := index.isLt
  have p := pc.isLt
  have position : 1036 * index.val + pc.val < 1036 * count := by omega
  have quotient : (1036 * index.val + pc.val) / 1036 = index.val := by omega
  have remainder : (1036 * index.val + pc.val) % 1036 = pc.val := by omega
  simp only [gateLoopLabels, if_neg normal, if_neg cutoff, gateLoop, Vector.getElem_ofFn,
    dif_pos position, remainder]
  have selected : (⟨(1036 * index.val + pc.val) / 1036, by omega⟩ : Fin count) = index := Fin.ext quotient
  exact congrArg (fun chosen : Fin count => relocate (gateLoopLabels chosen)
    ((gateDriver attempts plan[chosen]).code[pc.val]'pc.isLt)) selected

/-- The loop boundary denotes the next gate or the final normal return. -/
def gateLoopBoundary {count : Nat} (index : Nat) (within : index ≤ count) : Fin (1036 * count + 2) :=
  ⟨1036 * index, by omega⟩

/-- The host contains every loop instruction before the normal and cutoff returns. -/
def ContainsGateLoop {count : Nat} (host : Machine) (plan : Vector GateCode count) (attempts : Nat)
    (fits : 1036 * count + 1 < 2 ^ 256) (labels : Fin (1036 * count + 2) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (1036 * count + 2), pc.val < 1036 * count →
    host.code[(labels pc).val] = relocate labels ((gateLoop plan attempts fits).code[pc.val])

/-- Each gate retains its checked source law inside any host loop. -/
theorem gateLoopBlock_contains {count : Nat} (host : Machine) (plan : Vector GateCode count) (attempts : Nat)
    (fits : 1036 * count + 1 < 2 ^ 256) (labels : Fin (1036 * count + 2) → Fin (host.size + 1))
    (present : ContainsGateLoop host plan attempts fits labels) (index : Fin count) :
    ContainsGateDriver host attempts plan[index] (labels ∘ gateLoopLabels index) := by
  intro pc normal cutoff
  have inside : (gateLoopLabels index pc).val < 1036 * count := by
    simp only [gateLoopLabels, if_neg normal, if_neg cutoff]
    have i := index.isLt
    have p := pc.isLt
    omega
  exact (present _ inside).trans
    ((congrArg (relocate labels) (gateLoop_contains plan attempts fits index pc normal cutoff)).trans
      (relocate_comp (gateLoopLabels index) labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The host contains each fixed-oracle loop instruction. -/
def ContainsLazyGateLoop {count : Nat} (host : Simulator) (plan : Vector GateCode count)
    (labels : Fin (1036 * count + 2) → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin (1036 * count + 2), pc.val < 1036 * count →
    host.code[(labels pc).val] = relocateSimulator labels (lazyGateLoopCode plan)[pc.val]

/-- Each gate retains its instruction table inside the loop. -/
theorem lazyGateLoop_contains {count : Nat} (plan : Vector GateCode count)
    (index : Fin count) (pc : Fin 1036) (inside : pc.val < 1034) :
    (lazyGateLoopCode plan)[(gateLoopLabels index pc).val] =
      relocateSimulator (gateLoopLabels index) (lazyGateInstruction plan[index] pc) := by
  have normal : pc ≠ 1034 := by intro same; subst pc; contradiction
  have cutoff : pc ≠ 1035 := by intro same; subst pc; contradiction
  have i := index.isLt
  have position : 1036 * index.val + pc.val < 1036 * count := by omega
  have quotient : (1036 * index.val + pc.val) / 1036 = index.val := by omega
  have remainder : (1036 * index.val + pc.val) % 1036 = pc.val := by omega
  simp only [gateLoopLabels, if_neg normal, if_neg cutoff, lazyGateLoopCode,
    Vector.getElem_ofFn, dif_pos position]
  have selected : (⟨(1036 * index.val + pc.val) / 1036, by omega⟩ : Fin count) = index := Fin.ext quotient
  have cursor : (⟨(1036 * index.val + pc.val) % 1036, by omega⟩ : Fin 1036) = pc := Fin.ext remainder
  exact congrArg₂ (fun (chosen : Fin count) (cursor : Fin 1036) =>
    relocateSimulator (gateLoopLabels chosen) (lazyGateInstruction plan[chosen] cursor)) selected cursor

/-- Each gate uses the host continuation at its normal return. -/
theorem lazyGateLoopBlock_contains {count : Nat} (host : Simulator) (plan : Vector GateCode count)
    (labels : Fin (1036 * count + 2) → Fin (host.size + 1))
    (present : ContainsLazyGateLoop host plan labels) (index : Fin count) :
    ContainsLazyGateDriver host plan[index] (labels ∘ gateLoopLabels index) := by
  intro pc inside
  have normal : pc ≠ 1034 := by intro same; subst pc; contradiction
  have cutoff : pc ≠ 1035 := by intro same; subst pc; contradiction
  have position : (gateLoopLabels index pc).val < 1036 * count := by
    simp only [gateLoopLabels, if_neg normal, if_neg cutoff]
    have i := index.isLt
    omega
  apply (present _ position).trans
  apply (congrArg (relocateSimulator labels) (lazyGateLoop_contains plan index pc inside)).trans
  cases lazyGateInstruction plan[index] pc <;> simp [relocateSimulator, relocate_comp]

end Kriterion.ArgoMAC.ArithmeticSimulator
