import Proof.Privacy.Simulator.Arithmetic.HistoryFreshMemory
import Proof.Privacy.Simulator.Arithmetic.ByteOutputBlock
import Proof.Privacy.Simulator.Arithmetic.TrialBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The freshness machine contains its complete domain loader. -/
theorem historyFresh_domainLoad : ContainsLinear historyFresh historyDomainLoad historyDomainLoadLabels := by
  intro index inside
  have bound : index < 5 := inside
  simp only [historyDomainLoadLabels, dif_pos bound, historyFresh, Vector.getElem_ofFn, dif_pos bound]

/-- The freshness machine contains its complete range loader. -/
theorem historyFresh_rangeLoad : ContainsLinear historyFresh historyRangeLoad historyRangeLoadLabels := by
  intro index inside
  have bound : index < 7 := inside
  simp only [historyRangeLoadLabels, dif_pos bound, historyFresh, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_pos (by omega)]
  simp only [Nat.add_sub_cancel_left]

/-- The freshness machine contains its domain lookup. -/
theorem historyFresh_domain : ContainsTableLookup historyFresh historyDomainLabels := by
  intro pc active
  simp only [historyDomainLabels, if_neg active, historyFresh, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  rfl

/-- The freshness machine contains its range lookup. -/
theorem historyFresh_range : ContainsTableLookup historyFresh historyRangeLabels := by
  intro pc active
  simp only [historyRangeLabels, if_neg active, historyFresh, Vector.getElem_ofFn]
  rw [dif_neg (by omega), dif_neg (by omega), dif_neg (by omega),
    dif_pos (by have bound := pc.isLt; omega)]
  simp only [Nat.add_sub_cancel_left]
  rfl

/-- A host contains all freshness instructions before the common return. -/
def ContainsHistoryFresh (host : Machine) (labels : Fin 43 → Fin (host.size + 1)) : Prop :=
  ∀ pc : Fin 43, pc ≠ 41 → host.code[(labels pc).val] =
    relocate labels (historyFresh.code[pc.val]'(by exact pc.isLt))

theorem historyFreshBlock_domainLoad (host : Machine) (labels : Fin 43 → Fin (host.size + 1))
    (present : ContainsHistoryFresh host labels) :
    ContainsLinear host historyDomainLoad (labels ∘ historyDomainLoadLabels) := by
  intro index inside
  have bound : index < 5 := inside
  have mapped : historyDomainLoadLabels index ≠ 41 := by
    intro same
    have vals := congrArg Fin.val same
    simp only [historyDomainLoadLabels, dif_pos bound] at vals
    change index = 41 at vals
    omega
  exact (present _ mapped).trans ((congrArg (relocate labels) (historyFresh_domainLoad index inside)).trans
    (LinearInstruction.relocate_emit labels _ _))

theorem historyFreshBlock_rangeLoad (host : Machine) (labels : Fin 43 → Fin (host.size + 1))
    (present : ContainsHistoryFresh host labels) :
    ContainsLinear host historyRangeLoad (labels ∘ historyRangeLoadLabels) := by
  intro index inside
  have bound : index < 7 := inside
  have mapped : historyRangeLoadLabels index ≠ 41 := by
    intro same
    have vals := congrArg Fin.val same
    simp only [historyRangeLoadLabels, dif_pos bound] at vals
    change 19 + index = 41 at vals
    omega
  exact (present _ mapped).trans ((congrArg (relocate labels) (historyFresh_rangeLoad index inside)).trans
    (LinearInstruction.relocate_emit labels _ _))

theorem historyFreshBlock_domain (host : Machine) (labels : Fin 43 → Fin (host.size + 1))
    (present : ContainsHistoryFresh host labels) : ContainsTableLookup host (labels ∘ historyDomainLabels) := by
  intro pc active
  have mapped : historyDomainLabels pc ≠ 41 := by
    intro same
    have vals := congrArg Fin.val same
    simp only [historyDomainLabels, if_neg active] at vals
    change 5 + pc.val = 41 at vals
    have bound := pc.isLt
    omega
  exact (present _ mapped).trans ((congrArg (relocate labels) (historyFresh_domain pc active)).trans
    (relocate_comp historyDomainLabels labels _))

theorem historyFreshBlock_range (host : Machine) (labels : Fin 43 → Fin (host.size + 1))
    (present : ContainsHistoryFresh host labels) : ContainsTableLookup host (labels ∘ historyRangeLabels) := by
  intro pc active
  have mapped : historyRangeLabels pc ≠ 41 := by
    intro same
    have vals := congrArg Fin.val same
    simp only [historyRangeLabels, if_neg active] at vals
    change 26 + pc.val = 41 at vals
    have bound := pc.isLt
    omega
  exact (present _ mapped).trans ((congrArg (relocate labels) (historyFresh_range pc active)).trans
    (relocate_comp historyRangeLabels labels _))

end Kriterion.ArgoMAC.ArithmeticSimulator
