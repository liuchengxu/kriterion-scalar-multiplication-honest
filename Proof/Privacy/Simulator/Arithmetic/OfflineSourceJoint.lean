import Proof.Privacy.Simulator.Arithmetic.PrivateScheduleInjective
import Proof.Privacy.Simulator.Arithmetic.DrawMemory

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine Security.SimulatorSampling
noncomputable section
attribute [local irreducible] offlineSchedule samplerBatchMemory offlinePlan

private noncomputable instance : Nonempty OfflineCoin := ⟨offline.law.support_nonempty.choose⟩

/-- The complete stored word sequence identifies one offline source coin. -/
theorem offlineStored_injective (base : Memory) :
    Function.Injective (fun coin => storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin)) := by
  intro a b same
  dsimp only at same
  apply offlineSchedule_injective
  apply List.ext_getElem ((offlineSchedule.wordsLength a).trans (offlineSchedule.wordsLength b).symm)
  intro index aInside bInside
  have aFits : 0 + (offlineSchedule.words a).length ≤ 2 ^ 256 := by rw [offlineSchedule.wordsLength]; decide
  have bFits : 0 + (offlineSchedule.words b).length ≤ 2 ^ 256 := by rw [offlineSchedule.wordsLength]; decide
  rw [← storeDrawWords_get (base.registers 10) 0 base.ram (offlineSchedule.words a) index aInside aFits,
    same, storeDrawWords_get (base.registers 10) 0 base.ram (offlineSchedule.words b) index bInside bFits]

/-- This proof-only decoder identifies the private coin from its complete RAM representation. -/
def offlineMemoryCoin (base : Memory) (ram : Word → Word) : OfflineCoin :=
  Function.invFun (fun coin => storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin)) ram

/-- The proof-only decoder is an inverse on every stored source coin. -/
theorem offlineMemoryCoin_stored (base : Memory) (coin : OfflineCoin) :
    offlineMemoryCoin base (storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin)) = coin :=
  Function.leftInverse_invFun (offlineStored_injective base) coin

/-- The actual offline sampler retains the exact typed private coin law. -/
theorem offlineMemoryCoin_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (samplerBatchMemory offlinePlan attempts 838208 0 base).map (fun result => offlineMemoryCoin base result.1.ram) =
      (offline.total attempts).law := by
  have law := congrArg (PMF.map (offlineMemoryCoin base)) (offlineMemory_source attempts base)
  simp only [PMF.map_comp, Function.comp_def, offlineMemoryCoin_stored] at law
  exact law.trans (PMF.map_id _)

/-- Every supported sampler return stores the exact coin that the decoder selects. -/
theorem offlineMemoryCoin_memory [BN254.FieldCertificate] (attempts : Nat) (base final : Memory) (cost : Nat)
    (supported : (final, cost) ∈ (samplerBatchMemory offlinePlan attempts 838208 0 base).support) :
    final.ram = storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words (offlineMemoryCoin base final.ram)) := by
  have reached : final.ram ∈ ((samplerBatchMemory offlinePlan attempts 838208 0 base).map fun result => result.1.ram).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(final, cost), supported, rfl⟩
  rw [offlineMemory_source] at reached
  obtain ⟨coin, _, same⟩ := (PMF.mem_support_map_iff _ _ _).mp reached
  rw [← same, offlineMemoryCoin_stored]

/-- The joint source keeps both the actual memory charge and the typed private coin. -/
def offlineSourceJoint (attempts : Nat) (base : Memory) : PMF ((Memory × Nat) × OfflineCoin) :=
  (samplerBatchMemory offlinePlan attempts 838208 0 base).map fun result =>
    (result, offlineMemoryCoin base result.1.ram)

/-- The first joint marginal is the complete actual sampler law. -/
theorem offlineSourceJoint_machine (attempts : Nat) (base : Memory) :
    (offlineSourceJoint attempts base).map Prod.fst = samplerBatchMemory offlinePlan attempts 838208 0 base := by
  simp only [offlineSourceJoint, PMF.map_comp, Function.comp_def]
  exact PMF.map_id _

/-- The second joint marginal is the complete typed source law. -/
theorem offlineSourceJoint_source [BN254.FieldCertificate] (attempts : Nat) (base : Memory) :
    (offlineSourceJoint attempts base).map Prod.snd = (offline.total attempts).law := by
  simpa only [offlineSourceJoint, PMF.map_comp, Function.comp_def] using offlineMemoryCoin_source attempts base

/-- Every supported joint pair stores all words of its typed private coin. -/
theorem offlineSourceJoint_words [BN254.FieldCertificate] (attempts : Nat) (base final : Memory)
    (cost : Nat) (coin : OfflineCoin) (supported : ((final, cost), coin) ∈ (offlineSourceJoint attempts base).support) :
    WordsAt final.ram (base.registers 10) 0 (offlineSchedule.words coin) := by
  obtain ⟨result, member, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  cases same
  intro index inside
  calc
    final.ram _ = storeDrawWords (base.registers 10) 0 base.ram
      (offlineSchedule.words (offlineMemoryCoin base final.ram)) _ :=
        congrFun (offlineMemoryCoin_memory attempts base final cost member) _
    _ = _ := storeDrawWords_get _ _ _ _ index inside (by rw [offlineSchedule.wordsLength]; decide)

end
end Kriterion.ArgoMAC.ArithmeticSimulator
