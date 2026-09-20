import Proof.Privacy.Simulator.Arithmetic.OnlineInputCode

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- Each parsed word updates one cell in the online input record. -/
def onlineReadStored (base : Memory) (width value : Nat) (offset : Word)
    (rest : List Bool) : Memory :=
  onlineStored offset (decodedInput base width value rest)

/-- Each input block reads one word and stores it before it returns. -/
theorem onlineInput_readStore [BN254.FieldCertificate] (width value : Nat)
    (readLabels : Fin 15 → Fin 98) (storeLabels : Nat → Fin 98) (offset : Word)
    (reader : ContainsWordInput onlineInput width readLabels)
    (writer : ContainsLinear onlineInput (onlineInputStore offset) storeLabels)
    (joined : readLabels 14 = storeLabels 0) (base : Memory) (rest : List Bool)
    (wire : base.bits 0 = bits width value ++ rest) (fits : width ≤ 256) :
    runPrefix onlineInput (7 * width + 9) ⟨readLabels 0, base⟩ =
      PMF.pure (some (false, ⟨storeLabels 3,
        onlineReadStored base width value offset rest⟩, 7 * width + 9)) := by
  have read := decodedInputHost_prefix onlineInput width value readLabels reader base rest wire fits
  have write := linear_prefix onlineInput (onlineInputStore offset) storeLabels writer
    (decodedInput base width value rest)
  rw [onlineInputStore_memory] at write
  change runPrefix onlineInput 3 ⟨storeLabels 0, decodedInput base width value rest⟩ = _ at write
  rw [show 7 * width + 9 = (7 * width + 6) + 3 by omega, prefix_add, read, PMF.pure_bind]
  dsimp only
  rw [joined, write]
  simp [onlineReadStored, onlineInputStore, PMF.pure_map, Nat.add_comm]

/-- The common prefix retains both input coordinates and the output tag. -/
def onlineTaggedMemory (base : Memory) (x y tag : Nat) (rest : List Bool) : Memory :=
  let first := onlineReadStored base 254 x 0 (bits 254 y ++ bits 2 tag ++ rest)
  let second := onlineReadStored first 254 y 1 (bits 2 tag ++ rest)
  onlineReadStored second 2 tag 2 rest

/-- The common prefix consumes two coordinates and the output tag. -/
theorem onlineInput_taggedPrefix [BN254.FieldCertificate] (base : Memory)
    (x y tag : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 tag ++ rest) :
    runPrefix onlineInput 3597 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨51, onlineTaggedMemory base x y tag rest⟩, 3597)) := by
  let first := onlineReadStored base 254 x 0 (bits 254 y ++ bits 2 tag ++ rest)
  let second := onlineReadStored first 254 y 1 (bits 2 tag ++ rest)
  have readX := onlineInput_readStore 254 x (onlineInputLabels 0 14) (onlineStoreLabels 14 17) 0
    onlineInput_blocks.1 onlineInput_stores.1 rfl base _ wire (by decide)
  change runPrefix onlineInput 1787 ⟨0, base⟩ =
    PMF.pure (some (false, ⟨17, first⟩, 1787)) at readX
  have readY := onlineInput_readStore 254 y (onlineInputLabels 17 31) (onlineStoreLabels 31 34) 1
    onlineInput_blocks.2.1 onlineInput_stores.2.1 rfl first _ rfl (by decide)
  change runPrefix onlineInput 1787 ⟨17, first⟩ =
    PMF.pure (some (false, ⟨34, second⟩, 1787)) at readY
  have readTag := onlineInput_readStore 2 tag (onlineInputLabels 34 48) (onlineStoreLabels 48 51) 2
    onlineInput_blocks.2.2.1 onlineInput_stores.2.2.1 rfl second rest rfl (by decide)
  change runPrefix onlineInput 23 ⟨34, second⟩ =
    PMF.pure (some (false, ⟨51, onlineReadStored second 2 tag 2 rest⟩, 23)) at readTag
  change runPrefix onlineInput (1787 + (1787 + 23)) ⟨0, base⟩ = _
  rw [prefix_add, readX, PMF.pure_bind]
  dsimp only
  rw [prefix_add, readY, PMF.pure_bind]
  dsimp only
  rw [readTag]
  simp [PMF.pure_map, onlineTaggedMemory, first, second, onlineReadStored]

/-- The affine path retains all five input words. -/
def onlineAffineMemory (base : Memory) (x y outX outY : Nat) (rest : List Bool) : Memory :=
  let tagged := onlineTaggedMemory base x y 1 (bits 254 outX ++ bits 254 outY ++ rest)
  let first := onlineReadStored (onlineBranchMemory tagged) 254 outX 3 (bits 254 outY ++ rest)
  onlineReadStored first 254 outY 4 rest

/-- The affine path returns after it stores both output coordinates. -/
theorem onlineInput_affinePrefix [BN254.FieldCertificate] (base : Memory)
    (x y outX outY : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 1 ++
      bits 254 outX ++ bits 254 outY ++ rest) :
    runPrefix onlineInput 7174 ⟨0, base⟩ =
      PMF.pure (some (false, ⟨97, onlineAffineMemory base x y outX outY rest⟩, 7174)) := by
  let tagged := onlineTaggedMemory base x y 1 (bits 254 outX ++ bits 254 outY ++ rest)
  let first := onlineReadStored (onlineBranchMemory tagged) 254 outX 3 (bits 254 outY ++ rest)
  have readTag := onlineInput_taggedPrefix base x y 1 (bits 254 outX ++ bits 254 outY ++ rest)
    (by simpa only [List.append_assoc] using wire)
  change runPrefix onlineInput 3597 ⟨0, base⟩ =
    PMF.pure (some (false, ⟨51, tagged⟩, 3597)) at readTag
  have tagValue : tagged.registers 0 = 1 := by
    simp [tagged, onlineTaggedMemory, onlineReadStored, onlineStored, decodedInput_values]
  have branch := onlineInput_branch tagged
  rw [tagValue, if_pos rfl] at branch
  have readX := onlineInput_readStore 254 outX (onlineInputLabels 54 68) (onlineStoreLabels 68 71) 3
    onlineInput_blocks.2.2.2.1 onlineInput_stores.2.2.2.1 rfl (onlineBranchMemory tagged) _ rfl (by decide)
  change runPrefix onlineInput 1787 ⟨54, onlineBranchMemory tagged⟩ =
    PMF.pure (some (false, ⟨71, first⟩, 1787)) at readX
  have readY := onlineInput_readStore 254 outY (onlineInputLabels 71 85) (onlineStoreLabels 85 97) 4
    onlineInput_blocks.2.2.2.2 onlineInput_stores.2.2.2.2 rfl first rest rfl (by decide)
  change runPrefix onlineInput 1787 ⟨71, first⟩ =
    PMF.pure (some (false, ⟨97, onlineReadStored first 254 outY 4 rest⟩, 1787)) at readY
  change runPrefix onlineInput (3597 + (3 + (1787 + 1787))) ⟨0, base⟩ = _
  rw [prefix_add, readTag, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, readX, PMF.pure_bind]
  dsimp only
  rw [readY]
  simp [PMF.pure_map, onlineAffineMemory, tagged, first, onlineReadStored]

end Kriterion.ArgoMAC.ArithmeticSimulator
