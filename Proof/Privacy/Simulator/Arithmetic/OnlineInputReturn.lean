import Proof.Privacy.Simulator.Arithmetic.OnlineInputBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol
set_option maxRecDepth 4096

/-- Each input block reads one word and stores it before it returns. -/
theorem onlineInputHost_readStore [BN254.FieldCertificate] (host : Machine) (width value : Nat)
    (readLabels : Fin 15 → Fin (host.size + 1)) (storeLabels : Nat → Fin (host.size + 1)) (offset : Word)
    (reader : ContainsWordInput host width readLabels)
    (writer : ContainsLinear host (onlineInputStore offset) storeLabels)
    (joined : readLabels 14 = storeLabels 0) (base : Memory) (rest : List Bool)
    (wire : base.bits 0 = bits width value ++ rest) (fits : width ≤ 256) :
    runPrefix host (7 * width + 9) ⟨readLabels 0, base⟩ =
      PMF.pure (some (false, ⟨storeLabels 3,
        onlineReadStored base width value offset rest⟩, 7 * width + 9)) := by
  have read := decodedInputHost_prefix host width value readLabels reader base rest wire fits
  have write := linear_prefix host (onlineInputStore offset) storeLabels writer
    (decodedInput base width value rest)
  rw [onlineInputStore_memory] at write
  change runPrefix host 3 ⟨storeLabels 0, decodedInput base width value rest⟩ = _ at write
  rw [show 7 * width + 9 = (7 * width + 6) + 3 by omega, prefix_add, read, PMF.pure_bind]
  dsimp only
  rw [joined, write]
  simp [onlineReadStored, onlineInputStore, PMF.pure_map, Nat.add_comm]

/-- The common prefix consumes two coordinates and the output tag. -/
theorem onlineInputHost_taggedPrefix [BN254.FieldCertificate]
    (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (base : Memory)
    (x y tag : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 tag ++ rest) :
    runPrefix host 3597 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 51, onlineTaggedMemory base x y tag rest⟩, 3597)) := by
  let first := onlineReadStored base 254 x 0 (bits 254 y ++ bits 2 tag ++ rest)
  let second := onlineReadStored first 254 y 1 (bits 2 tag ++ rest)
  have readX := onlineInputHost_readStore host 254 x (fun pc => labels (onlineInputLabels 0 14 pc)) (fun i => labels (onlineStoreLabels 14 17 i)) 0
    (onlineInputBlock_word host labels present 254 0 14 onlineInput_blocks.1)
    (onlineInputBlock_store host labels present 0 14 17 onlineInput_stores.1 (by decide)) rfl base _ wire (by decide)
  change runPrefix host 1787 ⟨labels 0, base⟩ =
    PMF.pure (some (false, ⟨labels 17, first⟩, 1787)) at readX
  have readY := onlineInputHost_readStore host 254 y (fun pc => labels (onlineInputLabels 17 31 pc)) (fun i => labels (onlineStoreLabels 31 34 i)) 1
    (onlineInputBlock_word host labels present 254 17 31 onlineInput_blocks.2.1)
    (onlineInputBlock_store host labels present 1 31 34 onlineInput_stores.2.1 (by decide)) rfl first _ rfl (by decide)
  change runPrefix host 1787 ⟨labels 17, first⟩ =
    PMF.pure (some (false, ⟨labels 34, second⟩, 1787)) at readY
  have readTag := onlineInputHost_readStore host 2 tag (fun pc => labels (onlineInputLabels 34 48 pc)) (fun i => labels (onlineStoreLabels 48 51 i)) 2
    (onlineInputBlock_word host labels present 2 34 48 onlineInput_blocks.2.2.1)
    (onlineInputBlock_store host labels present 2 48 51 onlineInput_stores.2.2.1 (by decide)) rfl second rest rfl (by decide)
  change runPrefix host 23 ⟨labels 34, second⟩ =
    PMF.pure (some (false, ⟨labels 51, onlineReadStored second 2 tag 2 rest⟩, 23)) at readTag
  change runPrefix host (1787 + (1787 + 23)) ⟨labels 0, base⟩ = _
  rw [prefix_add, readX, PMF.pure_bind]
  dsimp only
  rw [prefix_add, readY, PMF.pure_bind]
  dsimp only
  rw [readTag]
  simp [PMF.pure_map, onlineTaggedMemory, first, second, onlineReadStored]


/-- The affine path returns after it stores both output coordinates. -/
theorem onlineInputHost_affinePrefix [BN254.FieldCertificate]
    (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (base : Memory)
    (x y outX outY : Nat) (rest : List Bool)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 1 ++
      bits 254 outX ++ bits 254 outY ++ rest) :
    runPrefix host 7174 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 97, onlineAffineMemory base x y outX outY rest⟩, 7174)) := by
  let tagged := onlineTaggedMemory base x y 1 (bits 254 outX ++ bits 254 outY ++ rest)
  let first := onlineReadStored (onlineBranchMemory tagged) 254 outX 3 (bits 254 outY ++ rest)
  have readTag := onlineInputHost_taggedPrefix host labels present base x y 1 (bits 254 outX ++ bits 254 outY ++ rest)
    (by simpa only [List.append_assoc] using wire)
  change runPrefix host 3597 ⟨labels 0, base⟩ =
    PMF.pure (some (false, ⟨labels 51, tagged⟩, 3597)) at readTag
  have tagValue : tagged.registers 0 = 1 := by
    simp [tagged, onlineTaggedMemory, onlineReadStored, onlineStored, decodedInput_values]
  have branch := onlineInputBlock_branch host labels present tagged
  rw [tagValue, if_pos rfl] at branch
  have readX := onlineInputHost_readStore host 254 outX (fun pc => labels (onlineInputLabels 54 68 pc)) (fun i => labels (onlineStoreLabels 68 71 i)) 3
    (onlineInputBlock_word host labels present 254 54 68 onlineInput_blocks.2.2.2.1)
    (onlineInputBlock_store host labels present 3 68 71 onlineInput_stores.2.2.2.1 (by decide)) rfl (onlineBranchMemory tagged) _ rfl (by decide)
  change runPrefix host 1787 ⟨labels 54, onlineBranchMemory tagged⟩ =
    PMF.pure (some (false, ⟨labels 71, first⟩, 1787)) at readX
  have readY := onlineInputHost_readStore host 254 outY (fun pc => labels (onlineInputLabels 71 85 pc)) (fun i => labels (onlineStoreLabels 85 97 i)) 4
    (onlineInputBlock_word host labels present 254 71 85 onlineInput_blocks.2.2.2.2)
    (onlineInputBlock_store host labels present 4 85 97 onlineInput_stores.2.2.2.2 (by decide)) rfl first rest rfl (by decide)
  change runPrefix host 1787 ⟨labels 71, first⟩ =
    PMF.pure (some (false, ⟨labels 97, onlineReadStored first 254 outY 4 rest⟩, 1787)) at readY
  change runPrefix host (3597 + (3 + (1787 + 1787))) ⟨labels 0, base⟩ = _
  rw [prefix_add, readTag, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [prefix_add, readX, PMF.pure_bind]
  dsimp only
  rw [readY]
  simp [PMF.pure_map, onlineAffineMemory, tagged, first, onlineReadStored]

/-- The null path returns after it stores the two zero coordinates. -/
theorem onlineInputHost_nullPrefix [BN254.FieldCertificate]
    (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (base : Memory)
    (x y tag : Nat) (rest : List Bool) (tagFits : tag < 4) (notAffine : tag ≠ 1)
    (wire : base.bits 0 = bits 254 x ++ bits 254 y ++ bits 2 tag ++ rest) :
    runPrefix host 3607 ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 97, onlineNullMemory base x y tag rest⟩, 3607)) := by
  let tagged := onlineTaggedMemory base x y tag rest
  have readTag := onlineInputHost_taggedPrefix host labels present base x y tag rest wire
  have tagValue : tagged.registers 0 = BitVec.ofNat 256 tag := by
    simp [tagged, onlineTaggedMemory, onlineReadStored, onlineStored, decodedInput_values,
      Nat.mod_eq_of_lt tagFits]
  have tagNe : tagged.registers 0 ≠ 1 := by
    rw [tagValue]
    intro equal
    have values := congrArg BitVec.toNat equal
    simp only [BitVec.toNat_ofNat] at values
    have small : tag < 2 ^ 256 := by omega
    rw [Nat.mod_eq_of_lt small] at values
    exact notAffine values
  have branch := onlineInputBlock_branch host labels present tagged
  rw [if_neg tagNe] at branch
  have zeroPresent : ContainsLinear host onlineInputZero (fun i => labels (onlineZeroLabels i)) := by
    apply onlineInputBlock_linear host labels present _ _ onlineInput_zeroContains
    intro index valid
    have bound : index < 7 := valid
    simp only [onlineZeroLabels, dif_pos bound, Fin.val_mk]
    omega
  have zeros := linear_prefix host onlineInputZero (fun i => labels (onlineZeroLabels i))
    zeroPresent (onlineBranchMemory tagged)
  change runPrefix host 7 ⟨labels 90, onlineBranchMemory tagged⟩ =
    PMF.pure (some (false, ⟨labels 97, onlineNullMemory base x y tag rest⟩, 7)) at zeros
  change runPrefix host (3597 + (3 + 7)) ⟨labels 0, base⟩ = _
  rw [prefix_add, readTag, PMF.pure_bind]
  dsimp only
  rw [prefix_add, branch, PMF.pure_bind]
  dsimp only
  rw [zeros]
  simp [PMF.pure_map]


/-- The reader consumes the exact online protocol body. -/
theorem onlineInputHost_prefix [BN254.FieldCertificate]
    (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (base : Memory) (input : BN254.AffineInput)
    (result : Option BN254.Point) (rest : List Bool)
    (wire : base.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output result ++ rest) :
    runPrefix host (onlineInputCost result - 1) ⟨labels 0, base⟩ =
      PMF.pure (some (false, ⟨labels 97, onlineInputMemory base input result rest⟩, onlineInputCost result - 1)) := by
  cases result with
  | none =>
      exact onlineInputHost_nullPrefix host labels present base input.x.val input.y.val 0 rest (by decide) (by decide)
        (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
          show bits 2 0 = [false, false] from rfl, List.append_assoc] using wire)
  | some result =>
      cases result with
      | zero =>
          exact onlineInputHost_nullPrefix host labels present base input.x.val input.y.val 2 rest (by decide) (by decide)
            (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
              show bits 2 2 = [false, true] from rfl, List.append_assoc] using wire)
      | @some x y valid =>
          exact onlineInputHost_affinePrefix host labels present base input.x.val input.y.val x.val y.val rest
            (by simpa only [affine, GarbledCircuit.SimulatorProtocol.output,
              show bits 2 1 = [true, false] from rfl, List.append_assoc] using wire)

/-- The online reader returns to its caller with its exact memory and cost. -/
theorem onlineInputHost_continue [BN254.FieldCertificate]
    (host : Machine) (labels : Fin 98 → Fin (host.size + 1))
    (present : ContainsOnlineInput host labels) (base : Memory) (input : BN254.AffineInput)
    (result : Option BN254.Point) (rest : List Bool) (fuel : Nat)
    (wire : base.bits 0 = affine input ++ GarbledCircuit.SimulatorProtocol.output result ++ rest) :
    run host ((onlineInputCost result - 1) + fuel) ⟨labels 0, base⟩ =
      (run host fuel ⟨labels 97, onlineInputMemory base input result rest⟩).map
        (Option.map fun outcome => (outcome.1, outcome.2 + (onlineInputCost result - 1))) := by
  rw [run_after_prefix, onlineInputHost_prefix host labels present base input result rest wire,
    PMF.pure_bind]

end Kriterion.ArgoMAC.ArithmeticSimulator
