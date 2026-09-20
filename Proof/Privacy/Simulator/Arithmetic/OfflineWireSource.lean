import Proof.Privacy.Simulator.Arithmetic.SamplerBatch
import Proof.Privacy.Simulator.Arithmetic.PublicWireProtocol

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography.BoundedMachine GarbledCircuit.SimulatorProtocol Security
set_option maxRecDepth 4096
attribute [local irreducible] publicWire wireSegmentsProgram Wire.encoding publicValue
  samplerBatchMemory offlinePlan SimulatorSampling.Code.total bits WireSegment.wire

/-- The serializer output depends only on the source RAM and the retained output stack. -/
theorem publicWireProgram_output (memory : Memory) :
    (executeLinear publicWireProgram memory).bits 3 =
      publicWire.flatMap (WireSegment.wire memory.ram (memory.registers 11)) ++ memory.bits 3 := by
  have result := wireSegments_bits publicWire memory
  rw [← publicWireProgram_eq] at result
  rw [result, Function.update_self]

/-- A RAM observation keeps the exact sampler law when the caller data stays fixed. -/
theorem samplerBatchMemory_observe {Value : Type} {count : Nat} (plan : Vector DrawSpec count)
    (attempts remaining index : Nat) (base : Memory) (project : Memory → Value)
    (observe : (Word → Word) → Value)
    (depends : ∀ memory, memory.registers 11 = base.registers 11 → memory.bits = base.bits →
      project memory = observe memory.ram) :
    (samplerBatchMemory plan attempts remaining index base).map (fun result => project result.1) =
    ((samplerBatchMemory plan attempts remaining index base).map (fun result => result.1.ram)).map observe := by
  rw [PMF.map_comp]
  change (samplerBatchMemory plan attempts remaining index base).bind _ =
    (samplerBatchMemory plan attempts remaining index base).bind _
  apply ThreePhase.bind_eq_on_support
  intro result supported
  rcases result with ⟨memory, cost⟩
  exact congrArg PMF.pure (depends memory
    (samplerBatchMemory_caller plan attempts remaining index base memory cost 11 (by decide) supported)
    (samplerBatchMemory_bits plan attempts remaining index base memory cost supported))

/-- The sampler preserves the serializer address and the empty output stack. -/
theorem samplerBatchMemory_wire [FieldCertificate] {count : Nat} (plan : Vector DrawSpec count)
    (attempts remaining index : Nat) (base : Memory)
    (pointer : base.registers 11 = base.registers 10) (empty : base.bits 3 = []) :
    (samplerBatchMemory plan attempts remaining index base).map
      (fun result => (executeLinear publicWireProgram result.1).bits 3) =
    ((samplerBatchMemory plan attempts remaining index base).map (fun result => result.1.ram)).map
      (fun ram => publicWire.flatMap (WireSegment.wire ram (base.registers 10))) := by
  refine samplerBatchMemory_observe plan attempts remaining index base
    (fun memory => (executeLinear publicWireProgram memory).bits 3)
    (fun ram => publicWire.flatMap (WireSegment.wire ram (base.registers 10))) ?_
  intro memory saved bitsSaved
  rw [publicWireProgram_output, saved, pointer, bitsSaved, empty, List.append_nil]

/-- The stored offline source gives the exact canonical public wire. -/
theorem offlineStored_wire (coin : SimulatorSampling.OfflineCoin) (pointer : Word) (ram : Word → Word) :
    publicWire.flatMap (WireSegment.wire
      (storeDrawWords pointer 0 ram (offlineSchedule.words coin)) pointer) =
      (Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val) := by
  have fits : 0 + (offlineSchedule.words coin).length ≤ 2 ^ 256 := by
    rw [offlineSchedule.wordsLength]
    decide
  exact publicWire_bits coin.1 _ _ (offline_public_words coin _ _
    (wordsAt_store pointer 0 ram (offlineSchedule.words coin) fits))

/-- An observation preserves an exact source law through both maps. -/
theorem observe_source_map {A B C D : Type} (law : PMF A) (source : PMF B)
    (extract : A → C) (encode : B → C) (observe : C → D) (output : B → D)
    (exactLaw : law.map extract = source.map encode)
    (same : ∀ value, observe (encode value) = output value) :
    (law.map extract).map observe = source.map output := by
  rw [exactLaw, PMF.map_comp]
  exact congrArg (fun transform => source.map transform) (funext same)

/-- The complete private sampler and serializer return the exact canonical wire law. -/
theorem offlineMemory_wire [FieldCertificate] (attempts : Nat) (base : Memory)
    (pointer : base.registers 11 = base.registers 10) (empty : base.bits 3 = []) :
    (samplerBatchMemory offlinePlan attempts 838208 0 base).map
      (fun result => (executeLinear publicWireProgram result.1).bits 3) =
      (SimulatorSampling.offline.total attempts).law.map
        (fun coin => (Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val)) := by
  have observed := observe_source_map (A := Memory × Nat) (B := SimulatorSampling.OfflineCoin)
      (C := Word → Word) (D := List Bool) (samplerBatchMemory offlinePlan attempts 838208 0 base)
      (SimulatorSampling.offline.total attempts).law (fun result => result.1.ram)
      (fun coin => storeDrawWords (base.registers 10) 0 base.ram (offlineSchedule.words coin))
      (fun ram => publicWire.flatMap (WireSegment.wire ram (base.registers 10)))
      (fun coin => (Wire.encoding.encode (publicSourceTable coin.1)).flatMap (fun byte => bits 8 byte.val))
      (offlineMemory_source attempts base) (fun coin => offlineStored_wire coin (base.registers 10) base.ram)
  exact (samplerBatchMemory_wire offlinePlan attempts 838208 0 base pointer empty).trans observed

/-- The canonical parser accepts the complete sampled public table law. -/
theorem offlineMemory_public [FieldCertificate] (attempts : Nat) (base : Memory)
    (pointer : base.registers 11 = base.registers 10) (empty : base.bits 3 = []) :
    (samplerBatchMemory offlinePlan attempts 838208 0 base).map
      (fun result => publicValue Wire.encoding 8887896 ((executeLinear publicWireProgram result.1).bits 3)) =
      (SimulatorSampling.offline.total attempts).law.map (fun coin => some (publicSourceTable coin.1)) := by
  have mapped := congrArg (PMF.map (publicValue Wire.encoding 8887896)) (offlineMemory_wire attempts base pointer empty)
  simp only [PMF.map_comp, Function.comp_def] at mapped
  refine mapped.trans ?_
  apply congrArg (fun transform => (SimulatorSampling.offline.total attempts).law.map transform)
  funext coin
  exact publicValue_bytes Wire.encoding (publicSourceTable coin.1) 8887896 (publicSourceTable_length coin.1)

end Kriterion.ArgoMAC.ArithmeticSimulator
