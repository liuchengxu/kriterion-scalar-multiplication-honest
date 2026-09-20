import Proof.Privacy.Simulator.Arithmetic.EncLinkBlock

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The schedule stores both whitening keys and the charged fixed index stream. -/
noncomputable def encLinkScheduled (memory : Memory) : Memory :=
  executeLinear encLinkIndexPrelude (executeLinear encLinkWhitening memory)

/-- The whitening setup and fixed index schedule use 7120 instructions. -/
theorem encLinkBlock_schedule [BN254.FieldCertificate] (host : Machine) (attempts : Nat)
    (labels : Fin 7468 → Fin (host.size + 1)) (present : ContainsEncLink host attempts labels)
    (memory : Memory) :
    runPrefix host 7120 ⟨labels 88, memory⟩ =
      PMF.pure (some (false, ⟨labels 7208, encLinkScheduled memory⟩, 7120)) := by
  have whitening := encLinkBlock_linear host attempts labels present encLinkWhitening encLinkWhiteningLabels
    (encLink_whitening attempts) (by
      intro index valid
      have bound : index < 8 := valid
      simp [encLinkWhiteningLabels, encLinkLabels, bound]
      omega)
  have indices := encLinkBlock_linear host attempts labels present encLinkIndexPrelude encLinkIndexLabels
    (encLink_indices attempts) (by
      intro index valid
      have bound : index < 7112 := by simpa only [encLinkIndexPrelude_length] using valid
      simp [encLinkIndexLabels, encLinkLabels, bound]
      omega)
  have first := linear_prefix host encLinkWhitening (labels ∘ encLinkWhiteningLabels) whitening memory
  change runPrefix host 8 ⟨labels 88, memory⟩ = _ at first
  have second := linear_prefix host encLinkIndexPrelude (labels ∘ encLinkIndexLabels) indices
    (executeLinear encLinkWhitening memory)
  rw [encLinkIndexPrelude_length] at second
  change runPrefix host 7112 ⟨labels 96, _⟩ = _ at second
  rw [show 7120 = 8 + 7112 from rfl, prefix_add, first, PMF.pure_bind]
  dsimp only
  change (runPrefix host 7112 ⟨labels 96, _⟩).map _ = _
  rw [second]
  simp [encLinkScheduled, PMF.pure_map, encLinkIndexLabels, encLinkLabels,
    show encLinkWhitening.length = 8 from rfl]

/-- The complete schedule preserves all data except its two key cells and stack zero. -/
theorem encLinkScheduled_memory (memory : Memory) :
    (encLinkScheduled memory).ram =
      Function.update (Function.update memory.ram 39 (memory.registers 8 >>> 128))
        40 (memory.registers 8 &&& BitVec.ofNat 256 (2 ^ 128 - 1)) ∧
    (encLinkScheduled memory).bits = Function.update memory.bits 0 (encLinkIndexWire ++ memory.bits 0) := by
  unfold encLinkScheduled
  rw [encLinkIndexPrelude_memory]
  exact ⟨(encLinkWhitening_state memory).1, by rw [(encLinkWhitening_state memory).2]⟩

end Kriterion.ArgoMAC.ArithmeticSimulator
