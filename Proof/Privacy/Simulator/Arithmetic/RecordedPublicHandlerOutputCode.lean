import Proof.Privacy.Simulator.Arithmetic.RecordedPublicHandlerCode
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerDispatch

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The reverse scan retains its internal return and caller labels. -/
theorem recordedPublicHandler_inverseScan (attempts : Nat) :
    ContainsReverseSwapTable (recordedPublicHandler attempts)
      (recordedPublicRedirect ∘ publicInverseOverlayScanLabels) := by
  intro pc valid
  have bound := pc.isLt
  have notSave : publicInverseOverlayScanLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseOverlayScanLabels, valid] at this
    omega
  have notHistory : publicInverseOverlayScanLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseOverlayScanLabels, valid] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_inverseScan attempts pc valid)).trans
      (relocate_comp publicInverseOverlayScanLabels recordedPublicRedirect _))

/-- The answer writer starts after the history block and keeps its original output order. -/
theorem recordedPublicHandler_blockOutput (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) (wordOutput 128)
      (recordedPublicCore ∘ publicBlockOutputLabels) := by
  intro index valid
  have bound : index < 384 := by simpa only [wordOutput_length] using valid
  have next : recordedPublicRedirect (publicBlockOutputLabels (index + 1)) =
      recordedPublicCore (publicBlockOutputLabels (index + 1)) := by
    unfold recordedPublicRedirect publicBlockOutputLabels publicHandlerLabels
    split <;> simp_all [Fin.ext_iff, show 616 + (index + 1) ≠ 96 by omega,
      show 616 + (index + 1) ≠ 616 by omega, show 1000 + (index + 1) ≠ 96 by omega,
      show 1000 + (index + 1) ≠ 616 by omega]
  exact (recordedPublicHandler_core attempts _).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_blockOutput attempts index valid)).trans
      ((LinearInstruction.relocate_emit recordedPublicRedirect _ _).trans (by rw [next]; rfl)))

/-- The hash writer keeps both wire blocks and its original return. -/
theorem recordedPublicHandler_hashOutput (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) hashOutput
      (recordedPublicCore ∘ publicHashOutputLabels) := by
  intro index valid
  have bound : index < 770 := by simpa only [hashOutput_length] using valid
  have next : recordedPublicRedirect (publicHashOutputLabels (index + 1)) =
      recordedPublicCore (publicHashOutputLabels (index + 1)) := by
    unfold recordedPublicRedirect publicHashOutputLabels publicHandlerLabels
    split <;> simp_all [Fin.ext_iff, show 616 + (index + 1) ≠ 96 by omega,
      show 616 + (index + 1) ≠ 616 by omega, show 1000 + (index + 1) ≠ 96 by omega,
      show 1000 + (index + 1) ≠ 616 by omega]
  exact (recordedPublicHandler_core attempts _).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_hashOutput attempts index valid)).trans
      ((LinearInstruction.relocate_emit recordedPublicRedirect _ _).trans (by rw [next]; rfl)))

/-- The save block returns to the six original dispatch instructions. -/
theorem recordedPublicHandler_dispatch (attempts : Nat) :
    ContainsPublicDispatch (recordedPublicHandler attempts)
      (recordedPublicCore ∘ publicDispatchLabels) := by
  rcases publicHandler_containsDispatch attempts with ⟨c0, c1, c2, c3, c4, c5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (recordedPublicHandler_core attempts 96).trans
      (congrArg (relocate recordedPublicRedirect) c0)
  · exact (recordedPublicHandler_core attempts 97).trans
      (congrArg (relocate recordedPublicRedirect) c1)
  · exact (recordedPublicHandler_core attempts 98).trans
      (congrArg (relocate recordedPublicRedirect) c2)
  · exact (recordedPublicHandler_core attempts 99).trans
      (congrArg (relocate recordedPublicRedirect) c3)
  · exact (recordedPublicHandler_core attempts 100).trans
      (congrArg (relocate recordedPublicRedirect) c4)
  · exact (recordedPublicHandler_core attempts 101).trans
      (congrArg (relocate recordedPublicRedirect) c5)

private theorem original_haltCode (attempts : Nat) :
    (publicHandler attempts).code[1770]'(by change 1770 < 1772; decide) = .halt := by
  simp [publicHandler]
  try rfl

/-- The wrapper retains this core instruction with its redirected targets. -/
theorem recordedPublicHandler_haltCode (attempts : Nat) :
    (recordedPublicHandler attempts).code[1770]'(by change 1770 < 1810; decide) = relocate recordedPublicRedirect (.halt) :=
  (recordedPublicHandler_core attempts 1770).trans
    (congrArg (relocate recordedPublicRedirect) (original_haltCode attempts))

private theorem original_abortCode (attempts : Nat) :
    (publicHandler attempts).code[1771]'(by change 1771 < 1772; decide) = .halt := by
  simp [publicHandler]
  try rfl

/-- The wrapper retains this core instruction with its redirected targets. -/
theorem recordedPublicHandler_abortCode (attempts : Nat) :
    (recordedPublicHandler attempts).code[1771]'(by change 1771 < 1810; decide) = relocate recordedPublicRedirect (.halt) :=
  (recordedPublicHandler_core attempts 1771).trans
    (congrArg (relocate recordedPublicRedirect) (original_abortCode attempts))

private theorem original_forwardGateCode (attempts : Nat) :
    (publicHandler attempts).code[280]'(by change 280 < 1772; decide) = .branch 7 1771 281 := by
  simp [publicHandler]
  try rfl

/-- The wrapper retains this core instruction with its redirected targets. -/
theorem recordedPublicHandler_forwardGateCode (attempts : Nat) :
    (recordedPublicHandler attempts).code[280]'(by change 280 < 1810; decide) = relocate recordedPublicRedirect (.branch 7 1771 281) :=
  (recordedPublicHandler_core attempts 280).trans
    (congrArg (relocate recordedPublicRedirect) (original_forwardGateCode attempts))

private theorem original_inverseGateCode (attempts : Nat) :
    (publicHandler attempts).code[541]'(by change 541 < 1772; decide) = .branch 7 1771 616 := by
  simp [publicHandler]
  try rfl

/-- The wrapper retains this core instruction with its redirected targets. -/
theorem recordedPublicHandler_inverseGateCode (attempts : Nat) :
    (recordedPublicHandler attempts).code[541]'(by change 541 < 1810; decide) = relocate recordedPublicRedirect (.branch 7 1771 616) :=
  (recordedPublicHandler_core attempts 541).trans
    (congrArg (relocate recordedPublicRedirect) (original_inverseGateCode attempts))

private theorem original_hashGateCode (attempts : Nat) :
    (publicHandler attempts).code[615]'(by change 615 < 1772; decide) = .branch 7 1771 1000 := by
  simp [publicHandler]
  try rfl

/-- The wrapper retains this core instruction with its redirected targets. -/
theorem recordedPublicHandler_hashGateCode (attempts : Nat) :
    (recordedPublicHandler attempts).code[615]'(by change 615 < 1810; decide) = relocate recordedPublicRedirect (.branch 7 1771 1000) :=
  (recordedPublicHandler_core attempts 615).trans
    (congrArg (relocate recordedPublicRedirect) (original_hashGateCode attempts))

end Kriterion.ArgoMAC.ArithmeticSimulator
