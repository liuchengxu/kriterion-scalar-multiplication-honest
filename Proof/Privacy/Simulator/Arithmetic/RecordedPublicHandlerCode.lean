import Construction.Simulator.RecordedPublicHandler
import Proof.Privacy.Simulator.Arithmetic.PublicHandlerCode
import Proof.Privacy.Simulator.Arithmetic.PublicHistoryRun

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- Each core instruction uses the two redirected entry edges. -/
theorem recordedPublicHandler_core (attempts : Nat) (pc : Fin 1772) :
    (recordedPublicHandler attempts).code[(recordedPublicCore pc).val] =
      relocate recordedPublicRedirect ((publicHandler attempts).code[pc.val]) := by
  simp [recordedPublicHandler, recordedPublicCore, pc.isLt]
  rfl

/-- Each unchanged entry also uses the redirected caller labels. -/
theorem recordedPublicHandler_redirect (attempts : Nat) (pc : Fin 1772)
    (notSave : pc ≠ 96) (notHistory : pc ≠ 616) :
    (recordedPublicHandler attempts).code[(recordedPublicRedirect pc).val] =
      relocate recordedPublicRedirect ((publicHandler attempts).code[pc.val]) := by
  simpa [recordedPublicRedirect, notSave, notHistory] using recordedPublicHandler_core attempts pc

/-- The handler saves the external operand and tag before dispatch. -/
theorem recordedPublicHandler_save (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) publicHistorySave recordedPublicSaveLabels := by
  intro index valid
  have bound : index < 4 := valid
  simp [recordedPublicHandler, recordedPublicSaveLabels, bound,
    show ¬ 1772 + index < 1772 by omega, show 1772 + index < 1776 by omega]

/-- The handler contains the complete history block. -/
theorem recordedPublicHandler_history (attempts : Nat) :
    ContainsPublicHistory (recordedPublicHandler attempts) recordedPublicHistoryLabels := by
  intro pc valid
  have bound : pc.val < 34 := valid
  simp [recordedPublicHandler, recordedPublicHistoryLabels, bound,
    show ¬ 1776 + pc.val < 1772 by omega, show ¬ 1776 + pc.val < 1776 by omega]
  rfl

/-- The query reader returns to the save block. -/
theorem recordedPublicHandler_query (attempts : Nat) :
    ContainsQueryInput (recordedPublicHandler attempts)
      (recordedPublicRedirect ∘ publicQueryLabels) := by
  intro pc valid
  have bound : pc.val < 96 := valid
  have notSave : publicQueryLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicQueryLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicQueryLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicQueryLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_query attempts pc valid)).trans
      (relocate_comp publicQueryLabels recordedPublicRedirect _))

/-- The core retains the complete forward block and its caller return. -/
theorem recordedPublicHandler_forward (attempts : Nat) :
    ContainsStoredForward (recordedPublicHandler attempts) attempts
      (recordedPublicRedirect ∘ publicForwardLabels) := by
  intro pc valid
  have bound : pc.val < 178 := by
    have small := pc.isLt
    have different : pc.val ≠ 178 := by intro equal; apply valid; exact Fin.ext equal
    omega
  have notSave : publicForwardLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicForwardLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicForwardLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicForwardLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_forward attempts pc valid)).trans
      (relocate_comp publicForwardLabels recordedPublicRedirect _))

/-- The core retains the complete inverse block and its caller return. -/
theorem recordedPublicHandler_inverse (attempts : Nat) :
    ContainsStoredInverse (recordedPublicHandler attempts) attempts
      (recordedPublicRedirect ∘ publicInverseLabels) := by
  intro pc valid
  have bound : pc.val < 192 := by
    have small := pc.isLt
    have different : pc.val ≠ 192 := by intro equal; apply valid; exact Fin.ext equal
    omega
  have notSave : publicInverseLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicInverseLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_inverse attempts pc valid)).trans
      (relocate_comp publicInverseLabels recordedPublicRedirect _))

/-- The core retains the complete hash block and its caller return. -/
theorem recordedPublicHandler_hash (attempts : Nat) :
    ContainsHashHandler (recordedPublicHandler attempts)
      (recordedPublicRedirect ∘ publicHashLabels) := by
  intro pc valid
  have bound : pc.val < 73 := by
    have small := pc.isLt
    have different : pc.val ≠ 73 := by intro equal; apply valid; exact Fin.ext equal
    omega
  have notSave : publicHashLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicHashLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicHashLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicHashLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_hash attempts pc valid)).trans
      (relocate_comp publicHashLabels recordedPublicRedirect _))

/-- The core retains the complete overlayScan block and its caller return. -/
theorem recordedPublicHandler_overlayScan (attempts : Nat) :
    ContainsSwapTable (recordedPublicHandler attempts)
      (recordedPublicRedirect ∘ publicOverlayScanLabels) := by
  intro pc valid
  have bound : pc.val < 13 := by
    have small := pc.isLt
    have different : pc.val ≠ 13 := by intro equal; apply valid; exact Fin.ext equal
    omega
  have notSave : publicOverlayScanLabels pc ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicOverlayScanLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicOverlayScanLabels pc ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicOverlayScanLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_overlayScan attempts pc valid)).trans
      (relocate_comp publicOverlayScanLabels recordedPublicRedirect _))

/-- The core retains each instruction in the overlayLoad block. -/
theorem recordedPublicHandler_overlayLoad (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) overlayLoad
      (recordedPublicRedirect ∘ publicOverlayLoadLabels) := by
  intro index valid
  have bound : index < 5 := valid
  have notSave : publicOverlayLoadLabels index ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicOverlayLoadLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicOverlayLoadLabels index ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicOverlayLoadLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_overlayLoad attempts index valid)).trans
      (LinearInstruction.relocate_emit recordedPublicRedirect _ _))

/-- The core retains each instruction in the inverseHeader block. -/
theorem recordedPublicHandler_inverseHeader (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) oracleLoad
      (recordedPublicRedirect ∘ publicInverseHeaderLabels) := by
  intro index valid
  have bound : index < 22 := valid
  have notSave : publicInverseHeaderLabels index ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseHeaderLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicInverseHeaderLabels index ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseHeaderLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_inverseHeader attempts index valid)).trans
      (LinearInstruction.relocate_emit recordedPublicRedirect _ _))

/-- The core retains each instruction in the inverseLoad block. -/
theorem recordedPublicHandler_inverseLoad (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) overlayInverseLoad
      (recordedPublicRedirect ∘ publicInverseOverlayLoadLabels) := by
  intro index valid
  have bound : index < 9 := valid
  have notSave : publicInverseOverlayLoadLabels index ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseOverlayLoadLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicInverseOverlayLoadLabels index ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicInverseOverlayLoadLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_inverseLoad attempts index valid)).trans
      (LinearInstruction.relocate_emit recordedPublicRedirect _ _))

/-- The core retains each instruction in the restore block. -/
theorem recordedPublicHandler_restore (attempts : Nat) :
    ContainsLinear (recordedPublicHandler attempts) queryRestore
      (recordedPublicRedirect ∘ publicQueryRestoreLabels) := by
  intro index valid
  have bound : index < 4 := valid
  have notSave : publicQueryRestoreLabels index ≠ 96 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicQueryRestoreLabels, publicHandlerLabels, bound] at this
    omega
  have notHistory : publicQueryRestoreLabels index ≠ 616 := by
    intro equal
    have := congrArg Fin.val equal
    simp [publicQueryRestoreLabels, publicHandlerLabels, bound] at this
    omega
  exact (recordedPublicHandler_redirect attempts _ notSave notHistory).trans
    ((congrArg (relocate recordedPublicRedirect) (publicHandler_restore attempts index valid)).trans
      (LinearInstruction.relocate_emit recordedPublicRedirect _ _))

end Kriterion.ArgoMAC.ArithmeticSimulator
