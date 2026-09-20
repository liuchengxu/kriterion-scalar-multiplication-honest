import Construction.Simulator.PublicHandler
import Proof.Privacy.Simulator.Arithmetic.QueryInputReturn
import Proof.Privacy.Simulator.Arithmetic.StoredForwardBlock
import Proof.Privacy.Simulator.Arithmetic.StoredInverseBlock
import Proof.Privacy.Simulator.Arithmetic.HashHandlerBlock
import Proof.Privacy.Simulator.Arithmetic.OverlayScan

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open Cryptography.BoundedMachine

/-- The public machine contains the complete query block. -/
theorem publicHandler_query (attempts : Nat) :
    ContainsQueryInput (publicHandler attempts) publicQueryLabels := by
  intro pc valid
  have bound : pc.val < 96 := valid
  simp [publicHandler, publicQueryLabels, publicHandlerLabels, bound]
  rfl

/-- The public machine contains the complete forward block. -/
theorem publicHandler_forward (attempts : Nat) :
    ContainsStoredForward (publicHandler attempts) attempts publicForwardLabels := by
  intro pc valid
  have bound : pc.val < 178 := by
    have small := pc.isLt
    have different : pc.val ≠ 178 := by intro equal; apply valid; exact Fin.ext equal
    omega
  simp [publicHandler, publicForwardLabels, publicHandlerLabels, bound, show ¬ 102 + pc.val < 96 by omega,
    show 102 ≤ 102 + pc.val by omega,
    show 102 + pc.val < 280 by omega]
  rfl

/-- The public machine contains the complete overlayScan block. -/
theorem publicHandler_overlayScan (attempts : Nat) :
    ContainsSwapTable (publicHandler attempts) publicOverlayScanLabels := by
  intro pc valid
  have bound : pc.val < 13 := by
    have small := pc.isLt
    have different : pc.val ≠ 13 := by intro equal; apply valid; exact Fin.ext equal
    omega
  simp [publicHandler, publicOverlayScanLabels, publicHandlerLabels, bound, show ¬ 286 + pc.val < 96 by omega,
    show ¬ (102 ≤ 286 + pc.val ∧ 286 + pc.val < 280) by omega,
    show ¬ (281 ≤ 286 + pc.val ∧ 286 + pc.val < 286) by omega,
    show 286 ≤ 286 + pc.val by omega,
    show 286 + pc.val < 299 by omega]
  rfl

/-- The public machine contains the complete inverse block. -/
theorem publicHandler_inverse (attempts : Nat) :
    ContainsStoredInverse (publicHandler attempts) attempts publicInverseLabels := by
  intro pc valid
  have bound : pc.val < 192 := by
    have small := pc.isLt
    have different : pc.val ≠ 192 := by intro equal; apply valid; exact Fin.ext equal
    omega
  simp [publicHandler, publicInverseLabels, publicHandlerLabels, bound, show ¬ 349 + pc.val < 96 by omega,
    show ¬ (102 ≤ 349 + pc.val ∧ 349 + pc.val < 280) by omega,
    show ¬ (281 ≤ 349 + pc.val ∧ 349 + pc.val < 286) by omega,
    show ¬ (286 ≤ 349 + pc.val ∧ 349 + pc.val < 299) by omega,
    show ¬ (299 ≤ 349 + pc.val ∧ 349 + pc.val < 321) by omega,
    show ¬ (321 ≤ 349 + pc.val ∧ 349 + pc.val < 330) by omega,
    show ¬ (330 ≤ 349 + pc.val ∧ 349 + pc.val < 345) by omega,
    show ¬ (345 ≤ 349 + pc.val ∧ 349 + pc.val < 349) by omega,
    show 349 ≤ 349 + pc.val by omega,
    show 349 + pc.val < 541 by omega]
  rfl

/-- The public machine contains the complete hash block. -/
theorem publicHandler_hash (attempts : Nat) :
    ContainsHashHandler (publicHandler attempts) publicHashLabels := by
  intro pc valid
  have bound : pc.val < 73 := by
    have small := pc.isLt
    have different : pc.val ≠ 73 := by intro equal; apply valid; exact Fin.ext equal
    omega
  simp [publicHandler, publicHashLabels, publicHandlerLabels, bound, show ¬ 542 + pc.val < 96 by omega,
    show ¬ (102 ≤ 542 + pc.val ∧ 542 + pc.val < 280) by omega,
    show ¬ (281 ≤ 542 + pc.val ∧ 542 + pc.val < 286) by omega,
    show ¬ (286 ≤ 542 + pc.val ∧ 542 + pc.val < 299) by omega,
    show ¬ (299 ≤ 542 + pc.val ∧ 542 + pc.val < 321) by omega,
    show ¬ (321 ≤ 542 + pc.val ∧ 542 + pc.val < 330) by omega,
    show ¬ (330 ≤ 542 + pc.val ∧ 542 + pc.val < 345) by omega,
    show ¬ (345 ≤ 542 + pc.val ∧ 542 + pc.val < 349) by omega,
    show ¬ (349 ≤ 542 + pc.val ∧ 542 + pc.val < 541) by omega,
    show 542 ≤ 542 + pc.val by omega,
    show 542 + pc.val < 615 by omega]
  rfl

/-- The public machine contains every instruction in the overlayLoad block. -/
theorem publicHandler_overlayLoad (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (overlayLoad) publicOverlayLoadLabels := by
  intro index valid
  have bound : index < 5 := valid
  simp [publicHandler, publicOverlayLoadLabels, publicHandlerLabels, bound,
    show ¬ 281 + index < 96 by omega,
    show ¬ (102 ≤ 281 + index ∧ 281 + index < 280) by omega,
    show 281 ≤ 281 + index by omega,
    show 281 + index < 286 by omega]

/-- The public machine contains every instruction in the inverseHeader block. -/
theorem publicHandler_inverseHeader (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (oracleLoad) publicInverseHeaderLabels := by
  intro index valid
  have bound : index < 22 := valid
  simp [publicHandler, publicInverseHeaderLabels, publicHandlerLabels, bound,
    show ¬ 299 + index < 96 by omega,
    show ¬ (102 ≤ 299 + index ∧ 299 + index < 280) by omega,
    show ¬ (281 ≤ 299 + index ∧ 299 + index < 286) by omega,
    show ¬ (286 ≤ 299 + index ∧ 299 + index < 299) by omega,
    show 299 ≤ 299 + index by omega,
    show 299 + index < 321 by omega]

/-- The public machine contains every instruction in the inverseLoad block. -/
theorem publicHandler_inverseLoad (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (overlayInverseLoad) publicInverseOverlayLoadLabels := by
  intro index valid
  have bound : index < 9 := valid
  simp [publicHandler, publicInverseOverlayLoadLabels, publicHandlerLabels, bound,
    show ¬ 321 + index < 96 by omega,
    show ¬ (102 ≤ 321 + index ∧ 321 + index < 280) by omega,
    show ¬ (281 ≤ 321 + index ∧ 321 + index < 286) by omega,
    show ¬ (286 ≤ 321 + index ∧ 321 + index < 299) by omega,
    show ¬ (299 ≤ 321 + index ∧ 321 + index < 321) by omega,
    show 321 ≤ 321 + index by omega,
    show 321 + index < 330 by omega]

/-- The public machine contains every instruction in the restore block. -/
theorem publicHandler_restore (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (queryRestore) publicQueryRestoreLabels := by
  intro index valid
  have bound : index < 4 := valid
  simp [publicHandler, publicQueryRestoreLabels, publicHandlerLabels, bound,
    show ¬ 345 + index < 96 by omega,
    show ¬ (102 ≤ 345 + index ∧ 345 + index < 280) by omega,
    show ¬ (281 ≤ 345 + index ∧ 345 + index < 286) by omega,
    show ¬ (286 ≤ 345 + index ∧ 345 + index < 299) by omega,
    show ¬ (299 ≤ 345 + index ∧ 345 + index < 321) by omega,
    show ¬ (321 ≤ 345 + index ∧ 345 + index < 330) by omega,
    show ¬ (330 ≤ 345 + index ∧ 345 + index < 345) by omega,
    show 345 ≤ 345 + index by omega,
    show 345 + index < 349 by omega]

/-- The public machine contains every instruction in the blockOutput block. -/
theorem publicHandler_blockOutput (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (wordOutput 128) publicBlockOutputLabels := by
  intro index valid
  have bound : index < 384 := by simpa only [wordOutput_length] using valid
  simp [publicHandler, publicBlockOutputLabels, publicHandlerLabels, bound,
    show ¬ 616 + index < 96 by omega,
    show ¬ (102 ≤ 616 + index ∧ 616 + index < 280) by omega,
    show ¬ (281 ≤ 616 + index ∧ 616 + index < 286) by omega,
    show ¬ (286 ≤ 616 + index ∧ 616 + index < 299) by omega,
    show ¬ (299 ≤ 616 + index ∧ 616 + index < 321) by omega,
    show ¬ (321 ≤ 616 + index ∧ 616 + index < 330) by omega,
    show ¬ (330 ≤ 616 + index ∧ 616 + index < 345) by omega,
    show ¬ (345 ≤ 616 + index ∧ 616 + index < 349) by omega,
    show ¬ (349 ≤ 616 + index ∧ 616 + index < 541) by omega,
    show ¬ (542 ≤ 616 + index ∧ 616 + index < 615) by omega,
    show 616 ≤ 616 + index by omega,
    show 616 + index < 1000 by omega]

/-- The public machine contains every instruction in the hashOutput block. -/
theorem publicHandler_hashOutput (attempts : Nat) :
    ContainsLinear (publicHandler attempts) (hashOutput) publicHashOutputLabels := by
  intro index valid
  have bound : index < 770 := by simpa only [hashOutput_length] using valid
  simp [publicHandler, publicHashOutputLabels, publicHandlerLabels, bound,
    show ¬ 1000 + index < 96 by omega,
    show ¬ (102 ≤ 1000 + index ∧ 1000 + index < 280) by omega,
    show ¬ (281 ≤ 1000 + index ∧ 1000 + index < 286) by omega,
    show ¬ (286 ≤ 1000 + index ∧ 1000 + index < 299) by omega,
    show ¬ (299 ≤ 1000 + index ∧ 1000 + index < 321) by omega,
    show ¬ (321 ≤ 1000 + index ∧ 1000 + index < 330) by omega,
    show ¬ (330 ≤ 1000 + index ∧ 1000 + index < 345) by omega,
    show ¬ (345 ≤ 1000 + index ∧ 1000 + index < 349) by omega,
    show ¬ (349 ≤ 1000 + index ∧ 1000 + index < 541) by omega,
    show ¬ (542 ≤ 1000 + index ∧ 1000 + index < 615) by omega,
    show ¬ (616 ≤ 1000 + index ∧ 1000 + index < 1000) by omega,
    show 1000 ≤ 1000 + index by omega,
    show 1000 + index < 1770 by omega]

/-- The public machine contains the reverse overlay scan and its explicit return. -/
theorem publicHandler_inverseScan (attempts : Nat) :
    ContainsReverseSwapTable (publicHandler attempts) publicInverseOverlayScanLabels := by
  intro pc valid
  have bound := pc.isLt
  simp [publicHandler, publicInverseOverlayScanLabels, valid,
show ¬ 330 + pc.val < 96 by omega,
    show ¬ (102 ≤ 330 + pc.val ∧ 330 + pc.val < 280) by omega,
    show ¬ (281 ≤ 330 + pc.val ∧ 330 + pc.val < 286) by omega,
    show ¬ (286 ≤ 330 + pc.val ∧ 330 + pc.val < 299) by omega,
    show ¬ (299 ≤ 330 + pc.val ∧ 330 + pc.val < 321) by omega,
    show ¬ (321 ≤ 330 + pc.val ∧ 330 + pc.val < 330) by omega,
    show 330 ≤ 330 + pc.val by omega,
    show 330 + pc.val < 345 by omega]

  rfl

end Kriterion.ArgoMAC.ArithmeticSimulator
