import Proof.Privacy.Simulator.Arithmetic.OnlineValidLinkReady
import Proof.Privacy.Simulator.Arithmetic.EncLinkTypedSource
import Proof.Privacy.Simulator.Arithmetic.EncLinkSharedCutoff

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SimulatorSampling Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] encLinkIndices

/-- The complete link loop returns only a success or cutoff label. -/
theorem encLinkLoopSamples_terminal (attempts : Nat) (firstKey : Cryptography.Block) (suffix : List Bool)
    (indices : List EncPRF.PermutationIndex) (memory : Memory) (state : SparseOracleFamily)
    (result : EncLinkResult)
    (supported : result ∈ (encLinkLoopSamples attempts firstKey suffix indices memory state).support) :
    result.1.2.2 = 7466 ∨ result.1.2.2 = 7467 := by
  induction indices generalizing memory state result with
  | nil =>
      have same := (PMF.mem_support_pure_iff _ _).mp supported
      subst result
      exact Or.inl rfl
  | cons index indices ih =>
      obtain ⟨row, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
      split at tail
      · rename_i failed
        have same := (PMF.mem_support_pure_iff _ _).mp tail
        subst result
        exact Or.inr failed
      · obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
        exact ih row.1.1 row.2 last lastMember

/-- The complete link returns only a success or cutoff label. -/
theorem encLinkSamples_terminal (attempts : Nat) (memory : Memory) (state : SparseOracleFamily)
    (key : BaseField) (suffix : List Bool) (result : EncLinkResult)
    (supported : result ∈ (encLinkSamples attempts memory state key suffix).support) :
    result.1.2.2 = 7466 ∨ result.1.2.2 = 7467 := by
  obtain ⟨hash, member, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
  obtain ⟨last, lastMember, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp tail
  exact encLinkLoopSamples_terminal attempts _ suffix encLinkIndices _ _ last lastMember

/-- The prepared typed buffers give the exact shared link source law. -/
theorem onlineLinkMemory_sharedSource [FieldCertificate]
    (attempts limit : Nat) (memory : Memory) (state : SharedOracleSource) (coin : OfflineCoin) (input : AffineInput)
    (ready : OnlineLinkMemory memory state coin input limit)
    (room : 2 * (limit + 508) + 256 < 2 ^ 110)
    (hashRoom : 2 * (state.family.hash.length + 1) + 256 < 2 ^ 110) :
    (encLinkSamples attempts memory state.family coin.2.2 []).map
      (fun linked => if linked.1.2.2 = 7466 then
        some (encLinkOutputMac linked.1.1 onlineLinkedBase, ({state with family := linked.2} : SharedOracleSource)) else none) =
      runSampledCutoff (sharedSourceCutoff attempts)
        (sharedCombinedProgram (SimulatorMachine.link ((sharedOfflineFrame coin).selectedCurve input)
          input ((sharedOfflineFrame coin).labels input).inputMac)).toOracle state := by
  have operand : memory.registers 8 = hashKeyWord (((sharedOfflineFrame coin).selectedCurve input).result input) := by
    rw [sharedOfflineFrame_curveResult]
    exact ready.operand
  have typed := encLinkSamples_typed attempts memory state.family ((sharedOfflineFrame coin).selectedCurve input)
    input ((sharedOfflineFrame coin).labels input).inputMac onlineOriginalBase onlineLinkedBase limit []
    ready.represented.family ready.represented.capacity operand ready.inputPointer ready.inputX ready.inputY
    ready.outputPointer (by decide) (by decide) (by decide) (by decide) ready.labels
    (by intro i hi j hj; unfold onlineOriginalBase onlineLinkedBase; omega)
    ready.represented.counts.1 ready.represented.counts.2.1 room hashRoom ready.wire
  rw [sharedOfflineFrame_curveResult] at typed
  rw [← encLinkProgram_sharedCutoff attempts _ input _ state.family state.metadata, ← typed, PMF.map_comp]
  change (encLinkSamples attempts memory state.family coin.2.2 []).bind _ = _
  apply ThreePhase.bind_eq_on_support
  intro linked supported
  rcases encLinkSamples_terminal attempts memory state.family coin.2.2 [] linked supported with normal | failed
  · simp [Function.comp_def, encLinkTypedValue, normal]
  · simp [Function.comp_def, encLinkTypedValue, failed]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
