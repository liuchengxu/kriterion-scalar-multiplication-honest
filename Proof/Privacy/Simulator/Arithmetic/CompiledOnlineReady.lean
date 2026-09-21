import Proof.Privacy.Simulator.Arithmetic.OnlineJoint
import Proof.Privacy.Simulator.Arithmetic.CompiledDecisionProtocol
import Proof.Privacy.Simulator.Arithmetic.SharedOnlineGrowth

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.BoundedMachine Security Security.SharedSimulatorMachine
noncomputable section
attribute [local irreducible] onlineMemoryJoint compiledMachine

/-- The accepted online joint supplies all counters and the exact decision reserve. -/
theorem compiledOnlineJoint_ready [FieldCertificate] [GroupCertificate]
    (coin : SimulatorSampling.OfflineCoin) (input : AffineInput) (output : Option Point)
    (used setupSpent reserve : Nat) (state : State) (source : SharedOracleSource)
    (setup : setupSpent ≤ 2 ^ 30 + 605084290688 + 2)
    (initial : CompiledPublicReady 256 0 0 0 setupSpent used state source)
    (actual : PMF (Configuration 290305300 × Nat))
    (executed : ClosedRun (onlineMachine 256) 0
      (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output output))
      reserve actual)
    (charged : reserve ≤ 2153421270 * 256 + 46833536 * (used + 836423) + 6 * used + 235015545)
    (machineLaw : (onlineMemoryJoint 256 coin input output
      (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output output)) source).map
      (Option.map fun result => result.2.1) = actual.map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none))
    (sourceLaw : (onlineMemoryJoint 256 coin input output
      (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output output)) source).map
      (Option.map fun result => (result.1, result.2.2)) =
      runSampledCutoff (sharedSourceCutoff 256) (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input output) source)
    (stored : ∀ result, some result ∈ (onlineMemoryJoint 256 coin input output
      (compiledOnlineMemory state.memory (GarbledCircuit.SimulatorProtocol.affine input ++ GarbledCircuit.SimulatorProtocol.output output)) source).support →
      OracleFamilyMemory result.2.1.1.ram result.2.2.family ∧ OracleFamilyFits result.2.2.family ∧
        SharedHistoryMemory result.2.1.1.ram result.2.2.metadata)
    (labels : Garbling.Labels) (final : State) (next : SharedOracleSource)
    (member : some (labels, final, next) ∈ (compiledOnlineJoint 256 coin input output state source).support) :
    CompiledDecisionReady used final next := by
  obtain ⟨raw, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  cases raw with
  | none => simp at same
  | some raw =>
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    have sourceMember : some (raw.1, raw.2.2) ∈ (runSampledCutoff (sharedSourceCutoff 256)
        (sharedOnlineTotalProgram 256 (sharedOfflineFrame coin) input output) source).support := by
      rw [← sourceLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some raw, reached, rfl⟩
    have growth := sharedOnlineTotalProgram_growth 256 used (sharedOfflineFrame coin) input output source raw.2.2 raw.1
      (by simpa only [Nat.zero_add] using initial.memory.counts) (by simpa only [Nat.zero_add] using initial.hash) sourceMember
    have represented := stored raw reached
    have costMember : some raw.2.1 ∈ (actual.map
        (fun result => if result.1.pc = 290305298 then some (result.1.memory, result.2) else none)).support := by
      rw [← machineLaw]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨some raw, reached, rfl⟩
    obtain ⟨result, actualMember, equal⟩ := (PMF.mem_support_map_iff _ _ _).mp costMember
    have costBound : raw.2.1.2 ≤ reserve := by
      have cost := compiledOnlineSource_cost 256 reserve _ actual executed result actualMember
      split at equal
      · simp only [Option.some.injEq, Prod.mk.injEq] at equal
        have sameCost := congrArg Prod.snd equal
        exact sameCost ▸ cost
      · contradiction
    have allowance := compiledOnlineCost_allowance used setupSpent reserve setup charged
    refine ⟨⟨represented.1, represented.2.1, represented.2.2, growth.1⟩, growth.2, ?_, ?_⟩
    · simpa only [Nat.zero_add] using initial.queries
    · change state.spent + (raw.2.1.2 + 2) ≤ compiledBlockAllowance used
      have := initial.spent
      omega

end
end Kriterion.ArgoMAC.ArithmeticSimulator
