import Proof.Privacy.Simulator.Arithmetic.SharedSourceTotalLaw

namespace Kriterion.ArgoMAC.ArithmeticSimulator
open BN254 Cryptography Cryptography.Assumptions Security Security.SimulatorMachine Security.SharedSimulatorMachine
noncomputable section

/-- The complete finite source includes offline sampling, both public phases, online sampling, and every oracle cutoff. -/
def sharedFiniteSourceDecision [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : SimulatorSampling.OfflineCoin → Shared.Simulator.State)
    (choose : SimulatorSampling.OfflineCoin → OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : SimulatorSampling.OfflineCoin → First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (source : SimulatorSampling.OfflineCoin → SharedOracleSource) : PMF Bool :=
  (SimulatorSampling.offline.total attempts).law.bind fun coin =>
    (runSampledCutoff (sharedSourceCutoff attempts)
      (sharedAdaptiveTotalProgram attempts (frame coin) (choose coin) input output (decide coin)) (source coin)).map
        (fun result => (result.map Prod.fst).getD false)

/-- The exact source uses the same adaptive program with exact private sampling and eager oracle completion. -/
def sharedExactSourceDecision [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat}
    (frame : SimulatorSampling.OfflineCoin → Shared.Simulator.State)
    (choose : SimulatorSampling.OfflineCoin → OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : SimulatorSampling.OfflineCoin → First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (source : SimulatorSampling.OfflineCoin → SharedOracleSource) : PMF Bool :=
  SimulatorSampling.offline.law.bind fun coin =>
    (sharedSourceCompletion (source coin)).bind fun oracle =>
      ((sharedAdaptiveProgram (frame coin) (choose coin) input output (decide coin)).run
        SharedSimulatorMachine.combinedEager oracle).map Prod.fst

/-- The whole finite source consumes at most 838389 private draws and at most 836423 internal
oracle operations, which the stated 1674813 draw allowance covers. -/
theorem sharedFiniteSourceDecision_law [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : SimulatorSampling.OfflineCoin → Shared.Simulator.State)
    (choose : SimulatorSampling.OfflineCoin → OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : SimulatorSampling.OfflineCoin → First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (source : SimulatorSampling.OfflineCoin → SharedOracleSource) :
    TotalLaw attempts (1674813 + firstBudget + secondBudget)
      (sharedExactSourceDecision frame choose input output decide source)
      (sharedFiniteSourceDecision attempts frame choose input output decide source) := by
  have law := (SimulatorSampling.Code.total_law attempts SimulatorSampling.offline).bind (fun coin =>
    sharedAdaptiveTotalSource_law attempts (frame coin) (choose coin) input output (decide coin) (source coin))
  exact law.weaken (by omega)

/-- The complete finite-source decision error has an explicit numerical bound. -/
theorem sharedFiniteSourceDecision_bound [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat} (attempts : Nat)
    (frame : SimulatorSampling.OfflineCoin → Shared.Simulator.State)
    (choose : SimulatorSampling.OfflineCoin → OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : SimulatorSampling.OfflineCoin → First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (source : SimulatorSampling.OfflineCoin → SharedOracleSource) :
    advantage (sharedFiniteSourceDecision attempts frame choose input output decide source)
      (sharedExactSourceDecision frame choose input output decide source) ≤
      (1674813 + firstBudget + secondBudget) * (2 : ℝ)⁻¹ ^ attempts := by
  have bound := (sharedFiniteSourceDecision_law attempts frame choose input output decide source).advantage
  unfold advantage at bound ⊢
  rw [abs_sub_comm]
  simpa only [Nat.cast_add, Nat.cast_ofNat] using bound

/-- The full private and oracle source loss fits the final challenge allowance. -/
theorem sharedFiniteSourceDecision_allowance [FieldCertificate] [GroupCertificate]
    {First : Type} {firstBudget secondBudget : Nat}
    (frame : SimulatorSampling.OfflineCoin → Shared.Simulator.State)
    (choose : SimulatorSampling.OfflineCoin → OracleProgram sharedSpec First firstBudget)
    (input : First → AffineInput) (output : First → Option Point)
    (decide : SimulatorSampling.OfflineCoin → First → Garbling.Labels → OracleProgram sharedSpec Bool secondBudget)
    (source : SimulatorSampling.OfflineCoin → SharedOracleSource) :
    advantage (sharedFiniteSourceDecision 256 frame choose input output decide source)
      (sharedExactSourceDecision frame choose input output decide source) ≤
      (2138378 + (firstBudget + secondBudget)) / (2 : ℝ) ^ 256 := by
  have bound := sharedFiniteSourceDecision_bound 256 frame choose input output decide source
  have positive : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ 256 := by positivity
  calc
    _ ≤ (1674813 + firstBudget + secondBudget) * (2 : ℝ)⁻¹ ^ 256 := bound
    _ ≤ (2138378 + (firstBudget + secondBudget)) * (2 : ℝ)⁻¹ ^ 256 := mul_le_mul_of_nonneg_right (by linarith) positive
    _ = _ := by rw [inv_pow, div_eq_mul_inv]

end
end Kriterion.ArgoMAC.ArithmeticSimulator
