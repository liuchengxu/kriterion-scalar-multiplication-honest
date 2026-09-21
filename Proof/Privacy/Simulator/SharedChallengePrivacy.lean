import Proof.Privacy.Source.SharedRealSourceSum
import Proof.Privacy.Bounds.SharedMachineArithmetic
import Construction.ArgoMAC.Encoding

namespace Kriterion.ArgoMAC.Security
open BN254 Cryptography Cryptography.Assumptions GarbledCircuit
noncomputable section

/-- The adapter gives the wire adversary the exact selected Lamport blocks. -/
def sharedWireAdversary {Aux : Type}
    (adversary : AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable LamportSignature Aux) :
    AdaptiveAdversary sharedRealOracleSpec AffineInput Pipeline.PackedTable Garbling.Labels Aux := {
  State := adversary.State
  firstQueryBudget := adversary.firstQueryBudget
  secondQueryBudget := adversary.secondQueryBudget
  chooseInput := adversary.chooseInput
  decide := fun parameter table labels => adversary.decide parameter table (Lamport.selectedLabels labels.inputMac)
}


end
end Kriterion.ArgoMAC.Security
