import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness7 : Witness := ⟨(866354835639/1000000000000),(-1/100000000000000),(401/100000000000000),(292547545930199/100000000000000),(292547545930701/100000000000000),(1030157221080299/100000000000000),(1030157221080801/100000000000000)⟩
theorem rightJets7 : verifiedJet cell7 cell7.right rightWitness7 = true := by decide +kernel
def leftWitness7 : Witness := ⟨(1156640488347/1000000000000),(199/100000000000000),(701/100000000000000),(493086072126799/100000000000000),(493086072127301/100000000000000),(1345570722273099/100000000000000),(1345570722273601/100000000000000)⟩
theorem leftJets7 : verifiedJet cell7 cell7.left leftWitness7 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
