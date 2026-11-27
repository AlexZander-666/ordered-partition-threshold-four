import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness9 : Witness := ⟨(850318553187/1000000000000),(-1/100000000000000),(301/100000000000000),(249447699829299/100000000000000),(249447699829801/100000000000000),(981110853602099/100000000000000),(981110853602601/100000000000000)⟩
theorem rightJets9 : verifiedJet cell9 cell9.right rightWitness9 = true := by decide +kernel
def leftWitness9 : Witness := ⟨(590401601763/500000000000),(99/100000000000000),(601/100000000000000),(508953997925899/100000000000000),(508953997926401/100000000000000),(1357114933677699/100000000000000),(1357114933678201/100000000000000)⟩
theorem leftJets9 : verifiedJet cell9 cell9.left leftWitness9 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
