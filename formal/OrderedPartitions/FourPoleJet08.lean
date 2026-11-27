import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness8 : Witness := ⟨(171593005453/200000000000),(-1/100000000000000),(401/100000000000000),(273357199789099/100000000000000),(273357199789601/100000000000000),(1007752686988099/100000000000000),(1007752686988601/100000000000000)⟩
theorem rightJets8 : verifiedJet cell8 cell8.right rightWitness8 = true := by decide +kernel
def leftWitness8 : Witness := ⟨(233793222891/200000000000),(299/100000000000000),(801/100000000000000),(501178168587399/100000000000000),(501178168587901/100000000000000),(1352149503431499/100000000000000),(1352149503432001/100000000000000)⟩
theorem leftJets8 : verifiedJet cell8 cell8.left leftWitness8 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
