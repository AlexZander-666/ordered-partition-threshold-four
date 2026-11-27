import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness4 : Witness := ⟨(925007456779/1000000000000),(-1/100000000000000),(501/100000000000000),(357112901578299/100000000000000),(357112901578801/100000000000000),(1118783440127599/100000000000000),(1118783440128101/100000000000000)⟩
theorem rightJets4 : verifiedJet cell4 cell4.right rightWitness4 = true := by decide +kernel
def leftWitness4 : Witness := ⟨(1081208209931/1000000000000),(99/100000000000000),(601/100000000000000),(445485932055099/100000000000000),(445485932055601/100000000000000),(1284239291654399/100000000000000),(1284239291654901/100000000000000)⟩
theorem leftJets4 : verifiedJet cell4 cell4.left leftWitness4 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
