import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness2 : Witness := ⟨(971777652543/1000000000000),(-1/100000000000000),(501/100000000000000),(384891985018099/100000000000000),(384891985018601/100000000000000),(1169862672335699/100000000000000),(1169862672336201/100000000000000)⟩
theorem rightJets2 : verifiedJet cell2 cell2.right rightWitness2 = true := by decide +kernel
def leftWitness2 : Witness := ⟨(205808819583/200000000000),(-1/100000000000000),(401/100000000000000),(415662392646199/100000000000000),(415662392646701/100000000000000),(1230868770273499/100000000000000),(1230868770274001/100000000000000)⟩
theorem leftJets2 : verifiedJet cell2 cell2.left leftWitness2 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
