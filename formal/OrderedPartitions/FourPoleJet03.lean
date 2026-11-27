import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness3 : Witness := ⟨(29718842241/31250000000),(199/100000000000000),(701/100000000000000),(373312910896699/100000000000000),(373312910897201/100000000000000),(1147547462660199/100000000000000),(1147547462660701/100000000000000)⟩
theorem rightJets3 : verifiedJet cell3 cell3.right rightWitness3 = true := by decide +kernel
def leftWitness3 : Witness := ⟨(210308530959/200000000000),(99/100000000000000),(601/100000000000000),(428204130480199/100000000000000),(428204130480701/100000000000000),(1254400977214199/100000000000000),(1254400977214701/100000000000000)⟩
theorem leftJets3 : verifiedJet cell3 cell3.left leftWitness3 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
