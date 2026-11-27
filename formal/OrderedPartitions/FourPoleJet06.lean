import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness6 : Witness := ⟨(440150086123/500000000000),(99/100000000000000),(601/100000000000000),(315342718538799/100000000000000),(315342718539301/100000000000000),(1058314157860099/100000000000000),(1058314157860601/100000000000000)⟩
theorem rightJets6 : verifiedJet cell6 cell6.right rightWitness6 = true := by decide +kernel
def leftWitness6 : Witness := ⟨(227454186647/200000000000),(199/100000000000000),(701/100000000000000),(480469858128599/100000000000000),(480469858129101/100000000000000),(1332801237322399/100000000000000),(1332801237322901/100000000000000)⟩
theorem leftJets6 : verifiedJet cell6 cell6.left leftWitness6 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
