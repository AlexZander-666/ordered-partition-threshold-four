import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness1 : Witness := ⟨(245624186761/250000000000),(-1/100000000000000),(401/100000000000000),(390663959942099/100000000000000),(390663959942601/100000000000000),(1181317312864599/100000000000000),(1181317312865101/100000000000000)⟩
theorem rightJets1 : verifiedJet cell1 cell1.right rightWitness1 = true := by decide +kernel
def leftWitness1 : Witness := ⟨(101781537499/100000000000),(199/100000000000000),(701/100000000000000),(409553692511399/100000000000000),(409553692511901/100000000000000),(1218971776382599/100000000000000),(1218971776383101/100000000000000)⟩
theorem leftJets1 : verifiedJet cell1 cell1.left leftWitness1 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
