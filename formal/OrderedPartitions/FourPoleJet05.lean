import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness5 : Witness := ⟨(901342688311/1000000000000),(-1/100000000000000),(501/100000000000000),(338585686822999/100000000000000),(338585686823501/100000000000000),(1089928558937699/100000000000000),(1089928558938201/100000000000000)⟩
theorem rightJets5 : verifiedJet cell5 cell5.right rightWitness5 = true := by decide +kernel
def leftWitness5 : Witness := ⟨(221988651169/200000000000),(299/100000000000000),(801/100000000000000),(463070991377699/100000000000000),(463070991378201/100000000000000),(1310844021096099/100000000000000),(1310844021096601/100000000000000)⟩
theorem leftJets5 : verifiedJet cell5 cell5.left leftWitness5 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
