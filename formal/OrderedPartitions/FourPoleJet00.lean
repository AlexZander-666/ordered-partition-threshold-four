import OrderedPartitions.FourPoleRationalJets
namespace OrderedPartitions.FourPole.Box
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def rightWitness0 : Witness := ⟨(989743972641/1000000000000),(-1/100000000000000),(501/100000000000000),(394534051289199/100000000000000),(394534051289701/100000000000000),(1189055421719799/100000000000000),(1189055421720301/100000000000000)⟩
theorem rightJets0 : verifiedJet cell0 cell0.right rightWitness0 = true := by decide +kernel
def leftWitness0 : Witness := ⟨(1010362337919/1000000000000),(-1/100000000000000),(501/100000000000000),(405541049473699/100000000000000),(405541049474201/100000000000000),(1211044583431599/100000000000000),(1211044583432101/100000000000000)⟩
theorem leftJets0 : verifiedJet cell0 cell0.left leftWitness0 = true := by decide +kernel
end OrderedPartitions.FourPole.Box
