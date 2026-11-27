import OrderedPartitions.FourPoleFiniteData.Counts232

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs232 : signsOK coeffs232 58 boxes232 = true := by
  decide +kernel
theorem root232 : Bracketed 232 boxes232 :=
  bracketed original232 (by decide +kernel) (signAt_of_signsOK signs232)

private theorem signs233 : signsOK coeffs233 58 boxes233 = true := by
  decide +kernel
theorem root233 : Bracketed 233 boxes233 :=
  bracketed original233 (by decide +kernel) (signAt_of_signsOK signs233)

private theorem signs234 : signsOK coeffs234 58 boxes234 = true := by
  decide +kernel
theorem root234 : Bracketed 234 boxes234 :=
  bracketed original234 (by decide +kernel) (signAt_of_signsOK signs234)

private theorem signs235 : signsOK coeffs235 58 boxes235 = true := by
  decide +kernel
theorem root235 : Bracketed 235 boxes235 :=
  bracketed original235 (by decide +kernel) (signAt_of_signsOK signs235)

private theorem signs236 : signsOK coeffs236 59 boxes236 = true := by
  decide +kernel
theorem root236 : Bracketed 236 boxes236 :=
  bracketed original236 (by decide +kernel) (signAt_of_signsOK signs236)

private theorem signs237 : signsOK coeffs237 59 boxes237 = true := by
  decide +kernel
theorem root237 : Bracketed 237 boxes237 :=
  bracketed original237 (by decide +kernel) (signAt_of_signsOK signs237)

private theorem signs238 : signsOK coeffs238 59 boxes238 = true := by
  decide +kernel
theorem root238 : Bracketed 238 boxes238 :=
  bracketed original238 (by decide +kernel) (signAt_of_signsOK signs238)

private theorem signs239 : signsOK coeffs239 59 boxes239 = true := by
  decide +kernel
theorem root239 : Bracketed 239 boxes239 :=
  bracketed original239 (by decide +kernel) (signAt_of_signsOK signs239)


#print axioms root239

end OrderedPartitions.FourPoleFinite
