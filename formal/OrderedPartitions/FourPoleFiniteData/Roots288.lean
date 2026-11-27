import OrderedPartitions.FourPoleFiniteData.Counts288

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs288 : signsOK coeffs288 72 boxes288 = true := by
  decide +kernel
theorem root288 : Bracketed 288 boxes288 :=
  bracketed original288 (by decide +kernel) (signAt_of_signsOK signs288)

private theorem signs289 : signsOK coeffs289 72 boxes289 = true := by
  decide +kernel
theorem root289 : Bracketed 289 boxes289 :=
  bracketed original289 (by decide +kernel) (signAt_of_signsOK signs289)

private theorem signs290 : signsOK coeffs290 72 boxes290 = true := by
  decide +kernel
theorem root290 : Bracketed 290 boxes290 :=
  bracketed original290 (by decide +kernel) (signAt_of_signsOK signs290)

private theorem signs291 : signsOK coeffs291 72 boxes291 = true := by
  decide +kernel
theorem root291 : Bracketed 291 boxes291 :=
  bracketed original291 (by decide +kernel) (signAt_of_signsOK signs291)


#print axioms root291

end OrderedPartitions.FourPoleFinite
