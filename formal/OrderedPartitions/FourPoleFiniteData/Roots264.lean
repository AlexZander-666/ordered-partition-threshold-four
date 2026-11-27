import OrderedPartitions.FourPoleFiniteData.Counts264

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs264 : signsOK coeffs264 66 boxes264 = true := by
  decide +kernel
theorem root264 : Bracketed 264 boxes264 :=
  bracketed original264 (by decide +kernel) (signAt_of_signsOK signs264)

private theorem signs265 : signsOK coeffs265 66 boxes265 = true := by
  decide +kernel
theorem root265 : Bracketed 265 boxes265 :=
  bracketed original265 (by decide +kernel) (signAt_of_signsOK signs265)

private theorem signs266 : signsOK coeffs266 66 boxes266 = true := by
  decide +kernel
theorem root266 : Bracketed 266 boxes266 :=
  bracketed original266 (by decide +kernel) (signAt_of_signsOK signs266)

private theorem signs267 : signsOK coeffs267 66 boxes267 = true := by
  decide +kernel
theorem root267 : Bracketed 267 boxes267 :=
  bracketed original267 (by decide +kernel) (signAt_of_signsOK signs267)

private theorem signs268 : signsOK coeffs268 67 boxes268 = true := by
  decide +kernel
theorem root268 : Bracketed 268 boxes268 :=
  bracketed original268 (by decide +kernel) (signAt_of_signsOK signs268)

private theorem signs269 : signsOK coeffs269 67 boxes269 = true := by
  decide +kernel
theorem root269 : Bracketed 269 boxes269 :=
  bracketed original269 (by decide +kernel) (signAt_of_signsOK signs269)

private theorem signs270 : signsOK coeffs270 67 boxes270 = true := by
  decide +kernel
theorem root270 : Bracketed 270 boxes270 :=
  bracketed original270 (by decide +kernel) (signAt_of_signsOK signs270)

private theorem signs271 : signsOK coeffs271 67 boxes271 = true := by
  decide +kernel
theorem root271 : Bracketed 271 boxes271 :=
  bracketed original271 (by decide +kernel) (signAt_of_signsOK signs271)


#print axioms root271

end OrderedPartitions.FourPoleFinite
