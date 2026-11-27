import OrderedPartitions.FourPoleFiniteData.Counts280

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs280 : signsOK coeffs280 70 boxes280 = true := by
  decide +kernel
theorem root280 : Bracketed 280 boxes280 :=
  bracketed original280 (by decide +kernel) (signAt_of_signsOK signs280)

private theorem signs281 : signsOK coeffs281 70 boxes281 = true := by
  decide +kernel
theorem root281 : Bracketed 281 boxes281 :=
  bracketed original281 (by decide +kernel) (signAt_of_signsOK signs281)

private theorem signs282 : signsOK coeffs282 70 boxes282 = true := by
  decide +kernel
theorem root282 : Bracketed 282 boxes282 :=
  bracketed original282 (by decide +kernel) (signAt_of_signsOK signs282)

private theorem signs283 : signsOK coeffs283 70 boxes283 = true := by
  decide +kernel
theorem root283 : Bracketed 283 boxes283 :=
  bracketed original283 (by decide +kernel) (signAt_of_signsOK signs283)

private theorem signs284 : signsOK coeffs284 71 boxes284 = true := by
  decide +kernel
theorem root284 : Bracketed 284 boxes284 :=
  bracketed original284 (by decide +kernel) (signAt_of_signsOK signs284)

private theorem signs285 : signsOK coeffs285 71 boxes285 = true := by
  decide +kernel
theorem root285 : Bracketed 285 boxes285 :=
  bracketed original285 (by decide +kernel) (signAt_of_signsOK signs285)

private theorem signs286 : signsOK coeffs286 71 boxes286 = true := by
  decide +kernel
theorem root286 : Bracketed 286 boxes286 :=
  bracketed original286 (by decide +kernel) (signAt_of_signsOK signs286)

private theorem signs287 : signsOK coeffs287 71 boxes287 = true := by
  decide +kernel
theorem root287 : Bracketed 287 boxes287 :=
  bracketed original287 (by decide +kernel) (signAt_of_signsOK signs287)


#print axioms root287

end OrderedPartitions.FourPoleFinite
