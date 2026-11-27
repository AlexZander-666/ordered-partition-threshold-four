import OrderedPartitions.FourPoleFiniteData.Counts240

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs240 : signsOK coeffs240 60 boxes240 = true := by
  decide +kernel
theorem root240 : Bracketed 240 boxes240 :=
  bracketed original240 (by decide +kernel) (signAt_of_signsOK signs240)

private theorem signs241 : signsOK coeffs241 60 boxes241 = true := by
  decide +kernel
theorem root241 : Bracketed 241 boxes241 :=
  bracketed original241 (by decide +kernel) (signAt_of_signsOK signs241)

private theorem signs242 : signsOK coeffs242 60 boxes242 = true := by
  decide +kernel
theorem root242 : Bracketed 242 boxes242 :=
  bracketed original242 (by decide +kernel) (signAt_of_signsOK signs242)

private theorem signs243 : signsOK coeffs243 60 boxes243 = true := by
  decide +kernel
theorem root243 : Bracketed 243 boxes243 :=
  bracketed original243 (by decide +kernel) (signAt_of_signsOK signs243)

private theorem signs244 : signsOK coeffs244 61 boxes244 = true := by
  decide +kernel
theorem root244 : Bracketed 244 boxes244 :=
  bracketed original244 (by decide +kernel) (signAt_of_signsOK signs244)

private theorem signs245 : signsOK coeffs245 61 boxes245 = true := by
  decide +kernel
theorem root245 : Bracketed 245 boxes245 :=
  bracketed original245 (by decide +kernel) (signAt_of_signsOK signs245)

private theorem signs246 : signsOK coeffs246 61 boxes246 = true := by
  decide +kernel
theorem root246 : Bracketed 246 boxes246 :=
  bracketed original246 (by decide +kernel) (signAt_of_signsOK signs246)

private theorem signs247 : signsOK coeffs247 61 boxes247 = true := by
  decide +kernel
theorem root247 : Bracketed 247 boxes247 :=
  bracketed original247 (by decide +kernel) (signAt_of_signsOK signs247)


#print axioms root247

end OrderedPartitions.FourPoleFinite
