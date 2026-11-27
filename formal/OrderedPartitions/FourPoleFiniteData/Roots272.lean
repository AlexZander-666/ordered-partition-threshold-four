import OrderedPartitions.FourPoleFiniteData.Counts272

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs272 : signsOK coeffs272 68 boxes272 = true := by
  decide +kernel
theorem root272 : Bracketed 272 boxes272 :=
  bracketed original272 (by decide +kernel) (signAt_of_signsOK signs272)

private theorem signs273 : signsOK coeffs273 68 boxes273 = true := by
  decide +kernel
theorem root273 : Bracketed 273 boxes273 :=
  bracketed original273 (by decide +kernel) (signAt_of_signsOK signs273)

private theorem signs274 : signsOK coeffs274 68 boxes274 = true := by
  decide +kernel
theorem root274 : Bracketed 274 boxes274 :=
  bracketed original274 (by decide +kernel) (signAt_of_signsOK signs274)

private theorem signs275 : signsOK coeffs275 68 boxes275 = true := by
  decide +kernel
theorem root275 : Bracketed 275 boxes275 :=
  bracketed original275 (by decide +kernel) (signAt_of_signsOK signs275)

private theorem signs276 : signsOK coeffs276 69 boxes276 = true := by
  decide +kernel
theorem root276 : Bracketed 276 boxes276 :=
  bracketed original276 (by decide +kernel) (signAt_of_signsOK signs276)

private theorem signs277 : signsOK coeffs277 69 boxes277 = true := by
  decide +kernel
theorem root277 : Bracketed 277 boxes277 :=
  bracketed original277 (by decide +kernel) (signAt_of_signsOK signs277)

private theorem signs278 : signsOK coeffs278 69 boxes278 = true := by
  decide +kernel
theorem root278 : Bracketed 278 boxes278 :=
  bracketed original278 (by decide +kernel) (signAt_of_signsOK signs278)

private theorem signs279 : signsOK coeffs279 69 boxes279 = true := by
  decide +kernel
theorem root279 : Bracketed 279 boxes279 :=
  bracketed original279 (by decide +kernel) (signAt_of_signsOK signs279)


#print axioms root279

end OrderedPartitions.FourPoleFinite
