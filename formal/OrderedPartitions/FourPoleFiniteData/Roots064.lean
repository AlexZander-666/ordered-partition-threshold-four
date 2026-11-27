import OrderedPartitions.FourPoleFiniteData.Counts064

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs64 : signsOK coeffs64 16 boxes64 = true := by
  decide +kernel
theorem root64 : Bracketed 64 boxes64 :=
  bracketed original64 (by decide +kernel) (signAt_of_signsOK signs64)

private theorem signs65 : signsOK coeffs65 16 boxes65 = true := by
  decide +kernel
theorem root65 : Bracketed 65 boxes65 :=
  bracketed original65 (by decide +kernel) (signAt_of_signsOK signs65)

private theorem signs66 : signsOK coeffs66 16 boxes66 = true := by
  decide +kernel
theorem root66 : Bracketed 66 boxes66 :=
  bracketed original66 (by decide +kernel) (signAt_of_signsOK signs66)

private theorem signs67 : signsOK coeffs67 16 boxes67 = true := by
  decide +kernel
theorem root67 : Bracketed 67 boxes67 :=
  bracketed original67 (by decide +kernel) (signAt_of_signsOK signs67)

private theorem signs68 : signsOK coeffs68 17 boxes68 = true := by
  decide +kernel
theorem root68 : Bracketed 68 boxes68 :=
  bracketed original68 (by decide +kernel) (signAt_of_signsOK signs68)

private theorem signs69 : signsOK coeffs69 17 boxes69 = true := by
  decide +kernel
theorem root69 : Bracketed 69 boxes69 :=
  bracketed original69 (by decide +kernel) (signAt_of_signsOK signs69)

private theorem signs70 : signsOK coeffs70 17 boxes70 = true := by
  decide +kernel
theorem root70 : Bracketed 70 boxes70 :=
  bracketed original70 (by decide +kernel) (signAt_of_signsOK signs70)

private theorem signs71 : signsOK coeffs71 17 boxes71 = true := by
  decide +kernel
theorem root71 : Bracketed 71 boxes71 :=
  bracketed original71 (by decide +kernel) (signAt_of_signsOK signs71)


#print axioms root71

end OrderedPartitions.FourPoleFinite
