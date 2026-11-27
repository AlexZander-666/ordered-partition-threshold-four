import OrderedPartitions.FourPoleFiniteData.Counts096

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs96 : signsOK coeffs96 24 boxes96 = true := by
  decide +kernel
theorem root96 : Bracketed 96 boxes96 :=
  bracketed original96 (by decide +kernel) (signAt_of_signsOK signs96)

private theorem signs97 : signsOK coeffs97 24 boxes97 = true := by
  decide +kernel
theorem root97 : Bracketed 97 boxes97 :=
  bracketed original97 (by decide +kernel) (signAt_of_signsOK signs97)

private theorem signs98 : signsOK coeffs98 24 boxes98 = true := by
  decide +kernel
theorem root98 : Bracketed 98 boxes98 :=
  bracketed original98 (by decide +kernel) (signAt_of_signsOK signs98)

private theorem signs99 : signsOK coeffs99 24 boxes99 = true := by
  decide +kernel
theorem root99 : Bracketed 99 boxes99 :=
  bracketed original99 (by decide +kernel) (signAt_of_signsOK signs99)

private theorem signs100 : signsOK coeffs100 25 boxes100 = true := by
  decide +kernel
theorem root100 : Bracketed 100 boxes100 :=
  bracketed original100 (by decide +kernel) (signAt_of_signsOK signs100)

private theorem signs101 : signsOK coeffs101 25 boxes101 = true := by
  decide +kernel
theorem root101 : Bracketed 101 boxes101 :=
  bracketed original101 (by decide +kernel) (signAt_of_signsOK signs101)

private theorem signs102 : signsOK coeffs102 25 boxes102 = true := by
  decide +kernel
theorem root102 : Bracketed 102 boxes102 :=
  bracketed original102 (by decide +kernel) (signAt_of_signsOK signs102)

private theorem signs103 : signsOK coeffs103 25 boxes103 = true := by
  decide +kernel
theorem root103 : Bracketed 103 boxes103 :=
  bracketed original103 (by decide +kernel) (signAt_of_signsOK signs103)


#print axioms root103

end OrderedPartitions.FourPoleFinite
