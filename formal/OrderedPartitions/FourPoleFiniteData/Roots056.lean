import OrderedPartitions.FourPoleFiniteData.Counts056

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs56 : signsOK coeffs56 14 boxes56 = true := by
  decide +kernel
theorem root56 : Bracketed 56 boxes56 :=
  bracketed original56 (by decide +kernel) (signAt_of_signsOK signs56)

private theorem signs57 : signsOK coeffs57 14 boxes57 = true := by
  decide +kernel
theorem root57 : Bracketed 57 boxes57 :=
  bracketed original57 (by decide +kernel) (signAt_of_signsOK signs57)

private theorem signs58 : signsOK coeffs58 14 boxes58 = true := by
  decide +kernel
theorem root58 : Bracketed 58 boxes58 :=
  bracketed original58 (by decide +kernel) (signAt_of_signsOK signs58)

private theorem signs59 : signsOK coeffs59 14 boxes59 = true := by
  decide +kernel
theorem root59 : Bracketed 59 boxes59 :=
  bracketed original59 (by decide +kernel) (signAt_of_signsOK signs59)

private theorem signs60 : signsOK coeffs60 15 boxes60 = true := by
  decide +kernel
theorem root60 : Bracketed 60 boxes60 :=
  bracketed original60 (by decide +kernel) (signAt_of_signsOK signs60)

private theorem signs61 : signsOK coeffs61 15 boxes61 = true := by
  decide +kernel
theorem root61 : Bracketed 61 boxes61 :=
  bracketed original61 (by decide +kernel) (signAt_of_signsOK signs61)

private theorem signs62 : signsOK coeffs62 15 boxes62 = true := by
  decide +kernel
theorem root62 : Bracketed 62 boxes62 :=
  bracketed original62 (by decide +kernel) (signAt_of_signsOK signs62)

private theorem signs63 : signsOK coeffs63 15 boxes63 = true := by
  decide +kernel
theorem root63 : Bracketed 63 boxes63 :=
  bracketed original63 (by decide +kernel) (signAt_of_signsOK signs63)


#print axioms root63

end OrderedPartitions.FourPoleFinite
