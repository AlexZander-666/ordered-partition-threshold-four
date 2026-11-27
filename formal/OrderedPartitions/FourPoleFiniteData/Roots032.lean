import OrderedPartitions.FourPoleFiniteData.Counts032

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs32 : signsOK coeffs32 8 boxes32 = true := by
  decide +kernel
theorem root32 : Bracketed 32 boxes32 :=
  bracketed original32 (by decide +kernel) (signAt_of_signsOK signs32)

private theorem signs33 : signsOK coeffs33 8 boxes33 = true := by
  decide +kernel
theorem root33 : Bracketed 33 boxes33 :=
  bracketed original33 (by decide +kernel) (signAt_of_signsOK signs33)

private theorem signs34 : signsOK coeffs34 8 boxes34 = true := by
  decide +kernel
theorem root34 : Bracketed 34 boxes34 :=
  bracketed original34 (by decide +kernel) (signAt_of_signsOK signs34)

private theorem signs35 : signsOK coeffs35 8 boxes35 = true := by
  decide +kernel
theorem root35 : Bracketed 35 boxes35 :=
  bracketed original35 (by decide +kernel) (signAt_of_signsOK signs35)

private theorem signs36 : signsOK coeffs36 9 boxes36 = true := by
  decide +kernel
theorem root36 : Bracketed 36 boxes36 :=
  bracketed original36 (by decide +kernel) (signAt_of_signsOK signs36)

private theorem signs37 : signsOK coeffs37 9 boxes37 = true := by
  decide +kernel
theorem root37 : Bracketed 37 boxes37 :=
  bracketed original37 (by decide +kernel) (signAt_of_signsOK signs37)

private theorem signs38 : signsOK coeffs38 9 boxes38 = true := by
  decide +kernel
theorem root38 : Bracketed 38 boxes38 :=
  bracketed original38 (by decide +kernel) (signAt_of_signsOK signs38)

private theorem signs39 : signsOK coeffs39 9 boxes39 = true := by
  decide +kernel
theorem root39 : Bracketed 39 boxes39 :=
  bracketed original39 (by decide +kernel) (signAt_of_signsOK signs39)


#print axioms root39

end OrderedPartitions.FourPoleFinite
