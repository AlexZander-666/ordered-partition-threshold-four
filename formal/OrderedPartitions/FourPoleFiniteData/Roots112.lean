import OrderedPartitions.FourPoleFiniteData.Counts112

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs112 : signsOK coeffs112 28 boxes112 = true := by
  decide +kernel
theorem root112 : Bracketed 112 boxes112 :=
  bracketed original112 (by decide +kernel) (signAt_of_signsOK signs112)

private theorem signs113 : signsOK coeffs113 28 boxes113 = true := by
  decide +kernel
theorem root113 : Bracketed 113 boxes113 :=
  bracketed original113 (by decide +kernel) (signAt_of_signsOK signs113)

private theorem signs114 : signsOK coeffs114 28 boxes114 = true := by
  decide +kernel
theorem root114 : Bracketed 114 boxes114 :=
  bracketed original114 (by decide +kernel) (signAt_of_signsOK signs114)

private theorem signs115 : signsOK coeffs115 28 boxes115 = true := by
  decide +kernel
theorem root115 : Bracketed 115 boxes115 :=
  bracketed original115 (by decide +kernel) (signAt_of_signsOK signs115)

private theorem signs116 : signsOK coeffs116 29 boxes116 = true := by
  decide +kernel
theorem root116 : Bracketed 116 boxes116 :=
  bracketed original116 (by decide +kernel) (signAt_of_signsOK signs116)

private theorem signs117 : signsOK coeffs117 29 boxes117 = true := by
  decide +kernel
theorem root117 : Bracketed 117 boxes117 :=
  bracketed original117 (by decide +kernel) (signAt_of_signsOK signs117)

private theorem signs118 : signsOK coeffs118 29 boxes118 = true := by
  decide +kernel
theorem root118 : Bracketed 118 boxes118 :=
  bracketed original118 (by decide +kernel) (signAt_of_signsOK signs118)

private theorem signs119 : signsOK coeffs119 29 boxes119 = true := by
  decide +kernel
theorem root119 : Bracketed 119 boxes119 :=
  bracketed original119 (by decide +kernel) (signAt_of_signsOK signs119)


#print axioms root119

end OrderedPartitions.FourPoleFinite
