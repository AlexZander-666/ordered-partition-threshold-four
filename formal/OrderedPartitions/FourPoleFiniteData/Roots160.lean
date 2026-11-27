import OrderedPartitions.FourPoleFiniteData.Counts160

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs160 : signsOK coeffs160 40 boxes160 = true := by
  decide +kernel
theorem root160 : Bracketed 160 boxes160 :=
  bracketed original160 (by decide +kernel) (signAt_of_signsOK signs160)

private theorem signs161 : signsOK coeffs161 40 boxes161 = true := by
  decide +kernel
theorem root161 : Bracketed 161 boxes161 :=
  bracketed original161 (by decide +kernel) (signAt_of_signsOK signs161)

private theorem signs162 : signsOK coeffs162 40 boxes162 = true := by
  decide +kernel
theorem root162 : Bracketed 162 boxes162 :=
  bracketed original162 (by decide +kernel) (signAt_of_signsOK signs162)

private theorem signs163 : signsOK coeffs163 40 boxes163 = true := by
  decide +kernel
theorem root163 : Bracketed 163 boxes163 :=
  bracketed original163 (by decide +kernel) (signAt_of_signsOK signs163)

private theorem signs164 : signsOK coeffs164 41 boxes164 = true := by
  decide +kernel
theorem root164 : Bracketed 164 boxes164 :=
  bracketed original164 (by decide +kernel) (signAt_of_signsOK signs164)

private theorem signs165 : signsOK coeffs165 41 boxes165 = true := by
  decide +kernel
theorem root165 : Bracketed 165 boxes165 :=
  bracketed original165 (by decide +kernel) (signAt_of_signsOK signs165)

private theorem signs166 : signsOK coeffs166 41 boxes166 = true := by
  decide +kernel
theorem root166 : Bracketed 166 boxes166 :=
  bracketed original166 (by decide +kernel) (signAt_of_signsOK signs166)

private theorem signs167 : signsOK coeffs167 41 boxes167 = true := by
  decide +kernel
theorem root167 : Bracketed 167 boxes167 :=
  bracketed original167 (by decide +kernel) (signAt_of_signsOK signs167)


#print axioms root167

end OrderedPartitions.FourPoleFinite
