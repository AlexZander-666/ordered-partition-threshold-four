import OrderedPartitions.FourPoleFiniteData.Counts256

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs256 : signsOK coeffs256 64 boxes256 = true := by
  decide +kernel
theorem root256 : Bracketed 256 boxes256 :=
  bracketed original256 (by decide +kernel) (signAt_of_signsOK signs256)

private theorem signs257 : signsOK coeffs257 64 boxes257 = true := by
  decide +kernel
theorem root257 : Bracketed 257 boxes257 :=
  bracketed original257 (by decide +kernel) (signAt_of_signsOK signs257)

private theorem signs258 : signsOK coeffs258 64 boxes258 = true := by
  decide +kernel
theorem root258 : Bracketed 258 boxes258 :=
  bracketed original258 (by decide +kernel) (signAt_of_signsOK signs258)

private theorem signs259 : signsOK coeffs259 64 boxes259 = true := by
  decide +kernel
theorem root259 : Bracketed 259 boxes259 :=
  bracketed original259 (by decide +kernel) (signAt_of_signsOK signs259)

private theorem signs260 : signsOK coeffs260 65 boxes260 = true := by
  decide +kernel
theorem root260 : Bracketed 260 boxes260 :=
  bracketed original260 (by decide +kernel) (signAt_of_signsOK signs260)

private theorem signs261 : signsOK coeffs261 65 boxes261 = true := by
  decide +kernel
theorem root261 : Bracketed 261 boxes261 :=
  bracketed original261 (by decide +kernel) (signAt_of_signsOK signs261)

private theorem signs262 : signsOK coeffs262 65 boxes262 = true := by
  decide +kernel
theorem root262 : Bracketed 262 boxes262 :=
  bracketed original262 (by decide +kernel) (signAt_of_signsOK signs262)

private theorem signs263 : signsOK coeffs263 65 boxes263 = true := by
  decide +kernel
theorem root263 : Bracketed 263 boxes263 :=
  bracketed original263 (by decide +kernel) (signAt_of_signsOK signs263)


#print axioms root263

end OrderedPartitions.FourPoleFinite
