import OrderedPartitions.FourPoleFiniteData.Counts248

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem signs248 : signsOK coeffs248 62 boxes248 = true := by
  decide +kernel
theorem root248 : Bracketed 248 boxes248 :=
  bracketed original248 (by decide +kernel) (signAt_of_signsOK signs248)

private theorem signs249 : signsOK coeffs249 62 boxes249 = true := by
  decide +kernel
theorem root249 : Bracketed 249 boxes249 :=
  bracketed original249 (by decide +kernel) (signAt_of_signsOK signs249)

private theorem signs250 : signsOK coeffs250 62 boxes250 = true := by
  decide +kernel
theorem root250 : Bracketed 250 boxes250 :=
  bracketed original250 (by decide +kernel) (signAt_of_signsOK signs250)

private theorem signs251 : signsOK coeffs251 62 boxes251 = true := by
  decide +kernel
theorem root251 : Bracketed 251 boxes251 :=
  bracketed original251 (by decide +kernel) (signAt_of_signsOK signs251)

private theorem signs252 : signsOK coeffs252 63 boxes252 = true := by
  decide +kernel
theorem root252 : Bracketed 252 boxes252 :=
  bracketed original252 (by decide +kernel) (signAt_of_signsOK signs252)

private theorem signs253 : signsOK coeffs253 63 boxes253 = true := by
  decide +kernel
theorem root253 : Bracketed 253 boxes253 :=
  bracketed original253 (by decide +kernel) (signAt_of_signsOK signs253)

private theorem signs254 : signsOK coeffs254 63 boxes254 = true := by
  decide +kernel
theorem root254 : Bracketed 254 boxes254 :=
  bracketed original254 (by decide +kernel) (signAt_of_signsOK signs254)

private theorem signs255 : signsOK coeffs255 63 boxes255 = true := by
  decide +kernel
theorem root255 : Bracketed 255 boxes255 :=
  bracketed original255 (by decide +kernel) (signAt_of_signsOK signs255)


#print axioms root255

end OrderedPartitions.FourPoleFinite
