import OrderedPartitions.FourPoleFiniteData.Arithmetic280
import OrderedPartitions.FourPoleFiniteData.Counts272

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory280 : HistoryOK 280 history280 :=
  historyPush checkedHistory279 checkedWeights280 checkedRow280
theorem original280 : poly coeffs280 = row 280 4 :=
  head_original (checkedHistory280)

theorem checkedHistory281 : HistoryOK 281 history281 :=
  historyPush checkedHistory280 checkedWeights281 checkedRow281
theorem original281 : poly coeffs281 = row 281 4 :=
  head_original (checkedHistory281)

theorem checkedHistory282 : HistoryOK 282 history282 :=
  historyPush checkedHistory281 checkedWeights282 checkedRow282
theorem original282 : poly coeffs282 = row 282 4 :=
  head_original (checkedHistory282)

theorem checkedHistory283 : HistoryOK 283 history283 :=
  historyPush checkedHistory282 checkedWeights283 checkedRow283
theorem original283 : poly coeffs283 = row 283 4 :=
  head_original (checkedHistory283)

theorem checkedHistory284 : HistoryOK 284 history284 :=
  historyPush checkedHistory283 checkedWeights284 checkedRow284
theorem original284 : poly coeffs284 = row 284 4 :=
  head_original (checkedHistory284)

theorem checkedHistory285 : HistoryOK 285 history285 :=
  historyPush checkedHistory284 checkedWeights285 checkedRow285
theorem original285 : poly coeffs285 = row 285 4 :=
  head_original (checkedHistory285)

theorem checkedHistory286 : HistoryOK 286 history286 :=
  historyPush checkedHistory285 checkedWeights286 checkedRow286
theorem original286 : poly coeffs286 = row 286 4 :=
  head_original (checkedHistory286)

theorem checkedHistory287 : HistoryOK 287 history287 :=
  historyPush checkedHistory286 checkedWeights287 checkedRow287
theorem original287 : poly coeffs287 = row 287 4 :=
  head_original (checkedHistory287)


#print axioms original287

end OrderedPartitions.FourPoleFinite
