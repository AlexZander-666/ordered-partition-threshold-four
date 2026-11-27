import OrderedPartitions.FourPoleFiniteData.Arithmetic264
import OrderedPartitions.FourPoleFiniteData.Counts256

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory264 : HistoryOK 264 history264 :=
  historyPush checkedHistory263 checkedWeights264 checkedRow264
theorem original264 : poly coeffs264 = row 264 4 :=
  head_original (checkedHistory264)

theorem checkedHistory265 : HistoryOK 265 history265 :=
  historyPush checkedHistory264 checkedWeights265 checkedRow265
theorem original265 : poly coeffs265 = row 265 4 :=
  head_original (checkedHistory265)

theorem checkedHistory266 : HistoryOK 266 history266 :=
  historyPush checkedHistory265 checkedWeights266 checkedRow266
theorem original266 : poly coeffs266 = row 266 4 :=
  head_original (checkedHistory266)

theorem checkedHistory267 : HistoryOK 267 history267 :=
  historyPush checkedHistory266 checkedWeights267 checkedRow267
theorem original267 : poly coeffs267 = row 267 4 :=
  head_original (checkedHistory267)

theorem checkedHistory268 : HistoryOK 268 history268 :=
  historyPush checkedHistory267 checkedWeights268 checkedRow268
theorem original268 : poly coeffs268 = row 268 4 :=
  head_original (checkedHistory268)

theorem checkedHistory269 : HistoryOK 269 history269 :=
  historyPush checkedHistory268 checkedWeights269 checkedRow269
theorem original269 : poly coeffs269 = row 269 4 :=
  head_original (checkedHistory269)

theorem checkedHistory270 : HistoryOK 270 history270 :=
  historyPush checkedHistory269 checkedWeights270 checkedRow270
theorem original270 : poly coeffs270 = row 270 4 :=
  head_original (checkedHistory270)

theorem checkedHistory271 : HistoryOK 271 history271 :=
  historyPush checkedHistory270 checkedWeights271 checkedRow271
theorem original271 : poly coeffs271 = row 271 4 :=
  head_original (checkedHistory271)


#print axioms original271

end OrderedPartitions.FourPoleFinite
