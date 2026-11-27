import OrderedPartitions.FourPoleFiniteData.Arithmetic288
import OrderedPartitions.FourPoleFiniteData.Counts280

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory288 : HistoryOK 288 history288 :=
  historyPush checkedHistory287 checkedWeights288 checkedRow288
theorem original288 : poly coeffs288 = row 288 4 :=
  head_original (checkedHistory288)

theorem checkedHistory289 : HistoryOK 289 history289 :=
  historyPush checkedHistory288 checkedWeights289 checkedRow289
theorem original289 : poly coeffs289 = row 289 4 :=
  head_original (checkedHistory289)

theorem checkedHistory290 : HistoryOK 290 history290 :=
  historyPush checkedHistory289 checkedWeights290 checkedRow290
theorem original290 : poly coeffs290 = row 290 4 :=
  head_original (checkedHistory290)

theorem checkedHistory291 : HistoryOK 291 history291 :=
  historyPush checkedHistory290 checkedWeights291 checkedRow291
theorem original291 : poly coeffs291 = row 291 4 :=
  head_original (checkedHistory291)


#print axioms original291

end OrderedPartitions.FourPoleFinite
