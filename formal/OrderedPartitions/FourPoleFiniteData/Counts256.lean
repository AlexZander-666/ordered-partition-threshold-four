import OrderedPartitions.FourPoleFiniteData.Arithmetic256
import OrderedPartitions.FourPoleFiniteData.Counts248

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory256 : HistoryOK 256 history256 :=
  historyPush checkedHistory255 checkedWeights256 checkedRow256
theorem original256 : poly coeffs256 = row 256 4 :=
  head_original (checkedHistory256)

theorem checkedHistory257 : HistoryOK 257 history257 :=
  historyPush checkedHistory256 checkedWeights257 checkedRow257
theorem original257 : poly coeffs257 = row 257 4 :=
  head_original (checkedHistory257)

theorem checkedHistory258 : HistoryOK 258 history258 :=
  historyPush checkedHistory257 checkedWeights258 checkedRow258
theorem original258 : poly coeffs258 = row 258 4 :=
  head_original (checkedHistory258)

theorem checkedHistory259 : HistoryOK 259 history259 :=
  historyPush checkedHistory258 checkedWeights259 checkedRow259
theorem original259 : poly coeffs259 = row 259 4 :=
  head_original (checkedHistory259)

theorem checkedHistory260 : HistoryOK 260 history260 :=
  historyPush checkedHistory259 checkedWeights260 checkedRow260
theorem original260 : poly coeffs260 = row 260 4 :=
  head_original (checkedHistory260)

theorem checkedHistory261 : HistoryOK 261 history261 :=
  historyPush checkedHistory260 checkedWeights261 checkedRow261
theorem original261 : poly coeffs261 = row 261 4 :=
  head_original (checkedHistory261)

theorem checkedHistory262 : HistoryOK 262 history262 :=
  historyPush checkedHistory261 checkedWeights262 checkedRow262
theorem original262 : poly coeffs262 = row 262 4 :=
  head_original (checkedHistory262)

theorem checkedHistory263 : HistoryOK 263 history263 :=
  historyPush checkedHistory262 checkedWeights263 checkedRow263
theorem original263 : poly coeffs263 = row 263 4 :=
  head_original (checkedHistory263)


#print axioms original263

end OrderedPartitions.FourPoleFinite
