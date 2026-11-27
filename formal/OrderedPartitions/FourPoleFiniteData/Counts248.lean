import OrderedPartitions.FourPoleFiniteData.Arithmetic248
import OrderedPartitions.FourPoleFiniteData.Counts240

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory248 : HistoryOK 248 history248 :=
  historyPush checkedHistory247 checkedWeights248 checkedRow248
theorem original248 : poly coeffs248 = row 248 4 :=
  head_original (checkedHistory248)

theorem checkedHistory249 : HistoryOK 249 history249 :=
  historyPush checkedHistory248 checkedWeights249 checkedRow249
theorem original249 : poly coeffs249 = row 249 4 :=
  head_original (checkedHistory249)

theorem checkedHistory250 : HistoryOK 250 history250 :=
  historyPush checkedHistory249 checkedWeights250 checkedRow250
theorem original250 : poly coeffs250 = row 250 4 :=
  head_original (checkedHistory250)

theorem checkedHistory251 : HistoryOK 251 history251 :=
  historyPush checkedHistory250 checkedWeights251 checkedRow251
theorem original251 : poly coeffs251 = row 251 4 :=
  head_original (checkedHistory251)

theorem checkedHistory252 : HistoryOK 252 history252 :=
  historyPush checkedHistory251 checkedWeights252 checkedRow252
theorem original252 : poly coeffs252 = row 252 4 :=
  head_original (checkedHistory252)

theorem checkedHistory253 : HistoryOK 253 history253 :=
  historyPush checkedHistory252 checkedWeights253 checkedRow253
theorem original253 : poly coeffs253 = row 253 4 :=
  head_original (checkedHistory253)

theorem checkedHistory254 : HistoryOK 254 history254 :=
  historyPush checkedHistory253 checkedWeights254 checkedRow254
theorem original254 : poly coeffs254 = row 254 4 :=
  head_original (checkedHistory254)

theorem checkedHistory255 : HistoryOK 255 history255 :=
  historyPush checkedHistory254 checkedWeights255 checkedRow255
theorem original255 : poly coeffs255 = row 255 4 :=
  head_original (checkedHistory255)


#print axioms original255

end OrderedPartitions.FourPoleFinite
