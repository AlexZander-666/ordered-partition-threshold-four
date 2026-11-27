import OrderedPartitions.FourPoleFiniteData.Arithmetic104
import OrderedPartitions.FourPoleFiniteData.Counts096

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory104 : HistoryOK 104 history104 :=
  historyPush checkedHistory103 checkedWeights104 checkedRow104
theorem original104 : poly coeffs104 = row 104 4 :=
  head_original (checkedHistory104)

theorem checkedHistory105 : HistoryOK 105 history105 :=
  historyPush checkedHistory104 checkedWeights105 checkedRow105
theorem original105 : poly coeffs105 = row 105 4 :=
  head_original (checkedHistory105)

theorem checkedHistory106 : HistoryOK 106 history106 :=
  historyPush checkedHistory105 checkedWeights106 checkedRow106
theorem original106 : poly coeffs106 = row 106 4 :=
  head_original (checkedHistory106)

theorem checkedHistory107 : HistoryOK 107 history107 :=
  historyPush checkedHistory106 checkedWeights107 checkedRow107
theorem original107 : poly coeffs107 = row 107 4 :=
  head_original (checkedHistory107)

theorem checkedHistory108 : HistoryOK 108 history108 :=
  historyPush checkedHistory107 checkedWeights108 checkedRow108
theorem original108 : poly coeffs108 = row 108 4 :=
  head_original (checkedHistory108)

theorem checkedHistory109 : HistoryOK 109 history109 :=
  historyPush checkedHistory108 checkedWeights109 checkedRow109
theorem original109 : poly coeffs109 = row 109 4 :=
  head_original (checkedHistory109)

theorem checkedHistory110 : HistoryOK 110 history110 :=
  historyPush checkedHistory109 checkedWeights110 checkedRow110
theorem original110 : poly coeffs110 = row 110 4 :=
  head_original (checkedHistory110)

theorem checkedHistory111 : HistoryOK 111 history111 :=
  historyPush checkedHistory110 checkedWeights111 checkedRow111
theorem original111 : poly coeffs111 = row 111 4 :=
  head_original (checkedHistory111)


#print axioms original111

end OrderedPartitions.FourPoleFinite
