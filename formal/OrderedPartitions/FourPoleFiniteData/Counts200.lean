import OrderedPartitions.FourPoleFiniteData.Arithmetic200
import OrderedPartitions.FourPoleFiniteData.Counts192

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory200 : HistoryOK 200 history200 :=
  historyPush checkedHistory199 checkedWeights200 checkedRow200
theorem original200 : poly coeffs200 = row 200 4 :=
  head_original (checkedHistory200)

theorem checkedHistory201 : HistoryOK 201 history201 :=
  historyPush checkedHistory200 checkedWeights201 checkedRow201
theorem original201 : poly coeffs201 = row 201 4 :=
  head_original (checkedHistory201)

theorem checkedHistory202 : HistoryOK 202 history202 :=
  historyPush checkedHistory201 checkedWeights202 checkedRow202
theorem original202 : poly coeffs202 = row 202 4 :=
  head_original (checkedHistory202)

theorem checkedHistory203 : HistoryOK 203 history203 :=
  historyPush checkedHistory202 checkedWeights203 checkedRow203
theorem original203 : poly coeffs203 = row 203 4 :=
  head_original (checkedHistory203)

theorem checkedHistory204 : HistoryOK 204 history204 :=
  historyPush checkedHistory203 checkedWeights204 checkedRow204
theorem original204 : poly coeffs204 = row 204 4 :=
  head_original (checkedHistory204)

theorem checkedHistory205 : HistoryOK 205 history205 :=
  historyPush checkedHistory204 checkedWeights205 checkedRow205
theorem original205 : poly coeffs205 = row 205 4 :=
  head_original (checkedHistory205)

theorem checkedHistory206 : HistoryOK 206 history206 :=
  historyPush checkedHistory205 checkedWeights206 checkedRow206
theorem original206 : poly coeffs206 = row 206 4 :=
  head_original (checkedHistory206)

theorem checkedHistory207 : HistoryOK 207 history207 :=
  historyPush checkedHistory206 checkedWeights207 checkedRow207
theorem original207 : poly coeffs207 = row 207 4 :=
  head_original (checkedHistory207)


#print axioms original207

end OrderedPartitions.FourPoleFinite
