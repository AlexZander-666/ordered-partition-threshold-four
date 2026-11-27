import OrderedPartitions.FourPoleFiniteData.Arithmetic240
import OrderedPartitions.FourPoleFiniteData.Counts232

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory240 : HistoryOK 240 history240 :=
  historyPush checkedHistory239 checkedWeights240 checkedRow240
theorem original240 : poly coeffs240 = row 240 4 :=
  head_original (checkedHistory240)

theorem checkedHistory241 : HistoryOK 241 history241 :=
  historyPush checkedHistory240 checkedWeights241 checkedRow241
theorem original241 : poly coeffs241 = row 241 4 :=
  head_original (checkedHistory241)

theorem checkedHistory242 : HistoryOK 242 history242 :=
  historyPush checkedHistory241 checkedWeights242 checkedRow242
theorem original242 : poly coeffs242 = row 242 4 :=
  head_original (checkedHistory242)

theorem checkedHistory243 : HistoryOK 243 history243 :=
  historyPush checkedHistory242 checkedWeights243 checkedRow243
theorem original243 : poly coeffs243 = row 243 4 :=
  head_original (checkedHistory243)

theorem checkedHistory244 : HistoryOK 244 history244 :=
  historyPush checkedHistory243 checkedWeights244 checkedRow244
theorem original244 : poly coeffs244 = row 244 4 :=
  head_original (checkedHistory244)

theorem checkedHistory245 : HistoryOK 245 history245 :=
  historyPush checkedHistory244 checkedWeights245 checkedRow245
theorem original245 : poly coeffs245 = row 245 4 :=
  head_original (checkedHistory245)

theorem checkedHistory246 : HistoryOK 246 history246 :=
  historyPush checkedHistory245 checkedWeights246 checkedRow246
theorem original246 : poly coeffs246 = row 246 4 :=
  head_original (checkedHistory246)

theorem checkedHistory247 : HistoryOK 247 history247 :=
  historyPush checkedHistory246 checkedWeights247 checkedRow247
theorem original247 : poly coeffs247 = row 247 4 :=
  head_original (checkedHistory247)


#print axioms original247

end OrderedPartitions.FourPoleFinite
