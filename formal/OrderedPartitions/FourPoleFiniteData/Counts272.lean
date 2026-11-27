import OrderedPartitions.FourPoleFiniteData.Arithmetic272
import OrderedPartitions.FourPoleFiniteData.Counts264

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem checkedHistory272 : HistoryOK 272 history272 :=
  historyPush checkedHistory271 checkedWeights272 checkedRow272
theorem original272 : poly coeffs272 = row 272 4 :=
  head_original (checkedHistory272)

theorem checkedHistory273 : HistoryOK 273 history273 :=
  historyPush checkedHistory272 checkedWeights273 checkedRow273
theorem original273 : poly coeffs273 = row 273 4 :=
  head_original (checkedHistory273)

theorem checkedHistory274 : HistoryOK 274 history274 :=
  historyPush checkedHistory273 checkedWeights274 checkedRow274
theorem original274 : poly coeffs274 = row 274 4 :=
  head_original (checkedHistory274)

theorem checkedHistory275 : HistoryOK 275 history275 :=
  historyPush checkedHistory274 checkedWeights275 checkedRow275
theorem original275 : poly coeffs275 = row 275 4 :=
  head_original (checkedHistory275)

theorem checkedHistory276 : HistoryOK 276 history276 :=
  historyPush checkedHistory275 checkedWeights276 checkedRow276
theorem original276 : poly coeffs276 = row 276 4 :=
  head_original (checkedHistory276)

theorem checkedHistory277 : HistoryOK 277 history277 :=
  historyPush checkedHistory276 checkedWeights277 checkedRow277
theorem original277 : poly coeffs277 = row 277 4 :=
  head_original (checkedHistory277)

theorem checkedHistory278 : HistoryOK 278 history278 :=
  historyPush checkedHistory277 checkedWeights278 checkedRow278
theorem original278 : poly coeffs278 = row 278 4 :=
  head_original (checkedHistory278)

theorem checkedHistory279 : HistoryOK 279 history279 :=
  historyPush checkedHistory278 checkedWeights279 checkedRow279
theorem original279 : poly coeffs279 = row 279 4 :=
  head_original (checkedHistory279)


#print axioms original279

end OrderedPartitions.FourPoleFinite
