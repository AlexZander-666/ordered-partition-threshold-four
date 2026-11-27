import OrderedPartitions.FourPoleFiniteData.Roots248
import OrderedPartitions.FourPoleFiniteData.Roots256

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair248Gap1 :
    RootTracking.OrderedPair (248/4) (row 248 4) (row 249 4) :=
  stay_pair (by decide) root248 root249 (by decide +kernel)

theorem pair248Gap2 :
    RootTracking.OrderedPair (248/4) (row 248 4) (row 250 4) :=
  stay_pair (by decide) root248 root250 (by decide +kernel)

theorem pair248Gap3 :
    RootTracking.OrderedPair (248/4) (row 248 4) (row 251 4) :=
  stay_pair (by decide) root248 root251 (by decide +kernel)

theorem pair248Gap4 :
    RootTracking.OrderedPair (248/4) (row 248 4) (row 252 4) :=
  rise_pair (by decide) root248 root252 (by decide +kernel)

theorem pair249Gap1 :
    RootTracking.OrderedPair (249/4) (row 249 4) (row 250 4) :=
  stay_pair (by decide) root249 root250 (by decide +kernel)

theorem pair249Gap2 :
    RootTracking.OrderedPair (249/4) (row 249 4) (row 251 4) :=
  stay_pair (by decide) root249 root251 (by decide +kernel)

theorem pair249Gap3 :
    RootTracking.OrderedPair (249/4) (row 249 4) (row 252 4) :=
  rise_pair (by decide) root249 root252 (by decide +kernel)

theorem pair249Gap4 :
    RootTracking.OrderedPair (249/4) (row 249 4) (row 253 4) :=
  rise_pair (by decide) root249 root253 (by decide +kernel)

theorem pair250Gap1 :
    RootTracking.OrderedPair (250/4) (row 250 4) (row 251 4) :=
  stay_pair (by decide) root250 root251 (by decide +kernel)

theorem pair250Gap2 :
    RootTracking.OrderedPair (250/4) (row 250 4) (row 252 4) :=
  rise_pair (by decide) root250 root252 (by decide +kernel)

theorem pair250Gap3 :
    RootTracking.OrderedPair (250/4) (row 250 4) (row 253 4) :=
  rise_pair (by decide) root250 root253 (by decide +kernel)

theorem pair250Gap4 :
    RootTracking.OrderedPair (250/4) (row 250 4) (row 254 4) :=
  rise_pair (by decide) root250 root254 (by decide +kernel)

theorem pair251Gap1 :
    RootTracking.OrderedPair (251/4) (row 251 4) (row 252 4) :=
  rise_pair (by decide) root251 root252 (by decide +kernel)

theorem pair251Gap2 :
    RootTracking.OrderedPair (251/4) (row 251 4) (row 253 4) :=
  rise_pair (by decide) root251 root253 (by decide +kernel)

theorem pair251Gap3 :
    RootTracking.OrderedPair (251/4) (row 251 4) (row 254 4) :=
  rise_pair (by decide) root251 root254 (by decide +kernel)

theorem pair251Gap4 :
    RootTracking.OrderedPair (251/4) (row 251 4) (row 255 4) :=
  rise_pair (by decide) root251 root255 (by decide +kernel)

theorem pair252Gap1 :
    RootTracking.OrderedPair (252/4) (row 252 4) (row 253 4) :=
  stay_pair (by decide) root252 root253 (by decide +kernel)

theorem pair252Gap2 :
    RootTracking.OrderedPair (252/4) (row 252 4) (row 254 4) :=
  stay_pair (by decide) root252 root254 (by decide +kernel)

theorem pair252Gap3 :
    RootTracking.OrderedPair (252/4) (row 252 4) (row 255 4) :=
  stay_pair (by decide) root252 root255 (by decide +kernel)

theorem pair252Gap4 :
    RootTracking.OrderedPair (252/4) (row 252 4) (row 256 4) :=
  rise_pair (by decide) root252 root256 (by decide +kernel)

theorem pair253Gap1 :
    RootTracking.OrderedPair (253/4) (row 253 4) (row 254 4) :=
  stay_pair (by decide) root253 root254 (by decide +kernel)

theorem pair253Gap2 :
    RootTracking.OrderedPair (253/4) (row 253 4) (row 255 4) :=
  stay_pair (by decide) root253 root255 (by decide +kernel)

theorem pair253Gap3 :
    RootTracking.OrderedPair (253/4) (row 253 4) (row 256 4) :=
  rise_pair (by decide) root253 root256 (by decide +kernel)

theorem pair253Gap4 :
    RootTracking.OrderedPair (253/4) (row 253 4) (row 257 4) :=
  rise_pair (by decide) root253 root257 (by decide +kernel)

theorem pair254Gap1 :
    RootTracking.OrderedPair (254/4) (row 254 4) (row 255 4) :=
  stay_pair (by decide) root254 root255 (by decide +kernel)

theorem pair254Gap2 :
    RootTracking.OrderedPair (254/4) (row 254 4) (row 256 4) :=
  rise_pair (by decide) root254 root256 (by decide +kernel)

theorem pair254Gap3 :
    RootTracking.OrderedPair (254/4) (row 254 4) (row 257 4) :=
  rise_pair (by decide) root254 root257 (by decide +kernel)

theorem pair254Gap4 :
    RootTracking.OrderedPair (254/4) (row 254 4) (row 258 4) :=
  rise_pair (by decide) root254 root258 (by decide +kernel)

theorem pair255Gap1 :
    RootTracking.OrderedPair (255/4) (row 255 4) (row 256 4) :=
  rise_pair (by decide) root255 root256 (by decide +kernel)

theorem pair255Gap2 :
    RootTracking.OrderedPair (255/4) (row 255 4) (row 257 4) :=
  rise_pair (by decide) root255 root257 (by decide +kernel)

theorem pair255Gap3 :
    RootTracking.OrderedPair (255/4) (row 255 4) (row 258 4) :=
  rise_pair (by decide) root255 root258 (by decide +kernel)

theorem pair255Gap4 :
    RootTracking.OrderedPair (255/4) (row 255 4) (row 259 4) :=
  rise_pair (by decide) root255 root259 (by decide +kernel)

theorem range248Gap1 (n : ℕ) (lo : 248 ≤ n) (hi : n ≤ 255) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair248Gap1
  · exact pair249Gap1
  · exact pair250Gap1
  · exact pair251Gap1
  · exact pair252Gap1
  · exact pair253Gap1
  · exact pair254Gap1
  · exact pair255Gap1

theorem range248Gap2 (n : ℕ) (lo : 248 ≤ n) (hi : n ≤ 255) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair248Gap2
  · exact pair249Gap2
  · exact pair250Gap2
  · exact pair251Gap2
  · exact pair252Gap2
  · exact pair253Gap2
  · exact pair254Gap2
  · exact pair255Gap2

theorem range248Gap3 (n : ℕ) (lo : 248 ≤ n) (hi : n ≤ 255) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair248Gap3
  · exact pair249Gap3
  · exact pair250Gap3
  · exact pair251Gap3
  · exact pair252Gap3
  · exact pair253Gap3
  · exact pair254Gap3
  · exact pair255Gap3

theorem range248Gap4 (n : ℕ) (lo : 248 ≤ n) (hi : n ≤ 255) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair248Gap4
  · exact pair249Gap4
  · exact pair250Gap4
  · exact pair251Gap4
  · exact pair252Gap4
  · exact pair253Gap4
  · exact pair254Gap4
  · exact pair255Gap4


#print axioms range248Gap1
#print axioms range248Gap2
#print axioms range248Gap3
#print axioms range248Gap4

end OrderedPartitions.FourPoleFinite
