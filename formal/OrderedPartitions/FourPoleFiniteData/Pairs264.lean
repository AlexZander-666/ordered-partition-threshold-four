import OrderedPartitions.FourPoleFiniteData.Roots264
import OrderedPartitions.FourPoleFiniteData.Roots272

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair264Gap1 :
    RootTracking.OrderedPair (264/4) (row 264 4) (row 265 4) :=
  stay_pair (by decide) root264 root265 (by decide +kernel)

theorem pair264Gap2 :
    RootTracking.OrderedPair (264/4) (row 264 4) (row 266 4) :=
  stay_pair (by decide) root264 root266 (by decide +kernel)

theorem pair264Gap3 :
    RootTracking.OrderedPair (264/4) (row 264 4) (row 267 4) :=
  stay_pair (by decide) root264 root267 (by decide +kernel)

theorem pair264Gap4 :
    RootTracking.OrderedPair (264/4) (row 264 4) (row 268 4) :=
  rise_pair (by decide) root264 root268 (by decide +kernel)

theorem pair265Gap1 :
    RootTracking.OrderedPair (265/4) (row 265 4) (row 266 4) :=
  stay_pair (by decide) root265 root266 (by decide +kernel)

theorem pair265Gap2 :
    RootTracking.OrderedPair (265/4) (row 265 4) (row 267 4) :=
  stay_pair (by decide) root265 root267 (by decide +kernel)

theorem pair265Gap3 :
    RootTracking.OrderedPair (265/4) (row 265 4) (row 268 4) :=
  rise_pair (by decide) root265 root268 (by decide +kernel)

theorem pair265Gap4 :
    RootTracking.OrderedPair (265/4) (row 265 4) (row 269 4) :=
  rise_pair (by decide) root265 root269 (by decide +kernel)

theorem pair266Gap1 :
    RootTracking.OrderedPair (266/4) (row 266 4) (row 267 4) :=
  stay_pair (by decide) root266 root267 (by decide +kernel)

theorem pair266Gap2 :
    RootTracking.OrderedPair (266/4) (row 266 4) (row 268 4) :=
  rise_pair (by decide) root266 root268 (by decide +kernel)

theorem pair266Gap3 :
    RootTracking.OrderedPair (266/4) (row 266 4) (row 269 4) :=
  rise_pair (by decide) root266 root269 (by decide +kernel)

theorem pair266Gap4 :
    RootTracking.OrderedPair (266/4) (row 266 4) (row 270 4) :=
  rise_pair (by decide) root266 root270 (by decide +kernel)

theorem pair267Gap1 :
    RootTracking.OrderedPair (267/4) (row 267 4) (row 268 4) :=
  rise_pair (by decide) root267 root268 (by decide +kernel)

theorem pair267Gap2 :
    RootTracking.OrderedPair (267/4) (row 267 4) (row 269 4) :=
  rise_pair (by decide) root267 root269 (by decide +kernel)

theorem pair267Gap3 :
    RootTracking.OrderedPair (267/4) (row 267 4) (row 270 4) :=
  rise_pair (by decide) root267 root270 (by decide +kernel)

theorem pair267Gap4 :
    RootTracking.OrderedPair (267/4) (row 267 4) (row 271 4) :=
  rise_pair (by decide) root267 root271 (by decide +kernel)

theorem pair268Gap1 :
    RootTracking.OrderedPair (268/4) (row 268 4) (row 269 4) :=
  stay_pair (by decide) root268 root269 (by decide +kernel)

theorem pair268Gap2 :
    RootTracking.OrderedPair (268/4) (row 268 4) (row 270 4) :=
  stay_pair (by decide) root268 root270 (by decide +kernel)

theorem pair268Gap3 :
    RootTracking.OrderedPair (268/4) (row 268 4) (row 271 4) :=
  stay_pair (by decide) root268 root271 (by decide +kernel)

theorem pair268Gap4 :
    RootTracking.OrderedPair (268/4) (row 268 4) (row 272 4) :=
  rise_pair (by decide) root268 root272 (by decide +kernel)

theorem pair269Gap1 :
    RootTracking.OrderedPair (269/4) (row 269 4) (row 270 4) :=
  stay_pair (by decide) root269 root270 (by decide +kernel)

theorem pair269Gap2 :
    RootTracking.OrderedPair (269/4) (row 269 4) (row 271 4) :=
  stay_pair (by decide) root269 root271 (by decide +kernel)

theorem pair269Gap3 :
    RootTracking.OrderedPair (269/4) (row 269 4) (row 272 4) :=
  rise_pair (by decide) root269 root272 (by decide +kernel)

theorem pair269Gap4 :
    RootTracking.OrderedPair (269/4) (row 269 4) (row 273 4) :=
  rise_pair (by decide) root269 root273 (by decide +kernel)

theorem pair270Gap1 :
    RootTracking.OrderedPair (270/4) (row 270 4) (row 271 4) :=
  stay_pair (by decide) root270 root271 (by decide +kernel)

theorem pair270Gap2 :
    RootTracking.OrderedPair (270/4) (row 270 4) (row 272 4) :=
  rise_pair (by decide) root270 root272 (by decide +kernel)

theorem pair270Gap3 :
    RootTracking.OrderedPair (270/4) (row 270 4) (row 273 4) :=
  rise_pair (by decide) root270 root273 (by decide +kernel)

theorem pair270Gap4 :
    RootTracking.OrderedPair (270/4) (row 270 4) (row 274 4) :=
  rise_pair (by decide) root270 root274 (by decide +kernel)

theorem pair271Gap1 :
    RootTracking.OrderedPair (271/4) (row 271 4) (row 272 4) :=
  rise_pair (by decide) root271 root272 (by decide +kernel)

theorem pair271Gap2 :
    RootTracking.OrderedPair (271/4) (row 271 4) (row 273 4) :=
  rise_pair (by decide) root271 root273 (by decide +kernel)

theorem pair271Gap3 :
    RootTracking.OrderedPair (271/4) (row 271 4) (row 274 4) :=
  rise_pair (by decide) root271 root274 (by decide +kernel)

theorem pair271Gap4 :
    RootTracking.OrderedPair (271/4) (row 271 4) (row 275 4) :=
  rise_pair (by decide) root271 root275 (by decide +kernel)

theorem range264Gap1 (n : ℕ) (lo : 264 ≤ n) (hi : n ≤ 271) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair264Gap1
  · exact pair265Gap1
  · exact pair266Gap1
  · exact pair267Gap1
  · exact pair268Gap1
  · exact pair269Gap1
  · exact pair270Gap1
  · exact pair271Gap1

theorem range264Gap2 (n : ℕ) (lo : 264 ≤ n) (hi : n ≤ 271) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair264Gap2
  · exact pair265Gap2
  · exact pair266Gap2
  · exact pair267Gap2
  · exact pair268Gap2
  · exact pair269Gap2
  · exact pair270Gap2
  · exact pair271Gap2

theorem range264Gap3 (n : ℕ) (lo : 264 ≤ n) (hi : n ≤ 271) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair264Gap3
  · exact pair265Gap3
  · exact pair266Gap3
  · exact pair267Gap3
  · exact pair268Gap3
  · exact pair269Gap3
  · exact pair270Gap3
  · exact pair271Gap3

theorem range264Gap4 (n : ℕ) (lo : 264 ≤ n) (hi : n ≤ 271) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair264Gap4
  · exact pair265Gap4
  · exact pair266Gap4
  · exact pair267Gap4
  · exact pair268Gap4
  · exact pair269Gap4
  · exact pair270Gap4
  · exact pair271Gap4


#print axioms range264Gap1
#print axioms range264Gap2
#print axioms range264Gap3
#print axioms range264Gap4

end OrderedPartitions.FourPoleFinite
