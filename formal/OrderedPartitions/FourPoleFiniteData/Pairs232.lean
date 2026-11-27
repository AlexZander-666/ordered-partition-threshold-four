import OrderedPartitions.FourPoleFiniteData.Roots232
import OrderedPartitions.FourPoleFiniteData.Roots240

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair232Gap1 :
    RootTracking.OrderedPair (232/4) (row 232 4) (row 233 4) :=
  stay_pair (by decide) root232 root233 (by decide +kernel)

theorem pair232Gap2 :
    RootTracking.OrderedPair (232/4) (row 232 4) (row 234 4) :=
  stay_pair (by decide) root232 root234 (by decide +kernel)

theorem pair232Gap3 :
    RootTracking.OrderedPair (232/4) (row 232 4) (row 235 4) :=
  stay_pair (by decide) root232 root235 (by decide +kernel)

theorem pair232Gap4 :
    RootTracking.OrderedPair (232/4) (row 232 4) (row 236 4) :=
  rise_pair (by decide) root232 root236 (by decide +kernel)

theorem pair233Gap1 :
    RootTracking.OrderedPair (233/4) (row 233 4) (row 234 4) :=
  stay_pair (by decide) root233 root234 (by decide +kernel)

theorem pair233Gap2 :
    RootTracking.OrderedPair (233/4) (row 233 4) (row 235 4) :=
  stay_pair (by decide) root233 root235 (by decide +kernel)

theorem pair233Gap3 :
    RootTracking.OrderedPair (233/4) (row 233 4) (row 236 4) :=
  rise_pair (by decide) root233 root236 (by decide +kernel)

theorem pair233Gap4 :
    RootTracking.OrderedPair (233/4) (row 233 4) (row 237 4) :=
  rise_pair (by decide) root233 root237 (by decide +kernel)

theorem pair234Gap1 :
    RootTracking.OrderedPair (234/4) (row 234 4) (row 235 4) :=
  stay_pair (by decide) root234 root235 (by decide +kernel)

theorem pair234Gap2 :
    RootTracking.OrderedPair (234/4) (row 234 4) (row 236 4) :=
  rise_pair (by decide) root234 root236 (by decide +kernel)

theorem pair234Gap3 :
    RootTracking.OrderedPair (234/4) (row 234 4) (row 237 4) :=
  rise_pair (by decide) root234 root237 (by decide +kernel)

theorem pair234Gap4 :
    RootTracking.OrderedPair (234/4) (row 234 4) (row 238 4) :=
  rise_pair (by decide) root234 root238 (by decide +kernel)

theorem pair235Gap1 :
    RootTracking.OrderedPair (235/4) (row 235 4) (row 236 4) :=
  rise_pair (by decide) root235 root236 (by decide +kernel)

theorem pair235Gap2 :
    RootTracking.OrderedPair (235/4) (row 235 4) (row 237 4) :=
  rise_pair (by decide) root235 root237 (by decide +kernel)

theorem pair235Gap3 :
    RootTracking.OrderedPair (235/4) (row 235 4) (row 238 4) :=
  rise_pair (by decide) root235 root238 (by decide +kernel)

theorem pair235Gap4 :
    RootTracking.OrderedPair (235/4) (row 235 4) (row 239 4) :=
  rise_pair (by decide) root235 root239 (by decide +kernel)

theorem pair236Gap1 :
    RootTracking.OrderedPair (236/4) (row 236 4) (row 237 4) :=
  stay_pair (by decide) root236 root237 (by decide +kernel)

theorem pair236Gap2 :
    RootTracking.OrderedPair (236/4) (row 236 4) (row 238 4) :=
  stay_pair (by decide) root236 root238 (by decide +kernel)

theorem pair236Gap3 :
    RootTracking.OrderedPair (236/4) (row 236 4) (row 239 4) :=
  stay_pair (by decide) root236 root239 (by decide +kernel)

theorem pair236Gap4 :
    RootTracking.OrderedPair (236/4) (row 236 4) (row 240 4) :=
  rise_pair (by decide) root236 root240 (by decide +kernel)

theorem pair237Gap1 :
    RootTracking.OrderedPair (237/4) (row 237 4) (row 238 4) :=
  stay_pair (by decide) root237 root238 (by decide +kernel)

theorem pair237Gap2 :
    RootTracking.OrderedPair (237/4) (row 237 4) (row 239 4) :=
  stay_pair (by decide) root237 root239 (by decide +kernel)

theorem pair237Gap3 :
    RootTracking.OrderedPair (237/4) (row 237 4) (row 240 4) :=
  rise_pair (by decide) root237 root240 (by decide +kernel)

theorem pair237Gap4 :
    RootTracking.OrderedPair (237/4) (row 237 4) (row 241 4) :=
  rise_pair (by decide) root237 root241 (by decide +kernel)

theorem pair238Gap1 :
    RootTracking.OrderedPair (238/4) (row 238 4) (row 239 4) :=
  stay_pair (by decide) root238 root239 (by decide +kernel)

theorem pair238Gap2 :
    RootTracking.OrderedPair (238/4) (row 238 4) (row 240 4) :=
  rise_pair (by decide) root238 root240 (by decide +kernel)

theorem pair238Gap3 :
    RootTracking.OrderedPair (238/4) (row 238 4) (row 241 4) :=
  rise_pair (by decide) root238 root241 (by decide +kernel)

theorem pair238Gap4 :
    RootTracking.OrderedPair (238/4) (row 238 4) (row 242 4) :=
  rise_pair (by decide) root238 root242 (by decide +kernel)

theorem pair239Gap1 :
    RootTracking.OrderedPair (239/4) (row 239 4) (row 240 4) :=
  rise_pair (by decide) root239 root240 (by decide +kernel)

theorem pair239Gap2 :
    RootTracking.OrderedPair (239/4) (row 239 4) (row 241 4) :=
  rise_pair (by decide) root239 root241 (by decide +kernel)

theorem pair239Gap3 :
    RootTracking.OrderedPair (239/4) (row 239 4) (row 242 4) :=
  rise_pair (by decide) root239 root242 (by decide +kernel)

theorem pair239Gap4 :
    RootTracking.OrderedPair (239/4) (row 239 4) (row 243 4) :=
  rise_pair (by decide) root239 root243 (by decide +kernel)

theorem range232Gap1 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair232Gap1
  · exact pair233Gap1
  · exact pair234Gap1
  · exact pair235Gap1
  · exact pair236Gap1
  · exact pair237Gap1
  · exact pair238Gap1
  · exact pair239Gap1

theorem range232Gap2 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair232Gap2
  · exact pair233Gap2
  · exact pair234Gap2
  · exact pair235Gap2
  · exact pair236Gap2
  · exact pair237Gap2
  · exact pair238Gap2
  · exact pair239Gap2

theorem range232Gap3 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair232Gap3
  · exact pair233Gap3
  · exact pair234Gap3
  · exact pair235Gap3
  · exact pair236Gap3
  · exact pair237Gap3
  · exact pair238Gap3
  · exact pair239Gap3

theorem range232Gap4 (n : ℕ) (lo : 232 ≤ n) (hi : n ≤ 239) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair232Gap4
  · exact pair233Gap4
  · exact pair234Gap4
  · exact pair235Gap4
  · exact pair236Gap4
  · exact pair237Gap4
  · exact pair238Gap4
  · exact pair239Gap4


#print axioms range232Gap1
#print axioms range232Gap2
#print axioms range232Gap3
#print axioms range232Gap4

end OrderedPartitions.FourPoleFinite
