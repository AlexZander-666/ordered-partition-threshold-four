import OrderedPartitions.FourPoleFiniteData.Roots280
import OrderedPartitions.FourPoleFiniteData.Roots288

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair280Gap1 :
    RootTracking.OrderedPair (280/4) (row 280 4) (row 281 4) :=
  stay_pair (by decide) root280 root281 (by decide +kernel)

theorem pair280Gap2 :
    RootTracking.OrderedPair (280/4) (row 280 4) (row 282 4) :=
  stay_pair (by decide) root280 root282 (by decide +kernel)

theorem pair280Gap3 :
    RootTracking.OrderedPair (280/4) (row 280 4) (row 283 4) :=
  stay_pair (by decide) root280 root283 (by decide +kernel)

theorem pair280Gap4 :
    RootTracking.OrderedPair (280/4) (row 280 4) (row 284 4) :=
  rise_pair (by decide) root280 root284 (by decide +kernel)

theorem pair281Gap1 :
    RootTracking.OrderedPair (281/4) (row 281 4) (row 282 4) :=
  stay_pair (by decide) root281 root282 (by decide +kernel)

theorem pair281Gap2 :
    RootTracking.OrderedPair (281/4) (row 281 4) (row 283 4) :=
  stay_pair (by decide) root281 root283 (by decide +kernel)

theorem pair281Gap3 :
    RootTracking.OrderedPair (281/4) (row 281 4) (row 284 4) :=
  rise_pair (by decide) root281 root284 (by decide +kernel)

theorem pair281Gap4 :
    RootTracking.OrderedPair (281/4) (row 281 4) (row 285 4) :=
  rise_pair (by decide) root281 root285 (by decide +kernel)

theorem pair282Gap1 :
    RootTracking.OrderedPair (282/4) (row 282 4) (row 283 4) :=
  stay_pair (by decide) root282 root283 (by decide +kernel)

theorem pair282Gap2 :
    RootTracking.OrderedPair (282/4) (row 282 4) (row 284 4) :=
  rise_pair (by decide) root282 root284 (by decide +kernel)

theorem pair282Gap3 :
    RootTracking.OrderedPair (282/4) (row 282 4) (row 285 4) :=
  rise_pair (by decide) root282 root285 (by decide +kernel)

theorem pair282Gap4 :
    RootTracking.OrderedPair (282/4) (row 282 4) (row 286 4) :=
  rise_pair (by decide) root282 root286 (by decide +kernel)

theorem pair283Gap1 :
    RootTracking.OrderedPair (283/4) (row 283 4) (row 284 4) :=
  rise_pair (by decide) root283 root284 (by decide +kernel)

theorem pair283Gap2 :
    RootTracking.OrderedPair (283/4) (row 283 4) (row 285 4) :=
  rise_pair (by decide) root283 root285 (by decide +kernel)

theorem pair283Gap3 :
    RootTracking.OrderedPair (283/4) (row 283 4) (row 286 4) :=
  rise_pair (by decide) root283 root286 (by decide +kernel)

theorem pair283Gap4 :
    RootTracking.OrderedPair (283/4) (row 283 4) (row 287 4) :=
  rise_pair (by decide) root283 root287 (by decide +kernel)

theorem pair284Gap1 :
    RootTracking.OrderedPair (284/4) (row 284 4) (row 285 4) :=
  stay_pair (by decide) root284 root285 (by decide +kernel)

theorem pair284Gap2 :
    RootTracking.OrderedPair (284/4) (row 284 4) (row 286 4) :=
  stay_pair (by decide) root284 root286 (by decide +kernel)

theorem pair284Gap3 :
    RootTracking.OrderedPair (284/4) (row 284 4) (row 287 4) :=
  stay_pair (by decide) root284 root287 (by decide +kernel)

theorem pair284Gap4 :
    RootTracking.OrderedPair (284/4) (row 284 4) (row 288 4) :=
  rise_pair (by decide) root284 root288 (by decide +kernel)

theorem pair285Gap1 :
    RootTracking.OrderedPair (285/4) (row 285 4) (row 286 4) :=
  stay_pair (by decide) root285 root286 (by decide +kernel)

theorem pair285Gap2 :
    RootTracking.OrderedPair (285/4) (row 285 4) (row 287 4) :=
  stay_pair (by decide) root285 root287 (by decide +kernel)

theorem pair285Gap3 :
    RootTracking.OrderedPair (285/4) (row 285 4) (row 288 4) :=
  rise_pair (by decide) root285 root288 (by decide +kernel)

theorem pair285Gap4 :
    RootTracking.OrderedPair (285/4) (row 285 4) (row 289 4) :=
  rise_pair (by decide) root285 root289 (by decide +kernel)

theorem pair286Gap1 :
    RootTracking.OrderedPair (286/4) (row 286 4) (row 287 4) :=
  stay_pair (by decide) root286 root287 (by decide +kernel)

theorem pair286Gap2 :
    RootTracking.OrderedPair (286/4) (row 286 4) (row 288 4) :=
  rise_pair (by decide) root286 root288 (by decide +kernel)

theorem pair286Gap3 :
    RootTracking.OrderedPair (286/4) (row 286 4) (row 289 4) :=
  rise_pair (by decide) root286 root289 (by decide +kernel)

theorem pair286Gap4 :
    RootTracking.OrderedPair (286/4) (row 286 4) (row 290 4) :=
  rise_pair (by decide) root286 root290 (by decide +kernel)

theorem pair287Gap1 :
    RootTracking.OrderedPair (287/4) (row 287 4) (row 288 4) :=
  rise_pair (by decide) root287 root288 (by decide +kernel)

theorem pair287Gap2 :
    RootTracking.OrderedPair (287/4) (row 287 4) (row 289 4) :=
  rise_pair (by decide) root287 root289 (by decide +kernel)

theorem pair287Gap3 :
    RootTracking.OrderedPair (287/4) (row 287 4) (row 290 4) :=
  rise_pair (by decide) root287 root290 (by decide +kernel)

theorem pair287Gap4 :
    RootTracking.OrderedPair (287/4) (row 287 4) (row 291 4) :=
  rise_pair (by decide) root287 root291 (by decide +kernel)

theorem range280Gap1 (n : ℕ) (lo : 280 ≤ n) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair280Gap1
  · exact pair281Gap1
  · exact pair282Gap1
  · exact pair283Gap1
  · exact pair284Gap1
  · exact pair285Gap1
  · exact pair286Gap1
  · exact pair287Gap1

theorem range280Gap2 (n : ℕ) (lo : 280 ≤ n) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair280Gap2
  · exact pair281Gap2
  · exact pair282Gap2
  · exact pair283Gap2
  · exact pair284Gap2
  · exact pair285Gap2
  · exact pair286Gap2
  · exact pair287Gap2

theorem range280Gap3 (n : ℕ) (lo : 280 ≤ n) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair280Gap3
  · exact pair281Gap3
  · exact pair282Gap3
  · exact pair283Gap3
  · exact pair284Gap3
  · exact pair285Gap3
  · exact pair286Gap3
  · exact pair287Gap3

theorem range280Gap4 (n : ℕ) (lo : 280 ≤ n) (hi : n ≤ 287) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair280Gap4
  · exact pair281Gap4
  · exact pair282Gap4
  · exact pair283Gap4
  · exact pair284Gap4
  · exact pair285Gap4
  · exact pair286Gap4
  · exact pair287Gap4


#print axioms range280Gap1
#print axioms range280Gap2
#print axioms range280Gap3
#print axioms range280Gap4

end OrderedPartitions.FourPoleFinite
