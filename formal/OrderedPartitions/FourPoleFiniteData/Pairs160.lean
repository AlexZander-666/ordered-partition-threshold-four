import OrderedPartitions.FourPoleFiniteData.Roots160
import OrderedPartitions.FourPoleFiniteData.Roots168

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair160Gap1 :
    RootTracking.OrderedPair (160/4) (row 160 4) (row 161 4) :=
  stay_pair (by decide) root160 root161 (by decide +kernel)

theorem pair160Gap2 :
    RootTracking.OrderedPair (160/4) (row 160 4) (row 162 4) :=
  stay_pair (by decide) root160 root162 (by decide +kernel)

theorem pair160Gap3 :
    RootTracking.OrderedPair (160/4) (row 160 4) (row 163 4) :=
  stay_pair (by decide) root160 root163 (by decide +kernel)

theorem pair160Gap4 :
    RootTracking.OrderedPair (160/4) (row 160 4) (row 164 4) :=
  rise_pair (by decide) root160 root164 (by decide +kernel)

theorem pair161Gap1 :
    RootTracking.OrderedPair (161/4) (row 161 4) (row 162 4) :=
  stay_pair (by decide) root161 root162 (by decide +kernel)

theorem pair161Gap2 :
    RootTracking.OrderedPair (161/4) (row 161 4) (row 163 4) :=
  stay_pair (by decide) root161 root163 (by decide +kernel)

theorem pair161Gap3 :
    RootTracking.OrderedPair (161/4) (row 161 4) (row 164 4) :=
  rise_pair (by decide) root161 root164 (by decide +kernel)

theorem pair161Gap4 :
    RootTracking.OrderedPair (161/4) (row 161 4) (row 165 4) :=
  rise_pair (by decide) root161 root165 (by decide +kernel)

theorem pair162Gap1 :
    RootTracking.OrderedPair (162/4) (row 162 4) (row 163 4) :=
  stay_pair (by decide) root162 root163 (by decide +kernel)

theorem pair162Gap2 :
    RootTracking.OrderedPair (162/4) (row 162 4) (row 164 4) :=
  rise_pair (by decide) root162 root164 (by decide +kernel)

theorem pair162Gap3 :
    RootTracking.OrderedPair (162/4) (row 162 4) (row 165 4) :=
  rise_pair (by decide) root162 root165 (by decide +kernel)

theorem pair162Gap4 :
    RootTracking.OrderedPair (162/4) (row 162 4) (row 166 4) :=
  rise_pair (by decide) root162 root166 (by decide +kernel)

theorem pair163Gap1 :
    RootTracking.OrderedPair (163/4) (row 163 4) (row 164 4) :=
  rise_pair (by decide) root163 root164 (by decide +kernel)

theorem pair163Gap2 :
    RootTracking.OrderedPair (163/4) (row 163 4) (row 165 4) :=
  rise_pair (by decide) root163 root165 (by decide +kernel)

theorem pair163Gap3 :
    RootTracking.OrderedPair (163/4) (row 163 4) (row 166 4) :=
  rise_pair (by decide) root163 root166 (by decide +kernel)

theorem pair163Gap4 :
    RootTracking.OrderedPair (163/4) (row 163 4) (row 167 4) :=
  rise_pair (by decide) root163 root167 (by decide +kernel)

theorem pair164Gap1 :
    RootTracking.OrderedPair (164/4) (row 164 4) (row 165 4) :=
  stay_pair (by decide) root164 root165 (by decide +kernel)

theorem pair164Gap2 :
    RootTracking.OrderedPair (164/4) (row 164 4) (row 166 4) :=
  stay_pair (by decide) root164 root166 (by decide +kernel)

theorem pair164Gap3 :
    RootTracking.OrderedPair (164/4) (row 164 4) (row 167 4) :=
  stay_pair (by decide) root164 root167 (by decide +kernel)

theorem pair164Gap4 :
    RootTracking.OrderedPair (164/4) (row 164 4) (row 168 4) :=
  rise_pair (by decide) root164 root168 (by decide +kernel)

theorem pair165Gap1 :
    RootTracking.OrderedPair (165/4) (row 165 4) (row 166 4) :=
  stay_pair (by decide) root165 root166 (by decide +kernel)

theorem pair165Gap2 :
    RootTracking.OrderedPair (165/4) (row 165 4) (row 167 4) :=
  stay_pair (by decide) root165 root167 (by decide +kernel)

theorem pair165Gap3 :
    RootTracking.OrderedPair (165/4) (row 165 4) (row 168 4) :=
  rise_pair (by decide) root165 root168 (by decide +kernel)

theorem pair165Gap4 :
    RootTracking.OrderedPair (165/4) (row 165 4) (row 169 4) :=
  rise_pair (by decide) root165 root169 (by decide +kernel)

theorem pair166Gap1 :
    RootTracking.OrderedPair (166/4) (row 166 4) (row 167 4) :=
  stay_pair (by decide) root166 root167 (by decide +kernel)

theorem pair166Gap2 :
    RootTracking.OrderedPair (166/4) (row 166 4) (row 168 4) :=
  rise_pair (by decide) root166 root168 (by decide +kernel)

theorem pair166Gap3 :
    RootTracking.OrderedPair (166/4) (row 166 4) (row 169 4) :=
  rise_pair (by decide) root166 root169 (by decide +kernel)

theorem pair166Gap4 :
    RootTracking.OrderedPair (166/4) (row 166 4) (row 170 4) :=
  rise_pair (by decide) root166 root170 (by decide +kernel)

theorem pair167Gap1 :
    RootTracking.OrderedPair (167/4) (row 167 4) (row 168 4) :=
  rise_pair (by decide) root167 root168 (by decide +kernel)

theorem pair167Gap2 :
    RootTracking.OrderedPair (167/4) (row 167 4) (row 169 4) :=
  rise_pair (by decide) root167 root169 (by decide +kernel)

theorem pair167Gap3 :
    RootTracking.OrderedPair (167/4) (row 167 4) (row 170 4) :=
  rise_pair (by decide) root167 root170 (by decide +kernel)

theorem pair167Gap4 :
    RootTracking.OrderedPair (167/4) (row 167 4) (row 171 4) :=
  rise_pair (by decide) root167 root171 (by decide +kernel)

theorem range160Gap1 (n : ℕ) (lo : 160 ≤ n) (hi : n ≤ 167) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair160Gap1
  · exact pair161Gap1
  · exact pair162Gap1
  · exact pair163Gap1
  · exact pair164Gap1
  · exact pair165Gap1
  · exact pair166Gap1
  · exact pair167Gap1

theorem range160Gap2 (n : ℕ) (lo : 160 ≤ n) (hi : n ≤ 167) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair160Gap2
  · exact pair161Gap2
  · exact pair162Gap2
  · exact pair163Gap2
  · exact pair164Gap2
  · exact pair165Gap2
  · exact pair166Gap2
  · exact pair167Gap2

theorem range160Gap3 (n : ℕ) (lo : 160 ≤ n) (hi : n ≤ 167) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair160Gap3
  · exact pair161Gap3
  · exact pair162Gap3
  · exact pair163Gap3
  · exact pair164Gap3
  · exact pair165Gap3
  · exact pair166Gap3
  · exact pair167Gap3

theorem range160Gap4 (n : ℕ) (lo : 160 ≤ n) (hi : n ≤ 167) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair160Gap4
  · exact pair161Gap4
  · exact pair162Gap4
  · exact pair163Gap4
  · exact pair164Gap4
  · exact pair165Gap4
  · exact pair166Gap4
  · exact pair167Gap4


#print axioms range160Gap1
#print axioms range160Gap2
#print axioms range160Gap3
#print axioms range160Gap4

end OrderedPartitions.FourPoleFinite
