import OrderedPartitions.FourPoleFiniteData.Roots040
import OrderedPartitions.FourPoleFiniteData.Roots048

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair40Gap1 :
    RootTracking.OrderedPair (40/4) (row 40 4) (row 41 4) :=
  stay_pair (by decide) root40 root41 (by decide +kernel)

theorem pair40Gap2 :
    RootTracking.OrderedPair (40/4) (row 40 4) (row 42 4) :=
  stay_pair (by decide) root40 root42 (by decide +kernel)

theorem pair40Gap3 :
    RootTracking.OrderedPair (40/4) (row 40 4) (row 43 4) :=
  stay_pair (by decide) root40 root43 (by decide +kernel)

theorem pair40Gap4 :
    RootTracking.OrderedPair (40/4) (row 40 4) (row 44 4) :=
  rise_pair (by decide) root40 root44 (by decide +kernel)

theorem pair41Gap1 :
    RootTracking.OrderedPair (41/4) (row 41 4) (row 42 4) :=
  stay_pair (by decide) root41 root42 (by decide +kernel)

theorem pair41Gap2 :
    RootTracking.OrderedPair (41/4) (row 41 4) (row 43 4) :=
  stay_pair (by decide) root41 root43 (by decide +kernel)

theorem pair41Gap3 :
    RootTracking.OrderedPair (41/4) (row 41 4) (row 44 4) :=
  rise_pair (by decide) root41 root44 (by decide +kernel)

theorem pair41Gap4 :
    RootTracking.OrderedPair (41/4) (row 41 4) (row 45 4) :=
  rise_pair (by decide) root41 root45 (by decide +kernel)

theorem pair42Gap1 :
    RootTracking.OrderedPair (42/4) (row 42 4) (row 43 4) :=
  stay_pair (by decide) root42 root43 (by decide +kernel)

theorem pair42Gap2 :
    RootTracking.OrderedPair (42/4) (row 42 4) (row 44 4) :=
  rise_pair (by decide) root42 root44 (by decide +kernel)

theorem pair42Gap3 :
    RootTracking.OrderedPair (42/4) (row 42 4) (row 45 4) :=
  rise_pair (by decide) root42 root45 (by decide +kernel)

theorem pair42Gap4 :
    RootTracking.OrderedPair (42/4) (row 42 4) (row 46 4) :=
  rise_pair (by decide) root42 root46 (by decide +kernel)

theorem pair43Gap1 :
    RootTracking.OrderedPair (43/4) (row 43 4) (row 44 4) :=
  rise_pair (by decide) root43 root44 (by decide +kernel)

theorem pair43Gap2 :
    RootTracking.OrderedPair (43/4) (row 43 4) (row 45 4) :=
  rise_pair (by decide) root43 root45 (by decide +kernel)

theorem pair43Gap3 :
    RootTracking.OrderedPair (43/4) (row 43 4) (row 46 4) :=
  rise_pair (by decide) root43 root46 (by decide +kernel)

theorem pair43Gap4 :
    RootTracking.OrderedPair (43/4) (row 43 4) (row 47 4) :=
  rise_pair (by decide) root43 root47 (by decide +kernel)

theorem pair44Gap1 :
    RootTracking.OrderedPair (44/4) (row 44 4) (row 45 4) :=
  stay_pair (by decide) root44 root45 (by decide +kernel)

theorem pair44Gap2 :
    RootTracking.OrderedPair (44/4) (row 44 4) (row 46 4) :=
  stay_pair (by decide) root44 root46 (by decide +kernel)

theorem pair44Gap3 :
    RootTracking.OrderedPair (44/4) (row 44 4) (row 47 4) :=
  stay_pair (by decide) root44 root47 (by decide +kernel)

theorem pair44Gap4 :
    RootTracking.OrderedPair (44/4) (row 44 4) (row 48 4) :=
  rise_pair (by decide) root44 root48 (by decide +kernel)

theorem pair45Gap1 :
    RootTracking.OrderedPair (45/4) (row 45 4) (row 46 4) :=
  stay_pair (by decide) root45 root46 (by decide +kernel)

theorem pair45Gap2 :
    RootTracking.OrderedPair (45/4) (row 45 4) (row 47 4) :=
  stay_pair (by decide) root45 root47 (by decide +kernel)

theorem pair45Gap3 :
    RootTracking.OrderedPair (45/4) (row 45 4) (row 48 4) :=
  rise_pair (by decide) root45 root48 (by decide +kernel)

theorem pair45Gap4 :
    RootTracking.OrderedPair (45/4) (row 45 4) (row 49 4) :=
  rise_pair (by decide) root45 root49 (by decide +kernel)

theorem pair46Gap1 :
    RootTracking.OrderedPair (46/4) (row 46 4) (row 47 4) :=
  stay_pair (by decide) root46 root47 (by decide +kernel)

theorem pair46Gap2 :
    RootTracking.OrderedPair (46/4) (row 46 4) (row 48 4) :=
  rise_pair (by decide) root46 root48 (by decide +kernel)

theorem pair46Gap3 :
    RootTracking.OrderedPair (46/4) (row 46 4) (row 49 4) :=
  rise_pair (by decide) root46 root49 (by decide +kernel)

theorem pair46Gap4 :
    RootTracking.OrderedPair (46/4) (row 46 4) (row 50 4) :=
  rise_pair (by decide) root46 root50 (by decide +kernel)

theorem pair47Gap1 :
    RootTracking.OrderedPair (47/4) (row 47 4) (row 48 4) :=
  rise_pair (by decide) root47 root48 (by decide +kernel)

theorem pair47Gap2 :
    RootTracking.OrderedPair (47/4) (row 47 4) (row 49 4) :=
  rise_pair (by decide) root47 root49 (by decide +kernel)

theorem pair47Gap3 :
    RootTracking.OrderedPair (47/4) (row 47 4) (row 50 4) :=
  rise_pair (by decide) root47 root50 (by decide +kernel)

theorem pair47Gap4 :
    RootTracking.OrderedPair (47/4) (row 47 4) (row 51 4) :=
  rise_pair (by decide) root47 root51 (by decide +kernel)

theorem range40Gap1 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair40Gap1
  · exact pair41Gap1
  · exact pair42Gap1
  · exact pair43Gap1
  · exact pair44Gap1
  · exact pair45Gap1
  · exact pair46Gap1
  · exact pair47Gap1

theorem range40Gap2 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair40Gap2
  · exact pair41Gap2
  · exact pair42Gap2
  · exact pair43Gap2
  · exact pair44Gap2
  · exact pair45Gap2
  · exact pair46Gap2
  · exact pair47Gap2

theorem range40Gap3 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair40Gap3
  · exact pair41Gap3
  · exact pair42Gap3
  · exact pair43Gap3
  · exact pair44Gap3
  · exact pair45Gap3
  · exact pair46Gap3
  · exact pair47Gap3

theorem range40Gap4 (n : ℕ) (lo : 40 ≤ n) (hi : n ≤ 47) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair40Gap4
  · exact pair41Gap4
  · exact pair42Gap4
  · exact pair43Gap4
  · exact pair44Gap4
  · exact pair45Gap4
  · exact pair46Gap4
  · exact pair47Gap4


#print axioms range40Gap1
#print axioms range40Gap2
#print axioms range40Gap3
#print axioms range40Gap4

end OrderedPartitions.FourPoleFinite
