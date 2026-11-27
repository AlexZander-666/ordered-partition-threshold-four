import OrderedPartitions.FourPoleFiniteData.Roots136
import OrderedPartitions.FourPoleFiniteData.Roots144

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair136Gap1 :
    RootTracking.OrderedPair (136/4) (row 136 4) (row 137 4) :=
  stay_pair (by decide) root136 root137 (by decide +kernel)

theorem pair136Gap2 :
    RootTracking.OrderedPair (136/4) (row 136 4) (row 138 4) :=
  stay_pair (by decide) root136 root138 (by decide +kernel)

theorem pair136Gap3 :
    RootTracking.OrderedPair (136/4) (row 136 4) (row 139 4) :=
  stay_pair (by decide) root136 root139 (by decide +kernel)

theorem pair136Gap4 :
    RootTracking.OrderedPair (136/4) (row 136 4) (row 140 4) :=
  rise_pair (by decide) root136 root140 (by decide +kernel)

theorem pair137Gap1 :
    RootTracking.OrderedPair (137/4) (row 137 4) (row 138 4) :=
  stay_pair (by decide) root137 root138 (by decide +kernel)

theorem pair137Gap2 :
    RootTracking.OrderedPair (137/4) (row 137 4) (row 139 4) :=
  stay_pair (by decide) root137 root139 (by decide +kernel)

theorem pair137Gap3 :
    RootTracking.OrderedPair (137/4) (row 137 4) (row 140 4) :=
  rise_pair (by decide) root137 root140 (by decide +kernel)

theorem pair137Gap4 :
    RootTracking.OrderedPair (137/4) (row 137 4) (row 141 4) :=
  rise_pair (by decide) root137 root141 (by decide +kernel)

theorem pair138Gap1 :
    RootTracking.OrderedPair (138/4) (row 138 4) (row 139 4) :=
  stay_pair (by decide) root138 root139 (by decide +kernel)

theorem pair138Gap2 :
    RootTracking.OrderedPair (138/4) (row 138 4) (row 140 4) :=
  rise_pair (by decide) root138 root140 (by decide +kernel)

theorem pair138Gap3 :
    RootTracking.OrderedPair (138/4) (row 138 4) (row 141 4) :=
  rise_pair (by decide) root138 root141 (by decide +kernel)

theorem pair138Gap4 :
    RootTracking.OrderedPair (138/4) (row 138 4) (row 142 4) :=
  rise_pair (by decide) root138 root142 (by decide +kernel)

theorem pair139Gap1 :
    RootTracking.OrderedPair (139/4) (row 139 4) (row 140 4) :=
  rise_pair (by decide) root139 root140 (by decide +kernel)

theorem pair139Gap2 :
    RootTracking.OrderedPair (139/4) (row 139 4) (row 141 4) :=
  rise_pair (by decide) root139 root141 (by decide +kernel)

theorem pair139Gap3 :
    RootTracking.OrderedPair (139/4) (row 139 4) (row 142 4) :=
  rise_pair (by decide) root139 root142 (by decide +kernel)

theorem pair139Gap4 :
    RootTracking.OrderedPair (139/4) (row 139 4) (row 143 4) :=
  rise_pair (by decide) root139 root143 (by decide +kernel)

theorem pair140Gap1 :
    RootTracking.OrderedPair (140/4) (row 140 4) (row 141 4) :=
  stay_pair (by decide) root140 root141 (by decide +kernel)

theorem pair140Gap2 :
    RootTracking.OrderedPair (140/4) (row 140 4) (row 142 4) :=
  stay_pair (by decide) root140 root142 (by decide +kernel)

theorem pair140Gap3 :
    RootTracking.OrderedPair (140/4) (row 140 4) (row 143 4) :=
  stay_pair (by decide) root140 root143 (by decide +kernel)

theorem pair140Gap4 :
    RootTracking.OrderedPair (140/4) (row 140 4) (row 144 4) :=
  rise_pair (by decide) root140 root144 (by decide +kernel)

theorem pair141Gap1 :
    RootTracking.OrderedPair (141/4) (row 141 4) (row 142 4) :=
  stay_pair (by decide) root141 root142 (by decide +kernel)

theorem pair141Gap2 :
    RootTracking.OrderedPair (141/4) (row 141 4) (row 143 4) :=
  stay_pair (by decide) root141 root143 (by decide +kernel)

theorem pair141Gap3 :
    RootTracking.OrderedPair (141/4) (row 141 4) (row 144 4) :=
  rise_pair (by decide) root141 root144 (by decide +kernel)

theorem pair141Gap4 :
    RootTracking.OrderedPair (141/4) (row 141 4) (row 145 4) :=
  rise_pair (by decide) root141 root145 (by decide +kernel)

theorem pair142Gap1 :
    RootTracking.OrderedPair (142/4) (row 142 4) (row 143 4) :=
  stay_pair (by decide) root142 root143 (by decide +kernel)

theorem pair142Gap2 :
    RootTracking.OrderedPair (142/4) (row 142 4) (row 144 4) :=
  rise_pair (by decide) root142 root144 (by decide +kernel)

theorem pair142Gap3 :
    RootTracking.OrderedPair (142/4) (row 142 4) (row 145 4) :=
  rise_pair (by decide) root142 root145 (by decide +kernel)

theorem pair142Gap4 :
    RootTracking.OrderedPair (142/4) (row 142 4) (row 146 4) :=
  rise_pair (by decide) root142 root146 (by decide +kernel)

theorem pair143Gap1 :
    RootTracking.OrderedPair (143/4) (row 143 4) (row 144 4) :=
  rise_pair (by decide) root143 root144 (by decide +kernel)

theorem pair143Gap2 :
    RootTracking.OrderedPair (143/4) (row 143 4) (row 145 4) :=
  rise_pair (by decide) root143 root145 (by decide +kernel)

theorem pair143Gap3 :
    RootTracking.OrderedPair (143/4) (row 143 4) (row 146 4) :=
  rise_pair (by decide) root143 root146 (by decide +kernel)

theorem pair143Gap4 :
    RootTracking.OrderedPair (143/4) (row 143 4) (row 147 4) :=
  rise_pair (by decide) root143 root147 (by decide +kernel)

theorem range136Gap1 (n : ℕ) (lo : 136 ≤ n) (hi : n ≤ 143) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair136Gap1
  · exact pair137Gap1
  · exact pair138Gap1
  · exact pair139Gap1
  · exact pair140Gap1
  · exact pair141Gap1
  · exact pair142Gap1
  · exact pair143Gap1

theorem range136Gap2 (n : ℕ) (lo : 136 ≤ n) (hi : n ≤ 143) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair136Gap2
  · exact pair137Gap2
  · exact pair138Gap2
  · exact pair139Gap2
  · exact pair140Gap2
  · exact pair141Gap2
  · exact pair142Gap2
  · exact pair143Gap2

theorem range136Gap3 (n : ℕ) (lo : 136 ≤ n) (hi : n ≤ 143) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair136Gap3
  · exact pair137Gap3
  · exact pair138Gap3
  · exact pair139Gap3
  · exact pair140Gap3
  · exact pair141Gap3
  · exact pair142Gap3
  · exact pair143Gap3

theorem range136Gap4 (n : ℕ) (lo : 136 ≤ n) (hi : n ≤ 143) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair136Gap4
  · exact pair137Gap4
  · exact pair138Gap4
  · exact pair139Gap4
  · exact pair140Gap4
  · exact pair141Gap4
  · exact pair142Gap4
  · exact pair143Gap4


#print axioms range136Gap1
#print axioms range136Gap2
#print axioms range136Gap3
#print axioms range136Gap4

end OrderedPartitions.FourPoleFinite
