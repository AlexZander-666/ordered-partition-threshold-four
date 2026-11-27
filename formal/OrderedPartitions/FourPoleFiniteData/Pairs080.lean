import OrderedPartitions.FourPoleFiniteData.Roots080
import OrderedPartitions.FourPoleFiniteData.Roots088

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair80Gap1 :
    RootTracking.OrderedPair (80/4) (row 80 4) (row 81 4) :=
  stay_pair (by decide) root80 root81 (by decide +kernel)

theorem pair80Gap2 :
    RootTracking.OrderedPair (80/4) (row 80 4) (row 82 4) :=
  stay_pair (by decide) root80 root82 (by decide +kernel)

theorem pair80Gap3 :
    RootTracking.OrderedPair (80/4) (row 80 4) (row 83 4) :=
  stay_pair (by decide) root80 root83 (by decide +kernel)

theorem pair80Gap4 :
    RootTracking.OrderedPair (80/4) (row 80 4) (row 84 4) :=
  rise_pair (by decide) root80 root84 (by decide +kernel)

theorem pair81Gap1 :
    RootTracking.OrderedPair (81/4) (row 81 4) (row 82 4) :=
  stay_pair (by decide) root81 root82 (by decide +kernel)

theorem pair81Gap2 :
    RootTracking.OrderedPair (81/4) (row 81 4) (row 83 4) :=
  stay_pair (by decide) root81 root83 (by decide +kernel)

theorem pair81Gap3 :
    RootTracking.OrderedPair (81/4) (row 81 4) (row 84 4) :=
  rise_pair (by decide) root81 root84 (by decide +kernel)

theorem pair81Gap4 :
    RootTracking.OrderedPair (81/4) (row 81 4) (row 85 4) :=
  rise_pair (by decide) root81 root85 (by decide +kernel)

theorem pair82Gap1 :
    RootTracking.OrderedPair (82/4) (row 82 4) (row 83 4) :=
  stay_pair (by decide) root82 root83 (by decide +kernel)

theorem pair82Gap2 :
    RootTracking.OrderedPair (82/4) (row 82 4) (row 84 4) :=
  rise_pair (by decide) root82 root84 (by decide +kernel)

theorem pair82Gap3 :
    RootTracking.OrderedPair (82/4) (row 82 4) (row 85 4) :=
  rise_pair (by decide) root82 root85 (by decide +kernel)

theorem pair82Gap4 :
    RootTracking.OrderedPair (82/4) (row 82 4) (row 86 4) :=
  rise_pair (by decide) root82 root86 (by decide +kernel)

theorem pair83Gap1 :
    RootTracking.OrderedPair (83/4) (row 83 4) (row 84 4) :=
  rise_pair (by decide) root83 root84 (by decide +kernel)

theorem pair83Gap2 :
    RootTracking.OrderedPair (83/4) (row 83 4) (row 85 4) :=
  rise_pair (by decide) root83 root85 (by decide +kernel)

theorem pair83Gap3 :
    RootTracking.OrderedPair (83/4) (row 83 4) (row 86 4) :=
  rise_pair (by decide) root83 root86 (by decide +kernel)

theorem pair83Gap4 :
    RootTracking.OrderedPair (83/4) (row 83 4) (row 87 4) :=
  rise_pair (by decide) root83 root87 (by decide +kernel)

theorem pair84Gap1 :
    RootTracking.OrderedPair (84/4) (row 84 4) (row 85 4) :=
  stay_pair (by decide) root84 root85 (by decide +kernel)

theorem pair84Gap2 :
    RootTracking.OrderedPair (84/4) (row 84 4) (row 86 4) :=
  stay_pair (by decide) root84 root86 (by decide +kernel)

theorem pair84Gap3 :
    RootTracking.OrderedPair (84/4) (row 84 4) (row 87 4) :=
  stay_pair (by decide) root84 root87 (by decide +kernel)

theorem pair84Gap4 :
    RootTracking.OrderedPair (84/4) (row 84 4) (row 88 4) :=
  rise_pair (by decide) root84 root88 (by decide +kernel)

theorem pair85Gap1 :
    RootTracking.OrderedPair (85/4) (row 85 4) (row 86 4) :=
  stay_pair (by decide) root85 root86 (by decide +kernel)

theorem pair85Gap2 :
    RootTracking.OrderedPair (85/4) (row 85 4) (row 87 4) :=
  stay_pair (by decide) root85 root87 (by decide +kernel)

theorem pair85Gap3 :
    RootTracking.OrderedPair (85/4) (row 85 4) (row 88 4) :=
  rise_pair (by decide) root85 root88 (by decide +kernel)

theorem pair85Gap4 :
    RootTracking.OrderedPair (85/4) (row 85 4) (row 89 4) :=
  rise_pair (by decide) root85 root89 (by decide +kernel)

theorem pair86Gap1 :
    RootTracking.OrderedPair (86/4) (row 86 4) (row 87 4) :=
  stay_pair (by decide) root86 root87 (by decide +kernel)

theorem pair86Gap2 :
    RootTracking.OrderedPair (86/4) (row 86 4) (row 88 4) :=
  rise_pair (by decide) root86 root88 (by decide +kernel)

theorem pair86Gap3 :
    RootTracking.OrderedPair (86/4) (row 86 4) (row 89 4) :=
  rise_pair (by decide) root86 root89 (by decide +kernel)

theorem pair86Gap4 :
    RootTracking.OrderedPair (86/4) (row 86 4) (row 90 4) :=
  rise_pair (by decide) root86 root90 (by decide +kernel)

theorem pair87Gap1 :
    RootTracking.OrderedPair (87/4) (row 87 4) (row 88 4) :=
  rise_pair (by decide) root87 root88 (by decide +kernel)

theorem pair87Gap2 :
    RootTracking.OrderedPair (87/4) (row 87 4) (row 89 4) :=
  rise_pair (by decide) root87 root89 (by decide +kernel)

theorem pair87Gap3 :
    RootTracking.OrderedPair (87/4) (row 87 4) (row 90 4) :=
  rise_pair (by decide) root87 root90 (by decide +kernel)

theorem pair87Gap4 :
    RootTracking.OrderedPair (87/4) (row 87 4) (row 91 4) :=
  rise_pair (by decide) root87 root91 (by decide +kernel)

theorem range80Gap1 (n : ℕ) (lo : 80 ≤ n) (hi : n ≤ 87) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair80Gap1
  · exact pair81Gap1
  · exact pair82Gap1
  · exact pair83Gap1
  · exact pair84Gap1
  · exact pair85Gap1
  · exact pair86Gap1
  · exact pair87Gap1

theorem range80Gap2 (n : ℕ) (lo : 80 ≤ n) (hi : n ≤ 87) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair80Gap2
  · exact pair81Gap2
  · exact pair82Gap2
  · exact pair83Gap2
  · exact pair84Gap2
  · exact pair85Gap2
  · exact pair86Gap2
  · exact pair87Gap2

theorem range80Gap3 (n : ℕ) (lo : 80 ≤ n) (hi : n ≤ 87) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair80Gap3
  · exact pair81Gap3
  · exact pair82Gap3
  · exact pair83Gap3
  · exact pair84Gap3
  · exact pair85Gap3
  · exact pair86Gap3
  · exact pair87Gap3

theorem range80Gap4 (n : ℕ) (lo : 80 ≤ n) (hi : n ≤ 87) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair80Gap4
  · exact pair81Gap4
  · exact pair82Gap4
  · exact pair83Gap4
  · exact pair84Gap4
  · exact pair85Gap4
  · exact pair86Gap4
  · exact pair87Gap4


#print axioms range80Gap1
#print axioms range80Gap2
#print axioms range80Gap3
#print axioms range80Gap4

end OrderedPartitions.FourPoleFinite
