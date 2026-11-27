import OrderedPartitions.FourPoleFiniteData.Roots000
import OrderedPartitions.FourPoleFiniteData.Roots008

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair0Gap1 :
    RootTracking.OrderedPair (0/4) (row 0 4) (row 1 4) :=
  stay_pair (by decide) root0 root1 (by decide +kernel)

theorem pair0Gap2 :
    RootTracking.OrderedPair (0/4) (row 0 4) (row 2 4) :=
  stay_pair (by decide) root0 root2 (by decide +kernel)

theorem pair0Gap3 :
    RootTracking.OrderedPair (0/4) (row 0 4) (row 3 4) :=
  stay_pair (by decide) root0 root3 (by decide +kernel)

theorem pair0Gap4 :
    RootTracking.OrderedPair (0/4) (row 0 4) (row 4 4) :=
  rise_pair (by decide) root0 root4 (by decide +kernel)

theorem pair1Gap1 :
    RootTracking.OrderedPair (1/4) (row 1 4) (row 2 4) :=
  stay_pair (by decide) root1 root2 (by decide +kernel)

theorem pair1Gap2 :
    RootTracking.OrderedPair (1/4) (row 1 4) (row 3 4) :=
  stay_pair (by decide) root1 root3 (by decide +kernel)

theorem pair1Gap3 :
    RootTracking.OrderedPair (1/4) (row 1 4) (row 4 4) :=
  rise_pair (by decide) root1 root4 (by decide +kernel)

theorem pair1Gap4 :
    RootTracking.OrderedPair (1/4) (row 1 4) (row 5 4) :=
  rise_pair (by decide) root1 root5 (by decide +kernel)

theorem pair2Gap1 :
    RootTracking.OrderedPair (2/4) (row 2 4) (row 3 4) :=
  stay_pair (by decide) root2 root3 (by decide +kernel)

theorem pair2Gap2 :
    RootTracking.OrderedPair (2/4) (row 2 4) (row 4 4) :=
  rise_pair (by decide) root2 root4 (by decide +kernel)

theorem pair2Gap3 :
    RootTracking.OrderedPair (2/4) (row 2 4) (row 5 4) :=
  rise_pair (by decide) root2 root5 (by decide +kernel)

theorem pair2Gap4 :
    RootTracking.OrderedPair (2/4) (row 2 4) (row 6 4) :=
  rise_pair (by decide) root2 root6 (by decide +kernel)

theorem pair3Gap1 :
    RootTracking.OrderedPair (3/4) (row 3 4) (row 4 4) :=
  rise_pair (by decide) root3 root4 (by decide +kernel)

theorem pair3Gap2 :
    RootTracking.OrderedPair (3/4) (row 3 4) (row 5 4) :=
  rise_pair (by decide) root3 root5 (by decide +kernel)

theorem pair3Gap3 :
    RootTracking.OrderedPair (3/4) (row 3 4) (row 6 4) :=
  rise_pair (by decide) root3 root6 (by decide +kernel)

theorem pair3Gap4 :
    RootTracking.OrderedPair (3/4) (row 3 4) (row 7 4) :=
  rise_pair (by decide) root3 root7 (by decide +kernel)

theorem pair4Gap1 :
    RootTracking.OrderedPair (4/4) (row 4 4) (row 5 4) :=
  stay_pair (by decide) root4 root5 (by decide +kernel)

theorem pair4Gap2 :
    RootTracking.OrderedPair (4/4) (row 4 4) (row 6 4) :=
  stay_pair (by decide) root4 root6 (by decide +kernel)

theorem pair4Gap3 :
    RootTracking.OrderedPair (4/4) (row 4 4) (row 7 4) :=
  stay_pair (by decide) root4 root7 (by decide +kernel)

theorem pair4Gap4 :
    RootTracking.OrderedPair (4/4) (row 4 4) (row 8 4) :=
  rise_pair (by decide) root4 root8 (by decide +kernel)

theorem pair5Gap1 :
    RootTracking.OrderedPair (5/4) (row 5 4) (row 6 4) :=
  stay_pair (by decide) root5 root6 (by decide +kernel)

theorem pair5Gap2 :
    RootTracking.OrderedPair (5/4) (row 5 4) (row 7 4) :=
  stay_pair (by decide) root5 root7 (by decide +kernel)

theorem pair5Gap3 :
    RootTracking.OrderedPair (5/4) (row 5 4) (row 8 4) :=
  rise_pair (by decide) root5 root8 (by decide +kernel)

theorem pair5Gap4 :
    RootTracking.OrderedPair (5/4) (row 5 4) (row 9 4) :=
  rise_pair (by decide) root5 root9 (by decide +kernel)

theorem pair6Gap1 :
    RootTracking.OrderedPair (6/4) (row 6 4) (row 7 4) :=
  stay_pair (by decide) root6 root7 (by decide +kernel)

theorem pair6Gap2 :
    RootTracking.OrderedPair (6/4) (row 6 4) (row 8 4) :=
  rise_pair (by decide) root6 root8 (by decide +kernel)

theorem pair6Gap3 :
    RootTracking.OrderedPair (6/4) (row 6 4) (row 9 4) :=
  rise_pair (by decide) root6 root9 (by decide +kernel)

theorem pair6Gap4 :
    RootTracking.OrderedPair (6/4) (row 6 4) (row 10 4) :=
  rise_pair (by decide) root6 root10 (by decide +kernel)

theorem pair7Gap1 :
    RootTracking.OrderedPair (7/4) (row 7 4) (row 8 4) :=
  rise_pair (by decide) root7 root8 (by decide +kernel)

theorem pair7Gap2 :
    RootTracking.OrderedPair (7/4) (row 7 4) (row 9 4) :=
  rise_pair (by decide) root7 root9 (by decide +kernel)

theorem pair7Gap3 :
    RootTracking.OrderedPair (7/4) (row 7 4) (row 10 4) :=
  rise_pair (by decide) root7 root10 (by decide +kernel)

theorem pair7Gap4 :
    RootTracking.OrderedPair (7/4) (row 7 4) (row 11 4) :=
  rise_pair (by decide) root7 root11 (by decide +kernel)

theorem range0Gap1 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair0Gap1
  · exact pair1Gap1
  · exact pair2Gap1
  · exact pair3Gap1
  · exact pair4Gap1
  · exact pair5Gap1
  · exact pair6Gap1
  · exact pair7Gap1

theorem range0Gap2 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair0Gap2
  · exact pair1Gap2
  · exact pair2Gap2
  · exact pair3Gap2
  · exact pair4Gap2
  · exact pair5Gap2
  · exact pair6Gap2
  · exact pair7Gap2

theorem range0Gap3 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair0Gap3
  · exact pair1Gap3
  · exact pair2Gap3
  · exact pair3Gap3
  · exact pair4Gap3
  · exact pair5Gap3
  · exact pair6Gap3
  · exact pair7Gap3

theorem range0Gap4 (n : ℕ) (lo : 0 ≤ n) (hi : n ≤ 7) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair0Gap4
  · exact pair1Gap4
  · exact pair2Gap4
  · exact pair3Gap4
  · exact pair4Gap4
  · exact pair5Gap4
  · exact pair6Gap4
  · exact pair7Gap4


#print axioms range0Gap1
#print axioms range0Gap2
#print axioms range0Gap3
#print axioms range0Gap4

end OrderedPartitions.FourPoleFinite
