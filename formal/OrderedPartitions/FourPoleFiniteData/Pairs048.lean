import OrderedPartitions.FourPoleFiniteData.Roots048
import OrderedPartitions.FourPoleFiniteData.Roots056

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair48Gap1 :
    RootTracking.OrderedPair (48/4) (row 48 4) (row 49 4) :=
  stay_pair (by decide) root48 root49 (by decide +kernel)

theorem pair48Gap2 :
    RootTracking.OrderedPair (48/4) (row 48 4) (row 50 4) :=
  stay_pair (by decide) root48 root50 (by decide +kernel)

theorem pair48Gap3 :
    RootTracking.OrderedPair (48/4) (row 48 4) (row 51 4) :=
  stay_pair (by decide) root48 root51 (by decide +kernel)

theorem pair48Gap4 :
    RootTracking.OrderedPair (48/4) (row 48 4) (row 52 4) :=
  rise_pair (by decide) root48 root52 (by decide +kernel)

theorem pair49Gap1 :
    RootTracking.OrderedPair (49/4) (row 49 4) (row 50 4) :=
  stay_pair (by decide) root49 root50 (by decide +kernel)

theorem pair49Gap2 :
    RootTracking.OrderedPair (49/4) (row 49 4) (row 51 4) :=
  stay_pair (by decide) root49 root51 (by decide +kernel)

theorem pair49Gap3 :
    RootTracking.OrderedPair (49/4) (row 49 4) (row 52 4) :=
  rise_pair (by decide) root49 root52 (by decide +kernel)

theorem pair49Gap4 :
    RootTracking.OrderedPair (49/4) (row 49 4) (row 53 4) :=
  rise_pair (by decide) root49 root53 (by decide +kernel)

theorem pair50Gap1 :
    RootTracking.OrderedPair (50/4) (row 50 4) (row 51 4) :=
  stay_pair (by decide) root50 root51 (by decide +kernel)

theorem pair50Gap2 :
    RootTracking.OrderedPair (50/4) (row 50 4) (row 52 4) :=
  rise_pair (by decide) root50 root52 (by decide +kernel)

theorem pair50Gap3 :
    RootTracking.OrderedPair (50/4) (row 50 4) (row 53 4) :=
  rise_pair (by decide) root50 root53 (by decide +kernel)

theorem pair50Gap4 :
    RootTracking.OrderedPair (50/4) (row 50 4) (row 54 4) :=
  rise_pair (by decide) root50 root54 (by decide +kernel)

theorem pair51Gap1 :
    RootTracking.OrderedPair (51/4) (row 51 4) (row 52 4) :=
  rise_pair (by decide) root51 root52 (by decide +kernel)

theorem pair51Gap2 :
    RootTracking.OrderedPair (51/4) (row 51 4) (row 53 4) :=
  rise_pair (by decide) root51 root53 (by decide +kernel)

theorem pair51Gap3 :
    RootTracking.OrderedPair (51/4) (row 51 4) (row 54 4) :=
  rise_pair (by decide) root51 root54 (by decide +kernel)

theorem pair51Gap4 :
    RootTracking.OrderedPair (51/4) (row 51 4) (row 55 4) :=
  rise_pair (by decide) root51 root55 (by decide +kernel)

theorem pair52Gap1 :
    RootTracking.OrderedPair (52/4) (row 52 4) (row 53 4) :=
  stay_pair (by decide) root52 root53 (by decide +kernel)

theorem pair52Gap2 :
    RootTracking.OrderedPair (52/4) (row 52 4) (row 54 4) :=
  stay_pair (by decide) root52 root54 (by decide +kernel)

theorem pair52Gap3 :
    RootTracking.OrderedPair (52/4) (row 52 4) (row 55 4) :=
  stay_pair (by decide) root52 root55 (by decide +kernel)

theorem pair52Gap4 :
    RootTracking.OrderedPair (52/4) (row 52 4) (row 56 4) :=
  rise_pair (by decide) root52 root56 (by decide +kernel)

theorem pair53Gap1 :
    RootTracking.OrderedPair (53/4) (row 53 4) (row 54 4) :=
  stay_pair (by decide) root53 root54 (by decide +kernel)

theorem pair53Gap2 :
    RootTracking.OrderedPair (53/4) (row 53 4) (row 55 4) :=
  stay_pair (by decide) root53 root55 (by decide +kernel)

theorem pair53Gap3 :
    RootTracking.OrderedPair (53/4) (row 53 4) (row 56 4) :=
  rise_pair (by decide) root53 root56 (by decide +kernel)

theorem pair53Gap4 :
    RootTracking.OrderedPair (53/4) (row 53 4) (row 57 4) :=
  rise_pair (by decide) root53 root57 (by decide +kernel)

theorem pair54Gap1 :
    RootTracking.OrderedPair (54/4) (row 54 4) (row 55 4) :=
  stay_pair (by decide) root54 root55 (by decide +kernel)

theorem pair54Gap2 :
    RootTracking.OrderedPair (54/4) (row 54 4) (row 56 4) :=
  rise_pair (by decide) root54 root56 (by decide +kernel)

theorem pair54Gap3 :
    RootTracking.OrderedPair (54/4) (row 54 4) (row 57 4) :=
  rise_pair (by decide) root54 root57 (by decide +kernel)

theorem pair54Gap4 :
    RootTracking.OrderedPair (54/4) (row 54 4) (row 58 4) :=
  rise_pair (by decide) root54 root58 (by decide +kernel)

theorem pair55Gap1 :
    RootTracking.OrderedPair (55/4) (row 55 4) (row 56 4) :=
  rise_pair (by decide) root55 root56 (by decide +kernel)

theorem pair55Gap2 :
    RootTracking.OrderedPair (55/4) (row 55 4) (row 57 4) :=
  rise_pair (by decide) root55 root57 (by decide +kernel)

theorem pair55Gap3 :
    RootTracking.OrderedPair (55/4) (row 55 4) (row 58 4) :=
  rise_pair (by decide) root55 root58 (by decide +kernel)

theorem pair55Gap4 :
    RootTracking.OrderedPair (55/4) (row 55 4) (row 59 4) :=
  rise_pair (by decide) root55 root59 (by decide +kernel)

theorem range48Gap1 (n : ℕ) (lo : 48 ≤ n) (hi : n ≤ 55) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair48Gap1
  · exact pair49Gap1
  · exact pair50Gap1
  · exact pair51Gap1
  · exact pair52Gap1
  · exact pair53Gap1
  · exact pair54Gap1
  · exact pair55Gap1

theorem range48Gap2 (n : ℕ) (lo : 48 ≤ n) (hi : n ≤ 55) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair48Gap2
  · exact pair49Gap2
  · exact pair50Gap2
  · exact pair51Gap2
  · exact pair52Gap2
  · exact pair53Gap2
  · exact pair54Gap2
  · exact pair55Gap2

theorem range48Gap3 (n : ℕ) (lo : 48 ≤ n) (hi : n ≤ 55) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair48Gap3
  · exact pair49Gap3
  · exact pair50Gap3
  · exact pair51Gap3
  · exact pair52Gap3
  · exact pair53Gap3
  · exact pair54Gap3
  · exact pair55Gap3

theorem range48Gap4 (n : ℕ) (lo : 48 ≤ n) (hi : n ≤ 55) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair48Gap4
  · exact pair49Gap4
  · exact pair50Gap4
  · exact pair51Gap4
  · exact pair52Gap4
  · exact pair53Gap4
  · exact pair54Gap4
  · exact pair55Gap4


#print axioms range48Gap1
#print axioms range48Gap2
#print axioms range48Gap3
#print axioms range48Gap4

end OrderedPartitions.FourPoleFinite
