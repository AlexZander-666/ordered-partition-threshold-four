import OrderedPartitions.FourPoleFiniteData.Roots112
import OrderedPartitions.FourPoleFiniteData.Roots120

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair112Gap1 :
    RootTracking.OrderedPair (112/4) (row 112 4) (row 113 4) :=
  stay_pair (by decide) root112 root113 (by decide +kernel)

theorem pair112Gap2 :
    RootTracking.OrderedPair (112/4) (row 112 4) (row 114 4) :=
  stay_pair (by decide) root112 root114 (by decide +kernel)

theorem pair112Gap3 :
    RootTracking.OrderedPair (112/4) (row 112 4) (row 115 4) :=
  stay_pair (by decide) root112 root115 (by decide +kernel)

theorem pair112Gap4 :
    RootTracking.OrderedPair (112/4) (row 112 4) (row 116 4) :=
  rise_pair (by decide) root112 root116 (by decide +kernel)

theorem pair113Gap1 :
    RootTracking.OrderedPair (113/4) (row 113 4) (row 114 4) :=
  stay_pair (by decide) root113 root114 (by decide +kernel)

theorem pair113Gap2 :
    RootTracking.OrderedPair (113/4) (row 113 4) (row 115 4) :=
  stay_pair (by decide) root113 root115 (by decide +kernel)

theorem pair113Gap3 :
    RootTracking.OrderedPair (113/4) (row 113 4) (row 116 4) :=
  rise_pair (by decide) root113 root116 (by decide +kernel)

theorem pair113Gap4 :
    RootTracking.OrderedPair (113/4) (row 113 4) (row 117 4) :=
  rise_pair (by decide) root113 root117 (by decide +kernel)

theorem pair114Gap1 :
    RootTracking.OrderedPair (114/4) (row 114 4) (row 115 4) :=
  stay_pair (by decide) root114 root115 (by decide +kernel)

theorem pair114Gap2 :
    RootTracking.OrderedPair (114/4) (row 114 4) (row 116 4) :=
  rise_pair (by decide) root114 root116 (by decide +kernel)

theorem pair114Gap3 :
    RootTracking.OrderedPair (114/4) (row 114 4) (row 117 4) :=
  rise_pair (by decide) root114 root117 (by decide +kernel)

theorem pair114Gap4 :
    RootTracking.OrderedPair (114/4) (row 114 4) (row 118 4) :=
  rise_pair (by decide) root114 root118 (by decide +kernel)

theorem pair115Gap1 :
    RootTracking.OrderedPair (115/4) (row 115 4) (row 116 4) :=
  rise_pair (by decide) root115 root116 (by decide +kernel)

theorem pair115Gap2 :
    RootTracking.OrderedPair (115/4) (row 115 4) (row 117 4) :=
  rise_pair (by decide) root115 root117 (by decide +kernel)

theorem pair115Gap3 :
    RootTracking.OrderedPair (115/4) (row 115 4) (row 118 4) :=
  rise_pair (by decide) root115 root118 (by decide +kernel)

theorem pair115Gap4 :
    RootTracking.OrderedPair (115/4) (row 115 4) (row 119 4) :=
  rise_pair (by decide) root115 root119 (by decide +kernel)

theorem pair116Gap1 :
    RootTracking.OrderedPair (116/4) (row 116 4) (row 117 4) :=
  stay_pair (by decide) root116 root117 (by decide +kernel)

theorem pair116Gap2 :
    RootTracking.OrderedPair (116/4) (row 116 4) (row 118 4) :=
  stay_pair (by decide) root116 root118 (by decide +kernel)

theorem pair116Gap3 :
    RootTracking.OrderedPair (116/4) (row 116 4) (row 119 4) :=
  stay_pair (by decide) root116 root119 (by decide +kernel)

theorem pair116Gap4 :
    RootTracking.OrderedPair (116/4) (row 116 4) (row 120 4) :=
  rise_pair (by decide) root116 root120 (by decide +kernel)

theorem pair117Gap1 :
    RootTracking.OrderedPair (117/4) (row 117 4) (row 118 4) :=
  stay_pair (by decide) root117 root118 (by decide +kernel)

theorem pair117Gap2 :
    RootTracking.OrderedPair (117/4) (row 117 4) (row 119 4) :=
  stay_pair (by decide) root117 root119 (by decide +kernel)

theorem pair117Gap3 :
    RootTracking.OrderedPair (117/4) (row 117 4) (row 120 4) :=
  rise_pair (by decide) root117 root120 (by decide +kernel)

theorem pair117Gap4 :
    RootTracking.OrderedPair (117/4) (row 117 4) (row 121 4) :=
  rise_pair (by decide) root117 root121 (by decide +kernel)

theorem pair118Gap1 :
    RootTracking.OrderedPair (118/4) (row 118 4) (row 119 4) :=
  stay_pair (by decide) root118 root119 (by decide +kernel)

theorem pair118Gap2 :
    RootTracking.OrderedPair (118/4) (row 118 4) (row 120 4) :=
  rise_pair (by decide) root118 root120 (by decide +kernel)

theorem pair118Gap3 :
    RootTracking.OrderedPair (118/4) (row 118 4) (row 121 4) :=
  rise_pair (by decide) root118 root121 (by decide +kernel)

theorem pair118Gap4 :
    RootTracking.OrderedPair (118/4) (row 118 4) (row 122 4) :=
  rise_pair (by decide) root118 root122 (by decide +kernel)

theorem pair119Gap1 :
    RootTracking.OrderedPair (119/4) (row 119 4) (row 120 4) :=
  rise_pair (by decide) root119 root120 (by decide +kernel)

theorem pair119Gap2 :
    RootTracking.OrderedPair (119/4) (row 119 4) (row 121 4) :=
  rise_pair (by decide) root119 root121 (by decide +kernel)

theorem pair119Gap3 :
    RootTracking.OrderedPair (119/4) (row 119 4) (row 122 4) :=
  rise_pair (by decide) root119 root122 (by decide +kernel)

theorem pair119Gap4 :
    RootTracking.OrderedPair (119/4) (row 119 4) (row 123 4) :=
  rise_pair (by decide) root119 root123 (by decide +kernel)

theorem range112Gap1 (n : ℕ) (lo : 112 ≤ n) (hi : n ≤ 119) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair112Gap1
  · exact pair113Gap1
  · exact pair114Gap1
  · exact pair115Gap1
  · exact pair116Gap1
  · exact pair117Gap1
  · exact pair118Gap1
  · exact pair119Gap1

theorem range112Gap2 (n : ℕ) (lo : 112 ≤ n) (hi : n ≤ 119) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair112Gap2
  · exact pair113Gap2
  · exact pair114Gap2
  · exact pair115Gap2
  · exact pair116Gap2
  · exact pair117Gap2
  · exact pair118Gap2
  · exact pair119Gap2

theorem range112Gap3 (n : ℕ) (lo : 112 ≤ n) (hi : n ≤ 119) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair112Gap3
  · exact pair113Gap3
  · exact pair114Gap3
  · exact pair115Gap3
  · exact pair116Gap3
  · exact pair117Gap3
  · exact pair118Gap3
  · exact pair119Gap3

theorem range112Gap4 (n : ℕ) (lo : 112 ≤ n) (hi : n ≤ 119) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair112Gap4
  · exact pair113Gap4
  · exact pair114Gap4
  · exact pair115Gap4
  · exact pair116Gap4
  · exact pair117Gap4
  · exact pair118Gap4
  · exact pair119Gap4


#print axioms range112Gap1
#print axioms range112Gap2
#print axioms range112Gap3
#print axioms range112Gap4

end OrderedPartitions.FourPoleFinite
