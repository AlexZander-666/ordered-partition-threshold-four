import OrderedPartitions.FourPoleFiniteData.Roots064
import OrderedPartitions.FourPoleFiniteData.Roots072

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair64Gap1 :
    RootTracking.OrderedPair (64/4) (row 64 4) (row 65 4) :=
  stay_pair (by decide) root64 root65 (by decide +kernel)

theorem pair64Gap2 :
    RootTracking.OrderedPair (64/4) (row 64 4) (row 66 4) :=
  stay_pair (by decide) root64 root66 (by decide +kernel)

theorem pair64Gap3 :
    RootTracking.OrderedPair (64/4) (row 64 4) (row 67 4) :=
  stay_pair (by decide) root64 root67 (by decide +kernel)

theorem pair64Gap4 :
    RootTracking.OrderedPair (64/4) (row 64 4) (row 68 4) :=
  rise_pair (by decide) root64 root68 (by decide +kernel)

theorem pair65Gap1 :
    RootTracking.OrderedPair (65/4) (row 65 4) (row 66 4) :=
  stay_pair (by decide) root65 root66 (by decide +kernel)

theorem pair65Gap2 :
    RootTracking.OrderedPair (65/4) (row 65 4) (row 67 4) :=
  stay_pair (by decide) root65 root67 (by decide +kernel)

theorem pair65Gap3 :
    RootTracking.OrderedPair (65/4) (row 65 4) (row 68 4) :=
  rise_pair (by decide) root65 root68 (by decide +kernel)

theorem pair65Gap4 :
    RootTracking.OrderedPair (65/4) (row 65 4) (row 69 4) :=
  rise_pair (by decide) root65 root69 (by decide +kernel)

theorem pair66Gap1 :
    RootTracking.OrderedPair (66/4) (row 66 4) (row 67 4) :=
  stay_pair (by decide) root66 root67 (by decide +kernel)

theorem pair66Gap2 :
    RootTracking.OrderedPair (66/4) (row 66 4) (row 68 4) :=
  rise_pair (by decide) root66 root68 (by decide +kernel)

theorem pair66Gap3 :
    RootTracking.OrderedPair (66/4) (row 66 4) (row 69 4) :=
  rise_pair (by decide) root66 root69 (by decide +kernel)

theorem pair66Gap4 :
    RootTracking.OrderedPair (66/4) (row 66 4) (row 70 4) :=
  rise_pair (by decide) root66 root70 (by decide +kernel)

theorem pair67Gap1 :
    RootTracking.OrderedPair (67/4) (row 67 4) (row 68 4) :=
  rise_pair (by decide) root67 root68 (by decide +kernel)

theorem pair67Gap2 :
    RootTracking.OrderedPair (67/4) (row 67 4) (row 69 4) :=
  rise_pair (by decide) root67 root69 (by decide +kernel)

theorem pair67Gap3 :
    RootTracking.OrderedPair (67/4) (row 67 4) (row 70 4) :=
  rise_pair (by decide) root67 root70 (by decide +kernel)

theorem pair67Gap4 :
    RootTracking.OrderedPair (67/4) (row 67 4) (row 71 4) :=
  rise_pair (by decide) root67 root71 (by decide +kernel)

theorem pair68Gap1 :
    RootTracking.OrderedPair (68/4) (row 68 4) (row 69 4) :=
  stay_pair (by decide) root68 root69 (by decide +kernel)

theorem pair68Gap2 :
    RootTracking.OrderedPair (68/4) (row 68 4) (row 70 4) :=
  stay_pair (by decide) root68 root70 (by decide +kernel)

theorem pair68Gap3 :
    RootTracking.OrderedPair (68/4) (row 68 4) (row 71 4) :=
  stay_pair (by decide) root68 root71 (by decide +kernel)

theorem pair68Gap4 :
    RootTracking.OrderedPair (68/4) (row 68 4) (row 72 4) :=
  rise_pair (by decide) root68 root72 (by decide +kernel)

theorem pair69Gap1 :
    RootTracking.OrderedPair (69/4) (row 69 4) (row 70 4) :=
  stay_pair (by decide) root69 root70 (by decide +kernel)

theorem pair69Gap2 :
    RootTracking.OrderedPair (69/4) (row 69 4) (row 71 4) :=
  stay_pair (by decide) root69 root71 (by decide +kernel)

theorem pair69Gap3 :
    RootTracking.OrderedPair (69/4) (row 69 4) (row 72 4) :=
  rise_pair (by decide) root69 root72 (by decide +kernel)

theorem pair69Gap4 :
    RootTracking.OrderedPair (69/4) (row 69 4) (row 73 4) :=
  rise_pair (by decide) root69 root73 (by decide +kernel)

theorem pair70Gap1 :
    RootTracking.OrderedPair (70/4) (row 70 4) (row 71 4) :=
  stay_pair (by decide) root70 root71 (by decide +kernel)

theorem pair70Gap2 :
    RootTracking.OrderedPair (70/4) (row 70 4) (row 72 4) :=
  rise_pair (by decide) root70 root72 (by decide +kernel)

theorem pair70Gap3 :
    RootTracking.OrderedPair (70/4) (row 70 4) (row 73 4) :=
  rise_pair (by decide) root70 root73 (by decide +kernel)

theorem pair70Gap4 :
    RootTracking.OrderedPair (70/4) (row 70 4) (row 74 4) :=
  rise_pair (by decide) root70 root74 (by decide +kernel)

theorem pair71Gap1 :
    RootTracking.OrderedPair (71/4) (row 71 4) (row 72 4) :=
  rise_pair (by decide) root71 root72 (by decide +kernel)

theorem pair71Gap2 :
    RootTracking.OrderedPair (71/4) (row 71 4) (row 73 4) :=
  rise_pair (by decide) root71 root73 (by decide +kernel)

theorem pair71Gap3 :
    RootTracking.OrderedPair (71/4) (row 71 4) (row 74 4) :=
  rise_pair (by decide) root71 root74 (by decide +kernel)

theorem pair71Gap4 :
    RootTracking.OrderedPair (71/4) (row 71 4) (row 75 4) :=
  rise_pair (by decide) root71 root75 (by decide +kernel)

theorem range64Gap1 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair64Gap1
  · exact pair65Gap1
  · exact pair66Gap1
  · exact pair67Gap1
  · exact pair68Gap1
  · exact pair69Gap1
  · exact pair70Gap1
  · exact pair71Gap1

theorem range64Gap2 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair64Gap2
  · exact pair65Gap2
  · exact pair66Gap2
  · exact pair67Gap2
  · exact pair68Gap2
  · exact pair69Gap2
  · exact pair70Gap2
  · exact pair71Gap2

theorem range64Gap3 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair64Gap3
  · exact pair65Gap3
  · exact pair66Gap3
  · exact pair67Gap3
  · exact pair68Gap3
  · exact pair69Gap3
  · exact pair70Gap3
  · exact pair71Gap3

theorem range64Gap4 (n : ℕ) (lo : 64 ≤ n) (hi : n ≤ 71) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair64Gap4
  · exact pair65Gap4
  · exact pair66Gap4
  · exact pair67Gap4
  · exact pair68Gap4
  · exact pair69Gap4
  · exact pair70Gap4
  · exact pair71Gap4


#print axioms range64Gap1
#print axioms range64Gap2
#print axioms range64Gap3
#print axioms range64Gap4

end OrderedPartitions.FourPoleFinite
