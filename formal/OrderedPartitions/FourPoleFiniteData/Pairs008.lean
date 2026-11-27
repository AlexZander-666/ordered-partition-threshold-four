import OrderedPartitions.FourPoleFiniteData.Roots008
import OrderedPartitions.FourPoleFiniteData.Roots016

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair8Gap1 :
    RootTracking.OrderedPair (8/4) (row 8 4) (row 9 4) :=
  stay_pair (by decide) root8 root9 (by decide +kernel)

theorem pair8Gap2 :
    RootTracking.OrderedPair (8/4) (row 8 4) (row 10 4) :=
  stay_pair (by decide) root8 root10 (by decide +kernel)

theorem pair8Gap3 :
    RootTracking.OrderedPair (8/4) (row 8 4) (row 11 4) :=
  stay_pair (by decide) root8 root11 (by decide +kernel)

theorem pair8Gap4 :
    RootTracking.OrderedPair (8/4) (row 8 4) (row 12 4) :=
  rise_pair (by decide) root8 root12 (by decide +kernel)

theorem pair9Gap1 :
    RootTracking.OrderedPair (9/4) (row 9 4) (row 10 4) :=
  stay_pair (by decide) root9 root10 (by decide +kernel)

theorem pair9Gap2 :
    RootTracking.OrderedPair (9/4) (row 9 4) (row 11 4) :=
  stay_pair (by decide) root9 root11 (by decide +kernel)

theorem pair9Gap3 :
    RootTracking.OrderedPair (9/4) (row 9 4) (row 12 4) :=
  rise_pair (by decide) root9 root12 (by decide +kernel)

theorem pair9Gap4 :
    RootTracking.OrderedPair (9/4) (row 9 4) (row 13 4) :=
  rise_pair (by decide) root9 root13 (by decide +kernel)

theorem pair10Gap1 :
    RootTracking.OrderedPair (10/4) (row 10 4) (row 11 4) :=
  stay_pair (by decide) root10 root11 (by decide +kernel)

theorem pair10Gap2 :
    RootTracking.OrderedPair (10/4) (row 10 4) (row 12 4) :=
  rise_pair (by decide) root10 root12 (by decide +kernel)

theorem pair10Gap3 :
    RootTracking.OrderedPair (10/4) (row 10 4) (row 13 4) :=
  rise_pair (by decide) root10 root13 (by decide +kernel)

theorem pair10Gap4 :
    RootTracking.OrderedPair (10/4) (row 10 4) (row 14 4) :=
  rise_pair (by decide) root10 root14 (by decide +kernel)

theorem pair11Gap1 :
    RootTracking.OrderedPair (11/4) (row 11 4) (row 12 4) :=
  rise_pair (by decide) root11 root12 (by decide +kernel)

theorem pair11Gap2 :
    RootTracking.OrderedPair (11/4) (row 11 4) (row 13 4) :=
  rise_pair (by decide) root11 root13 (by decide +kernel)

theorem pair11Gap3 :
    RootTracking.OrderedPair (11/4) (row 11 4) (row 14 4) :=
  rise_pair (by decide) root11 root14 (by decide +kernel)

theorem pair11Gap4 :
    RootTracking.OrderedPair (11/4) (row 11 4) (row 15 4) :=
  rise_pair (by decide) root11 root15 (by decide +kernel)

theorem pair12Gap1 :
    RootTracking.OrderedPair (12/4) (row 12 4) (row 13 4) :=
  stay_pair (by decide) root12 root13 (by decide +kernel)

theorem pair12Gap2 :
    RootTracking.OrderedPair (12/4) (row 12 4) (row 14 4) :=
  stay_pair (by decide) root12 root14 (by decide +kernel)

theorem pair12Gap3 :
    RootTracking.OrderedPair (12/4) (row 12 4) (row 15 4) :=
  stay_pair (by decide) root12 root15 (by decide +kernel)

theorem pair12Gap4 :
    RootTracking.OrderedPair (12/4) (row 12 4) (row 16 4) :=
  rise_pair (by decide) root12 root16 (by decide +kernel)

theorem pair13Gap1 :
    RootTracking.OrderedPair (13/4) (row 13 4) (row 14 4) :=
  stay_pair (by decide) root13 root14 (by decide +kernel)

theorem pair13Gap2 :
    RootTracking.OrderedPair (13/4) (row 13 4) (row 15 4) :=
  stay_pair (by decide) root13 root15 (by decide +kernel)

theorem pair13Gap3 :
    RootTracking.OrderedPair (13/4) (row 13 4) (row 16 4) :=
  rise_pair (by decide) root13 root16 (by decide +kernel)

theorem pair13Gap4 :
    RootTracking.OrderedPair (13/4) (row 13 4) (row 17 4) :=
  rise_pair (by decide) root13 root17 (by decide +kernel)

theorem pair14Gap1 :
    RootTracking.OrderedPair (14/4) (row 14 4) (row 15 4) :=
  stay_pair (by decide) root14 root15 (by decide +kernel)

theorem pair14Gap2 :
    RootTracking.OrderedPair (14/4) (row 14 4) (row 16 4) :=
  rise_pair (by decide) root14 root16 (by decide +kernel)

theorem pair14Gap3 :
    RootTracking.OrderedPair (14/4) (row 14 4) (row 17 4) :=
  rise_pair (by decide) root14 root17 (by decide +kernel)

theorem pair14Gap4 :
    RootTracking.OrderedPair (14/4) (row 14 4) (row 18 4) :=
  rise_pair (by decide) root14 root18 (by decide +kernel)

theorem pair15Gap1 :
    RootTracking.OrderedPair (15/4) (row 15 4) (row 16 4) :=
  rise_pair (by decide) root15 root16 (by decide +kernel)

theorem pair15Gap2 :
    RootTracking.OrderedPair (15/4) (row 15 4) (row 17 4) :=
  rise_pair (by decide) root15 root17 (by decide +kernel)

theorem pair15Gap3 :
    RootTracking.OrderedPair (15/4) (row 15 4) (row 18 4) :=
  rise_pair (by decide) root15 root18 (by decide +kernel)

theorem pair15Gap4 :
    RootTracking.OrderedPair (15/4) (row 15 4) (row 19 4) :=
  rise_pair (by decide) root15 root19 (by decide +kernel)

theorem range8Gap1 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair8Gap1
  · exact pair9Gap1
  · exact pair10Gap1
  · exact pair11Gap1
  · exact pair12Gap1
  · exact pair13Gap1
  · exact pair14Gap1
  · exact pair15Gap1

theorem range8Gap2 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair8Gap2
  · exact pair9Gap2
  · exact pair10Gap2
  · exact pair11Gap2
  · exact pair12Gap2
  · exact pair13Gap2
  · exact pair14Gap2
  · exact pair15Gap2

theorem range8Gap3 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair8Gap3
  · exact pair9Gap3
  · exact pair10Gap3
  · exact pair11Gap3
  · exact pair12Gap3
  · exact pair13Gap3
  · exact pair14Gap3
  · exact pair15Gap3

theorem range8Gap4 (n : ℕ) (lo : 8 ≤ n) (hi : n ≤ 15) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair8Gap4
  · exact pair9Gap4
  · exact pair10Gap4
  · exact pair11Gap4
  · exact pair12Gap4
  · exact pair13Gap4
  · exact pair14Gap4
  · exact pair15Gap4


#print axioms range8Gap1
#print axioms range8Gap2
#print axioms range8Gap3
#print axioms range8Gap4

end OrderedPartitions.FourPoleFinite
