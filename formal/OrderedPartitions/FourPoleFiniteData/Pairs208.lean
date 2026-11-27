import OrderedPartitions.FourPoleFiniteData.Roots208
import OrderedPartitions.FourPoleFiniteData.Roots216

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair208Gap1 :
    RootTracking.OrderedPair (208/4) (row 208 4) (row 209 4) :=
  stay_pair (by decide) root208 root209 (by decide +kernel)

theorem pair208Gap2 :
    RootTracking.OrderedPair (208/4) (row 208 4) (row 210 4) :=
  stay_pair (by decide) root208 root210 (by decide +kernel)

theorem pair208Gap3 :
    RootTracking.OrderedPair (208/4) (row 208 4) (row 211 4) :=
  stay_pair (by decide) root208 root211 (by decide +kernel)

theorem pair208Gap4 :
    RootTracking.OrderedPair (208/4) (row 208 4) (row 212 4) :=
  rise_pair (by decide) root208 root212 (by decide +kernel)

theorem pair209Gap1 :
    RootTracking.OrderedPair (209/4) (row 209 4) (row 210 4) :=
  stay_pair (by decide) root209 root210 (by decide +kernel)

theorem pair209Gap2 :
    RootTracking.OrderedPair (209/4) (row 209 4) (row 211 4) :=
  stay_pair (by decide) root209 root211 (by decide +kernel)

theorem pair209Gap3 :
    RootTracking.OrderedPair (209/4) (row 209 4) (row 212 4) :=
  rise_pair (by decide) root209 root212 (by decide +kernel)

theorem pair209Gap4 :
    RootTracking.OrderedPair (209/4) (row 209 4) (row 213 4) :=
  rise_pair (by decide) root209 root213 (by decide +kernel)

theorem pair210Gap1 :
    RootTracking.OrderedPair (210/4) (row 210 4) (row 211 4) :=
  stay_pair (by decide) root210 root211 (by decide +kernel)

theorem pair210Gap2 :
    RootTracking.OrderedPair (210/4) (row 210 4) (row 212 4) :=
  rise_pair (by decide) root210 root212 (by decide +kernel)

theorem pair210Gap3 :
    RootTracking.OrderedPair (210/4) (row 210 4) (row 213 4) :=
  rise_pair (by decide) root210 root213 (by decide +kernel)

theorem pair210Gap4 :
    RootTracking.OrderedPair (210/4) (row 210 4) (row 214 4) :=
  rise_pair (by decide) root210 root214 (by decide +kernel)

theorem pair211Gap1 :
    RootTracking.OrderedPair (211/4) (row 211 4) (row 212 4) :=
  rise_pair (by decide) root211 root212 (by decide +kernel)

theorem pair211Gap2 :
    RootTracking.OrderedPair (211/4) (row 211 4) (row 213 4) :=
  rise_pair (by decide) root211 root213 (by decide +kernel)

theorem pair211Gap3 :
    RootTracking.OrderedPair (211/4) (row 211 4) (row 214 4) :=
  rise_pair (by decide) root211 root214 (by decide +kernel)

theorem pair211Gap4 :
    RootTracking.OrderedPair (211/4) (row 211 4) (row 215 4) :=
  rise_pair (by decide) root211 root215 (by decide +kernel)

theorem pair212Gap1 :
    RootTracking.OrderedPair (212/4) (row 212 4) (row 213 4) :=
  stay_pair (by decide) root212 root213 (by decide +kernel)

theorem pair212Gap2 :
    RootTracking.OrderedPair (212/4) (row 212 4) (row 214 4) :=
  stay_pair (by decide) root212 root214 (by decide +kernel)

theorem pair212Gap3 :
    RootTracking.OrderedPair (212/4) (row 212 4) (row 215 4) :=
  stay_pair (by decide) root212 root215 (by decide +kernel)

theorem pair212Gap4 :
    RootTracking.OrderedPair (212/4) (row 212 4) (row 216 4) :=
  rise_pair (by decide) root212 root216 (by decide +kernel)

theorem pair213Gap1 :
    RootTracking.OrderedPair (213/4) (row 213 4) (row 214 4) :=
  stay_pair (by decide) root213 root214 (by decide +kernel)

theorem pair213Gap2 :
    RootTracking.OrderedPair (213/4) (row 213 4) (row 215 4) :=
  stay_pair (by decide) root213 root215 (by decide +kernel)

theorem pair213Gap3 :
    RootTracking.OrderedPair (213/4) (row 213 4) (row 216 4) :=
  rise_pair (by decide) root213 root216 (by decide +kernel)

theorem pair213Gap4 :
    RootTracking.OrderedPair (213/4) (row 213 4) (row 217 4) :=
  rise_pair (by decide) root213 root217 (by decide +kernel)

theorem pair214Gap1 :
    RootTracking.OrderedPair (214/4) (row 214 4) (row 215 4) :=
  stay_pair (by decide) root214 root215 (by decide +kernel)

theorem pair214Gap2 :
    RootTracking.OrderedPair (214/4) (row 214 4) (row 216 4) :=
  rise_pair (by decide) root214 root216 (by decide +kernel)

theorem pair214Gap3 :
    RootTracking.OrderedPair (214/4) (row 214 4) (row 217 4) :=
  rise_pair (by decide) root214 root217 (by decide +kernel)

theorem pair214Gap4 :
    RootTracking.OrderedPair (214/4) (row 214 4) (row 218 4) :=
  rise_pair (by decide) root214 root218 (by decide +kernel)

theorem pair215Gap1 :
    RootTracking.OrderedPair (215/4) (row 215 4) (row 216 4) :=
  rise_pair (by decide) root215 root216 (by decide +kernel)

theorem pair215Gap2 :
    RootTracking.OrderedPair (215/4) (row 215 4) (row 217 4) :=
  rise_pair (by decide) root215 root217 (by decide +kernel)

theorem pair215Gap3 :
    RootTracking.OrderedPair (215/4) (row 215 4) (row 218 4) :=
  rise_pair (by decide) root215 root218 (by decide +kernel)

theorem pair215Gap4 :
    RootTracking.OrderedPair (215/4) (row 215 4) (row 219 4) :=
  rise_pair (by decide) root215 root219 (by decide +kernel)

theorem range208Gap1 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair208Gap1
  · exact pair209Gap1
  · exact pair210Gap1
  · exact pair211Gap1
  · exact pair212Gap1
  · exact pair213Gap1
  · exact pair214Gap1
  · exact pair215Gap1

theorem range208Gap2 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair208Gap2
  · exact pair209Gap2
  · exact pair210Gap2
  · exact pair211Gap2
  · exact pair212Gap2
  · exact pair213Gap2
  · exact pair214Gap2
  · exact pair215Gap2

theorem range208Gap3 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair208Gap3
  · exact pair209Gap3
  · exact pair210Gap3
  · exact pair211Gap3
  · exact pair212Gap3
  · exact pair213Gap3
  · exact pair214Gap3
  · exact pair215Gap3

theorem range208Gap4 (n : ℕ) (lo : 208 ≤ n) (hi : n ≤ 215) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair208Gap4
  · exact pair209Gap4
  · exact pair210Gap4
  · exact pair211Gap4
  · exact pair212Gap4
  · exact pair213Gap4
  · exact pair214Gap4
  · exact pair215Gap4


#print axioms range208Gap1
#print axioms range208Gap2
#print axioms range208Gap3
#print axioms range208Gap4

end OrderedPartitions.FourPoleFinite
