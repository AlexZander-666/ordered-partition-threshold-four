import OrderedPartitions.FourPoleFiniteData.Roots200
import OrderedPartitions.FourPoleFiniteData.Roots208

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair200Gap1 :
    RootTracking.OrderedPair (200/4) (row 200 4) (row 201 4) :=
  stay_pair (by decide) root200 root201 (by decide +kernel)

theorem pair200Gap2 :
    RootTracking.OrderedPair (200/4) (row 200 4) (row 202 4) :=
  stay_pair (by decide) root200 root202 (by decide +kernel)

theorem pair200Gap3 :
    RootTracking.OrderedPair (200/4) (row 200 4) (row 203 4) :=
  stay_pair (by decide) root200 root203 (by decide +kernel)

theorem pair200Gap4 :
    RootTracking.OrderedPair (200/4) (row 200 4) (row 204 4) :=
  rise_pair (by decide) root200 root204 (by decide +kernel)

theorem pair201Gap1 :
    RootTracking.OrderedPair (201/4) (row 201 4) (row 202 4) :=
  stay_pair (by decide) root201 root202 (by decide +kernel)

theorem pair201Gap2 :
    RootTracking.OrderedPair (201/4) (row 201 4) (row 203 4) :=
  stay_pair (by decide) root201 root203 (by decide +kernel)

theorem pair201Gap3 :
    RootTracking.OrderedPair (201/4) (row 201 4) (row 204 4) :=
  rise_pair (by decide) root201 root204 (by decide +kernel)

theorem pair201Gap4 :
    RootTracking.OrderedPair (201/4) (row 201 4) (row 205 4) :=
  rise_pair (by decide) root201 root205 (by decide +kernel)

theorem pair202Gap1 :
    RootTracking.OrderedPair (202/4) (row 202 4) (row 203 4) :=
  stay_pair (by decide) root202 root203 (by decide +kernel)

theorem pair202Gap2 :
    RootTracking.OrderedPair (202/4) (row 202 4) (row 204 4) :=
  rise_pair (by decide) root202 root204 (by decide +kernel)

theorem pair202Gap3 :
    RootTracking.OrderedPair (202/4) (row 202 4) (row 205 4) :=
  rise_pair (by decide) root202 root205 (by decide +kernel)

theorem pair202Gap4 :
    RootTracking.OrderedPair (202/4) (row 202 4) (row 206 4) :=
  rise_pair (by decide) root202 root206 (by decide +kernel)

theorem pair203Gap1 :
    RootTracking.OrderedPair (203/4) (row 203 4) (row 204 4) :=
  rise_pair (by decide) root203 root204 (by decide +kernel)

theorem pair203Gap2 :
    RootTracking.OrderedPair (203/4) (row 203 4) (row 205 4) :=
  rise_pair (by decide) root203 root205 (by decide +kernel)

theorem pair203Gap3 :
    RootTracking.OrderedPair (203/4) (row 203 4) (row 206 4) :=
  rise_pair (by decide) root203 root206 (by decide +kernel)

theorem pair203Gap4 :
    RootTracking.OrderedPair (203/4) (row 203 4) (row 207 4) :=
  rise_pair (by decide) root203 root207 (by decide +kernel)

theorem pair204Gap1 :
    RootTracking.OrderedPair (204/4) (row 204 4) (row 205 4) :=
  stay_pair (by decide) root204 root205 (by decide +kernel)

theorem pair204Gap2 :
    RootTracking.OrderedPair (204/4) (row 204 4) (row 206 4) :=
  stay_pair (by decide) root204 root206 (by decide +kernel)

theorem pair204Gap3 :
    RootTracking.OrderedPair (204/4) (row 204 4) (row 207 4) :=
  stay_pair (by decide) root204 root207 (by decide +kernel)

theorem pair204Gap4 :
    RootTracking.OrderedPair (204/4) (row 204 4) (row 208 4) :=
  rise_pair (by decide) root204 root208 (by decide +kernel)

theorem pair205Gap1 :
    RootTracking.OrderedPair (205/4) (row 205 4) (row 206 4) :=
  stay_pair (by decide) root205 root206 (by decide +kernel)

theorem pair205Gap2 :
    RootTracking.OrderedPair (205/4) (row 205 4) (row 207 4) :=
  stay_pair (by decide) root205 root207 (by decide +kernel)

theorem pair205Gap3 :
    RootTracking.OrderedPair (205/4) (row 205 4) (row 208 4) :=
  rise_pair (by decide) root205 root208 (by decide +kernel)

theorem pair205Gap4 :
    RootTracking.OrderedPair (205/4) (row 205 4) (row 209 4) :=
  rise_pair (by decide) root205 root209 (by decide +kernel)

theorem pair206Gap1 :
    RootTracking.OrderedPair (206/4) (row 206 4) (row 207 4) :=
  stay_pair (by decide) root206 root207 (by decide +kernel)

theorem pair206Gap2 :
    RootTracking.OrderedPair (206/4) (row 206 4) (row 208 4) :=
  rise_pair (by decide) root206 root208 (by decide +kernel)

theorem pair206Gap3 :
    RootTracking.OrderedPair (206/4) (row 206 4) (row 209 4) :=
  rise_pair (by decide) root206 root209 (by decide +kernel)

theorem pair206Gap4 :
    RootTracking.OrderedPair (206/4) (row 206 4) (row 210 4) :=
  rise_pair (by decide) root206 root210 (by decide +kernel)

theorem pair207Gap1 :
    RootTracking.OrderedPair (207/4) (row 207 4) (row 208 4) :=
  rise_pair (by decide) root207 root208 (by decide +kernel)

theorem pair207Gap2 :
    RootTracking.OrderedPair (207/4) (row 207 4) (row 209 4) :=
  rise_pair (by decide) root207 root209 (by decide +kernel)

theorem pair207Gap3 :
    RootTracking.OrderedPair (207/4) (row 207 4) (row 210 4) :=
  rise_pair (by decide) root207 root210 (by decide +kernel)

theorem pair207Gap4 :
    RootTracking.OrderedPair (207/4) (row 207 4) (row 211 4) :=
  rise_pair (by decide) root207 root211 (by decide +kernel)

theorem range200Gap1 (n : ℕ) (lo : 200 ≤ n) (hi : n ≤ 207) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair200Gap1
  · exact pair201Gap1
  · exact pair202Gap1
  · exact pair203Gap1
  · exact pair204Gap1
  · exact pair205Gap1
  · exact pair206Gap1
  · exact pair207Gap1

theorem range200Gap2 (n : ℕ) (lo : 200 ≤ n) (hi : n ≤ 207) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair200Gap2
  · exact pair201Gap2
  · exact pair202Gap2
  · exact pair203Gap2
  · exact pair204Gap2
  · exact pair205Gap2
  · exact pair206Gap2
  · exact pair207Gap2

theorem range200Gap3 (n : ℕ) (lo : 200 ≤ n) (hi : n ≤ 207) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair200Gap3
  · exact pair201Gap3
  · exact pair202Gap3
  · exact pair203Gap3
  · exact pair204Gap3
  · exact pair205Gap3
  · exact pair206Gap3
  · exact pair207Gap3

theorem range200Gap4 (n : ℕ) (lo : 200 ≤ n) (hi : n ≤ 207) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair200Gap4
  · exact pair201Gap4
  · exact pair202Gap4
  · exact pair203Gap4
  · exact pair204Gap4
  · exact pair205Gap4
  · exact pair206Gap4
  · exact pair207Gap4


#print axioms range200Gap1
#print axioms range200Gap2
#print axioms range200Gap3
#print axioms range200Gap4

end OrderedPartitions.FourPoleFinite
