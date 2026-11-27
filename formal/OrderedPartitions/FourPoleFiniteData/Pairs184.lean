import OrderedPartitions.FourPoleFiniteData.Roots184
import OrderedPartitions.FourPoleFiniteData.Roots192

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair184Gap1 :
    RootTracking.OrderedPair (184/4) (row 184 4) (row 185 4) :=
  stay_pair (by decide) root184 root185 (by decide +kernel)

theorem pair184Gap2 :
    RootTracking.OrderedPair (184/4) (row 184 4) (row 186 4) :=
  stay_pair (by decide) root184 root186 (by decide +kernel)

theorem pair184Gap3 :
    RootTracking.OrderedPair (184/4) (row 184 4) (row 187 4) :=
  stay_pair (by decide) root184 root187 (by decide +kernel)

theorem pair184Gap4 :
    RootTracking.OrderedPair (184/4) (row 184 4) (row 188 4) :=
  rise_pair (by decide) root184 root188 (by decide +kernel)

theorem pair185Gap1 :
    RootTracking.OrderedPair (185/4) (row 185 4) (row 186 4) :=
  stay_pair (by decide) root185 root186 (by decide +kernel)

theorem pair185Gap2 :
    RootTracking.OrderedPair (185/4) (row 185 4) (row 187 4) :=
  stay_pair (by decide) root185 root187 (by decide +kernel)

theorem pair185Gap3 :
    RootTracking.OrderedPair (185/4) (row 185 4) (row 188 4) :=
  rise_pair (by decide) root185 root188 (by decide +kernel)

theorem pair185Gap4 :
    RootTracking.OrderedPair (185/4) (row 185 4) (row 189 4) :=
  rise_pair (by decide) root185 root189 (by decide +kernel)

theorem pair186Gap1 :
    RootTracking.OrderedPair (186/4) (row 186 4) (row 187 4) :=
  stay_pair (by decide) root186 root187 (by decide +kernel)

theorem pair186Gap2 :
    RootTracking.OrderedPair (186/4) (row 186 4) (row 188 4) :=
  rise_pair (by decide) root186 root188 (by decide +kernel)

theorem pair186Gap3 :
    RootTracking.OrderedPair (186/4) (row 186 4) (row 189 4) :=
  rise_pair (by decide) root186 root189 (by decide +kernel)

theorem pair186Gap4 :
    RootTracking.OrderedPair (186/4) (row 186 4) (row 190 4) :=
  rise_pair (by decide) root186 root190 (by decide +kernel)

theorem pair187Gap1 :
    RootTracking.OrderedPair (187/4) (row 187 4) (row 188 4) :=
  rise_pair (by decide) root187 root188 (by decide +kernel)

theorem pair187Gap2 :
    RootTracking.OrderedPair (187/4) (row 187 4) (row 189 4) :=
  rise_pair (by decide) root187 root189 (by decide +kernel)

theorem pair187Gap3 :
    RootTracking.OrderedPair (187/4) (row 187 4) (row 190 4) :=
  rise_pair (by decide) root187 root190 (by decide +kernel)

theorem pair187Gap4 :
    RootTracking.OrderedPair (187/4) (row 187 4) (row 191 4) :=
  rise_pair (by decide) root187 root191 (by decide +kernel)

theorem pair188Gap1 :
    RootTracking.OrderedPair (188/4) (row 188 4) (row 189 4) :=
  stay_pair (by decide) root188 root189 (by decide +kernel)

theorem pair188Gap2 :
    RootTracking.OrderedPair (188/4) (row 188 4) (row 190 4) :=
  stay_pair (by decide) root188 root190 (by decide +kernel)

theorem pair188Gap3 :
    RootTracking.OrderedPair (188/4) (row 188 4) (row 191 4) :=
  stay_pair (by decide) root188 root191 (by decide +kernel)

theorem pair188Gap4 :
    RootTracking.OrderedPair (188/4) (row 188 4) (row 192 4) :=
  rise_pair (by decide) root188 root192 (by decide +kernel)

theorem pair189Gap1 :
    RootTracking.OrderedPair (189/4) (row 189 4) (row 190 4) :=
  stay_pair (by decide) root189 root190 (by decide +kernel)

theorem pair189Gap2 :
    RootTracking.OrderedPair (189/4) (row 189 4) (row 191 4) :=
  stay_pair (by decide) root189 root191 (by decide +kernel)

theorem pair189Gap3 :
    RootTracking.OrderedPair (189/4) (row 189 4) (row 192 4) :=
  rise_pair (by decide) root189 root192 (by decide +kernel)

theorem pair189Gap4 :
    RootTracking.OrderedPair (189/4) (row 189 4) (row 193 4) :=
  rise_pair (by decide) root189 root193 (by decide +kernel)

theorem pair190Gap1 :
    RootTracking.OrderedPair (190/4) (row 190 4) (row 191 4) :=
  stay_pair (by decide) root190 root191 (by decide +kernel)

theorem pair190Gap2 :
    RootTracking.OrderedPair (190/4) (row 190 4) (row 192 4) :=
  rise_pair (by decide) root190 root192 (by decide +kernel)

theorem pair190Gap3 :
    RootTracking.OrderedPair (190/4) (row 190 4) (row 193 4) :=
  rise_pair (by decide) root190 root193 (by decide +kernel)

theorem pair190Gap4 :
    RootTracking.OrderedPair (190/4) (row 190 4) (row 194 4) :=
  rise_pair (by decide) root190 root194 (by decide +kernel)

theorem pair191Gap1 :
    RootTracking.OrderedPair (191/4) (row 191 4) (row 192 4) :=
  rise_pair (by decide) root191 root192 (by decide +kernel)

theorem pair191Gap2 :
    RootTracking.OrderedPair (191/4) (row 191 4) (row 193 4) :=
  rise_pair (by decide) root191 root193 (by decide +kernel)

theorem pair191Gap3 :
    RootTracking.OrderedPair (191/4) (row 191 4) (row 194 4) :=
  rise_pair (by decide) root191 root194 (by decide +kernel)

theorem pair191Gap4 :
    RootTracking.OrderedPair (191/4) (row 191 4) (row 195 4) :=
  rise_pair (by decide) root191 root195 (by decide +kernel)

theorem range184Gap1 (n : ℕ) (lo : 184 ≤ n) (hi : n ≤ 191) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair184Gap1
  · exact pair185Gap1
  · exact pair186Gap1
  · exact pair187Gap1
  · exact pair188Gap1
  · exact pair189Gap1
  · exact pair190Gap1
  · exact pair191Gap1

theorem range184Gap2 (n : ℕ) (lo : 184 ≤ n) (hi : n ≤ 191) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair184Gap2
  · exact pair185Gap2
  · exact pair186Gap2
  · exact pair187Gap2
  · exact pair188Gap2
  · exact pair189Gap2
  · exact pair190Gap2
  · exact pair191Gap2

theorem range184Gap3 (n : ℕ) (lo : 184 ≤ n) (hi : n ≤ 191) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair184Gap3
  · exact pair185Gap3
  · exact pair186Gap3
  · exact pair187Gap3
  · exact pair188Gap3
  · exact pair189Gap3
  · exact pair190Gap3
  · exact pair191Gap3

theorem range184Gap4 (n : ℕ) (lo : 184 ≤ n) (hi : n ≤ 191) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair184Gap4
  · exact pair185Gap4
  · exact pair186Gap4
  · exact pair187Gap4
  · exact pair188Gap4
  · exact pair189Gap4
  · exact pair190Gap4
  · exact pair191Gap4


#print axioms range184Gap1
#print axioms range184Gap2
#print axioms range184Gap3
#print axioms range184Gap4

end OrderedPartitions.FourPoleFinite
