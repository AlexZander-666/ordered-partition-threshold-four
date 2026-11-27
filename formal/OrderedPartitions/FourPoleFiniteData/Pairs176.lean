import OrderedPartitions.FourPoleFiniteData.Roots176
import OrderedPartitions.FourPoleFiniteData.Roots184

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair176Gap1 :
    RootTracking.OrderedPair (176/4) (row 176 4) (row 177 4) :=
  stay_pair (by decide) root176 root177 (by decide +kernel)

theorem pair176Gap2 :
    RootTracking.OrderedPair (176/4) (row 176 4) (row 178 4) :=
  stay_pair (by decide) root176 root178 (by decide +kernel)

theorem pair176Gap3 :
    RootTracking.OrderedPair (176/4) (row 176 4) (row 179 4) :=
  stay_pair (by decide) root176 root179 (by decide +kernel)

theorem pair176Gap4 :
    RootTracking.OrderedPair (176/4) (row 176 4) (row 180 4) :=
  rise_pair (by decide) root176 root180 (by decide +kernel)

theorem pair177Gap1 :
    RootTracking.OrderedPair (177/4) (row 177 4) (row 178 4) :=
  stay_pair (by decide) root177 root178 (by decide +kernel)

theorem pair177Gap2 :
    RootTracking.OrderedPair (177/4) (row 177 4) (row 179 4) :=
  stay_pair (by decide) root177 root179 (by decide +kernel)

theorem pair177Gap3 :
    RootTracking.OrderedPair (177/4) (row 177 4) (row 180 4) :=
  rise_pair (by decide) root177 root180 (by decide +kernel)

theorem pair177Gap4 :
    RootTracking.OrderedPair (177/4) (row 177 4) (row 181 4) :=
  rise_pair (by decide) root177 root181 (by decide +kernel)

theorem pair178Gap1 :
    RootTracking.OrderedPair (178/4) (row 178 4) (row 179 4) :=
  stay_pair (by decide) root178 root179 (by decide +kernel)

theorem pair178Gap2 :
    RootTracking.OrderedPair (178/4) (row 178 4) (row 180 4) :=
  rise_pair (by decide) root178 root180 (by decide +kernel)

theorem pair178Gap3 :
    RootTracking.OrderedPair (178/4) (row 178 4) (row 181 4) :=
  rise_pair (by decide) root178 root181 (by decide +kernel)

theorem pair178Gap4 :
    RootTracking.OrderedPair (178/4) (row 178 4) (row 182 4) :=
  rise_pair (by decide) root178 root182 (by decide +kernel)

theorem pair179Gap1 :
    RootTracking.OrderedPair (179/4) (row 179 4) (row 180 4) :=
  rise_pair (by decide) root179 root180 (by decide +kernel)

theorem pair179Gap2 :
    RootTracking.OrderedPair (179/4) (row 179 4) (row 181 4) :=
  rise_pair (by decide) root179 root181 (by decide +kernel)

theorem pair179Gap3 :
    RootTracking.OrderedPair (179/4) (row 179 4) (row 182 4) :=
  rise_pair (by decide) root179 root182 (by decide +kernel)

theorem pair179Gap4 :
    RootTracking.OrderedPair (179/4) (row 179 4) (row 183 4) :=
  rise_pair (by decide) root179 root183 (by decide +kernel)

theorem pair180Gap1 :
    RootTracking.OrderedPair (180/4) (row 180 4) (row 181 4) :=
  stay_pair (by decide) root180 root181 (by decide +kernel)

theorem pair180Gap2 :
    RootTracking.OrderedPair (180/4) (row 180 4) (row 182 4) :=
  stay_pair (by decide) root180 root182 (by decide +kernel)

theorem pair180Gap3 :
    RootTracking.OrderedPair (180/4) (row 180 4) (row 183 4) :=
  stay_pair (by decide) root180 root183 (by decide +kernel)

theorem pair180Gap4 :
    RootTracking.OrderedPair (180/4) (row 180 4) (row 184 4) :=
  rise_pair (by decide) root180 root184 (by decide +kernel)

theorem pair181Gap1 :
    RootTracking.OrderedPair (181/4) (row 181 4) (row 182 4) :=
  stay_pair (by decide) root181 root182 (by decide +kernel)

theorem pair181Gap2 :
    RootTracking.OrderedPair (181/4) (row 181 4) (row 183 4) :=
  stay_pair (by decide) root181 root183 (by decide +kernel)

theorem pair181Gap3 :
    RootTracking.OrderedPair (181/4) (row 181 4) (row 184 4) :=
  rise_pair (by decide) root181 root184 (by decide +kernel)

theorem pair181Gap4 :
    RootTracking.OrderedPair (181/4) (row 181 4) (row 185 4) :=
  rise_pair (by decide) root181 root185 (by decide +kernel)

theorem pair182Gap1 :
    RootTracking.OrderedPair (182/4) (row 182 4) (row 183 4) :=
  stay_pair (by decide) root182 root183 (by decide +kernel)

theorem pair182Gap2 :
    RootTracking.OrderedPair (182/4) (row 182 4) (row 184 4) :=
  rise_pair (by decide) root182 root184 (by decide +kernel)

theorem pair182Gap3 :
    RootTracking.OrderedPair (182/4) (row 182 4) (row 185 4) :=
  rise_pair (by decide) root182 root185 (by decide +kernel)

theorem pair182Gap4 :
    RootTracking.OrderedPair (182/4) (row 182 4) (row 186 4) :=
  rise_pair (by decide) root182 root186 (by decide +kernel)

theorem pair183Gap1 :
    RootTracking.OrderedPair (183/4) (row 183 4) (row 184 4) :=
  rise_pair (by decide) root183 root184 (by decide +kernel)

theorem pair183Gap2 :
    RootTracking.OrderedPair (183/4) (row 183 4) (row 185 4) :=
  rise_pair (by decide) root183 root185 (by decide +kernel)

theorem pair183Gap3 :
    RootTracking.OrderedPair (183/4) (row 183 4) (row 186 4) :=
  rise_pair (by decide) root183 root186 (by decide +kernel)

theorem pair183Gap4 :
    RootTracking.OrderedPair (183/4) (row 183 4) (row 187 4) :=
  rise_pair (by decide) root183 root187 (by decide +kernel)

theorem range176Gap1 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair176Gap1
  · exact pair177Gap1
  · exact pair178Gap1
  · exact pair179Gap1
  · exact pair180Gap1
  · exact pair181Gap1
  · exact pair182Gap1
  · exact pair183Gap1

theorem range176Gap2 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair176Gap2
  · exact pair177Gap2
  · exact pair178Gap2
  · exact pair179Gap2
  · exact pair180Gap2
  · exact pair181Gap2
  · exact pair182Gap2
  · exact pair183Gap2

theorem range176Gap3 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair176Gap3
  · exact pair177Gap3
  · exact pair178Gap3
  · exact pair179Gap3
  · exact pair180Gap3
  · exact pair181Gap3
  · exact pair182Gap3
  · exact pair183Gap3

theorem range176Gap4 (n : ℕ) (lo : 176 ≤ n) (hi : n ≤ 183) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair176Gap4
  · exact pair177Gap4
  · exact pair178Gap4
  · exact pair179Gap4
  · exact pair180Gap4
  · exact pair181Gap4
  · exact pair182Gap4
  · exact pair183Gap4


#print axioms range176Gap1
#print axioms range176Gap2
#print axioms range176Gap3
#print axioms range176Gap4

end OrderedPartitions.FourPoleFinite
