import OrderedPartitions.FourPoleFiniteData.Roots272
import OrderedPartitions.FourPoleFiniteData.Roots280

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair272Gap1 :
    RootTracking.OrderedPair (272/4) (row 272 4) (row 273 4) :=
  stay_pair (by decide) root272 root273 (by decide +kernel)

theorem pair272Gap2 :
    RootTracking.OrderedPair (272/4) (row 272 4) (row 274 4) :=
  stay_pair (by decide) root272 root274 (by decide +kernel)

theorem pair272Gap3 :
    RootTracking.OrderedPair (272/4) (row 272 4) (row 275 4) :=
  stay_pair (by decide) root272 root275 (by decide +kernel)

theorem pair272Gap4 :
    RootTracking.OrderedPair (272/4) (row 272 4) (row 276 4) :=
  rise_pair (by decide) root272 root276 (by decide +kernel)

theorem pair273Gap1 :
    RootTracking.OrderedPair (273/4) (row 273 4) (row 274 4) :=
  stay_pair (by decide) root273 root274 (by decide +kernel)

theorem pair273Gap2 :
    RootTracking.OrderedPair (273/4) (row 273 4) (row 275 4) :=
  stay_pair (by decide) root273 root275 (by decide +kernel)

theorem pair273Gap3 :
    RootTracking.OrderedPair (273/4) (row 273 4) (row 276 4) :=
  rise_pair (by decide) root273 root276 (by decide +kernel)

theorem pair273Gap4 :
    RootTracking.OrderedPair (273/4) (row 273 4) (row 277 4) :=
  rise_pair (by decide) root273 root277 (by decide +kernel)

theorem pair274Gap1 :
    RootTracking.OrderedPair (274/4) (row 274 4) (row 275 4) :=
  stay_pair (by decide) root274 root275 (by decide +kernel)

theorem pair274Gap2 :
    RootTracking.OrderedPair (274/4) (row 274 4) (row 276 4) :=
  rise_pair (by decide) root274 root276 (by decide +kernel)

theorem pair274Gap3 :
    RootTracking.OrderedPair (274/4) (row 274 4) (row 277 4) :=
  rise_pair (by decide) root274 root277 (by decide +kernel)

theorem pair274Gap4 :
    RootTracking.OrderedPair (274/4) (row 274 4) (row 278 4) :=
  rise_pair (by decide) root274 root278 (by decide +kernel)

theorem pair275Gap1 :
    RootTracking.OrderedPair (275/4) (row 275 4) (row 276 4) :=
  rise_pair (by decide) root275 root276 (by decide +kernel)

theorem pair275Gap2 :
    RootTracking.OrderedPair (275/4) (row 275 4) (row 277 4) :=
  rise_pair (by decide) root275 root277 (by decide +kernel)

theorem pair275Gap3 :
    RootTracking.OrderedPair (275/4) (row 275 4) (row 278 4) :=
  rise_pair (by decide) root275 root278 (by decide +kernel)

theorem pair275Gap4 :
    RootTracking.OrderedPair (275/4) (row 275 4) (row 279 4) :=
  rise_pair (by decide) root275 root279 (by decide +kernel)

theorem pair276Gap1 :
    RootTracking.OrderedPair (276/4) (row 276 4) (row 277 4) :=
  stay_pair (by decide) root276 root277 (by decide +kernel)

theorem pair276Gap2 :
    RootTracking.OrderedPair (276/4) (row 276 4) (row 278 4) :=
  stay_pair (by decide) root276 root278 (by decide +kernel)

theorem pair276Gap3 :
    RootTracking.OrderedPair (276/4) (row 276 4) (row 279 4) :=
  stay_pair (by decide) root276 root279 (by decide +kernel)

theorem pair276Gap4 :
    RootTracking.OrderedPair (276/4) (row 276 4) (row 280 4) :=
  rise_pair (by decide) root276 root280 (by decide +kernel)

theorem pair277Gap1 :
    RootTracking.OrderedPair (277/4) (row 277 4) (row 278 4) :=
  stay_pair (by decide) root277 root278 (by decide +kernel)

theorem pair277Gap2 :
    RootTracking.OrderedPair (277/4) (row 277 4) (row 279 4) :=
  stay_pair (by decide) root277 root279 (by decide +kernel)

theorem pair277Gap3 :
    RootTracking.OrderedPair (277/4) (row 277 4) (row 280 4) :=
  rise_pair (by decide) root277 root280 (by decide +kernel)

theorem pair277Gap4 :
    RootTracking.OrderedPair (277/4) (row 277 4) (row 281 4) :=
  rise_pair (by decide) root277 root281 (by decide +kernel)

theorem pair278Gap1 :
    RootTracking.OrderedPair (278/4) (row 278 4) (row 279 4) :=
  stay_pair (by decide) root278 root279 (by decide +kernel)

theorem pair278Gap2 :
    RootTracking.OrderedPair (278/4) (row 278 4) (row 280 4) :=
  rise_pair (by decide) root278 root280 (by decide +kernel)

theorem pair278Gap3 :
    RootTracking.OrderedPair (278/4) (row 278 4) (row 281 4) :=
  rise_pair (by decide) root278 root281 (by decide +kernel)

theorem pair278Gap4 :
    RootTracking.OrderedPair (278/4) (row 278 4) (row 282 4) :=
  rise_pair (by decide) root278 root282 (by decide +kernel)

theorem pair279Gap1 :
    RootTracking.OrderedPair (279/4) (row 279 4) (row 280 4) :=
  rise_pair (by decide) root279 root280 (by decide +kernel)

theorem pair279Gap2 :
    RootTracking.OrderedPair (279/4) (row 279 4) (row 281 4) :=
  rise_pair (by decide) root279 root281 (by decide +kernel)

theorem pair279Gap3 :
    RootTracking.OrderedPair (279/4) (row 279 4) (row 282 4) :=
  rise_pair (by decide) root279 root282 (by decide +kernel)

theorem pair279Gap4 :
    RootTracking.OrderedPair (279/4) (row 279 4) (row 283 4) :=
  rise_pair (by decide) root279 root283 (by decide +kernel)

theorem range272Gap1 (n : ℕ) (lo : 272 ≤ n) (hi : n ≤ 279) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair272Gap1
  · exact pair273Gap1
  · exact pair274Gap1
  · exact pair275Gap1
  · exact pair276Gap1
  · exact pair277Gap1
  · exact pair278Gap1
  · exact pair279Gap1

theorem range272Gap2 (n : ℕ) (lo : 272 ≤ n) (hi : n ≤ 279) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair272Gap2
  · exact pair273Gap2
  · exact pair274Gap2
  · exact pair275Gap2
  · exact pair276Gap2
  · exact pair277Gap2
  · exact pair278Gap2
  · exact pair279Gap2

theorem range272Gap3 (n : ℕ) (lo : 272 ≤ n) (hi : n ≤ 279) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair272Gap3
  · exact pair273Gap3
  · exact pair274Gap3
  · exact pair275Gap3
  · exact pair276Gap3
  · exact pair277Gap3
  · exact pair278Gap3
  · exact pair279Gap3

theorem range272Gap4 (n : ℕ) (lo : 272 ≤ n) (hi : n ≤ 279) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair272Gap4
  · exact pair273Gap4
  · exact pair274Gap4
  · exact pair275Gap4
  · exact pair276Gap4
  · exact pair277Gap4
  · exact pair278Gap4
  · exact pair279Gap4


#print axioms range272Gap1
#print axioms range272Gap2
#print axioms range272Gap3
#print axioms range272Gap4

end OrderedPartitions.FourPoleFinite
