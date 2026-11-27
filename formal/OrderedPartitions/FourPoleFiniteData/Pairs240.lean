import OrderedPartitions.FourPoleFiniteData.Roots240
import OrderedPartitions.FourPoleFiniteData.Roots248

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair240Gap1 :
    RootTracking.OrderedPair (240/4) (row 240 4) (row 241 4) :=
  stay_pair (by decide) root240 root241 (by decide +kernel)

theorem pair240Gap2 :
    RootTracking.OrderedPair (240/4) (row 240 4) (row 242 4) :=
  stay_pair (by decide) root240 root242 (by decide +kernel)

theorem pair240Gap3 :
    RootTracking.OrderedPair (240/4) (row 240 4) (row 243 4) :=
  stay_pair (by decide) root240 root243 (by decide +kernel)

theorem pair240Gap4 :
    RootTracking.OrderedPair (240/4) (row 240 4) (row 244 4) :=
  rise_pair (by decide) root240 root244 (by decide +kernel)

theorem pair241Gap1 :
    RootTracking.OrderedPair (241/4) (row 241 4) (row 242 4) :=
  stay_pair (by decide) root241 root242 (by decide +kernel)

theorem pair241Gap2 :
    RootTracking.OrderedPair (241/4) (row 241 4) (row 243 4) :=
  stay_pair (by decide) root241 root243 (by decide +kernel)

theorem pair241Gap3 :
    RootTracking.OrderedPair (241/4) (row 241 4) (row 244 4) :=
  rise_pair (by decide) root241 root244 (by decide +kernel)

theorem pair241Gap4 :
    RootTracking.OrderedPair (241/4) (row 241 4) (row 245 4) :=
  rise_pair (by decide) root241 root245 (by decide +kernel)

theorem pair242Gap1 :
    RootTracking.OrderedPair (242/4) (row 242 4) (row 243 4) :=
  stay_pair (by decide) root242 root243 (by decide +kernel)

theorem pair242Gap2 :
    RootTracking.OrderedPair (242/4) (row 242 4) (row 244 4) :=
  rise_pair (by decide) root242 root244 (by decide +kernel)

theorem pair242Gap3 :
    RootTracking.OrderedPair (242/4) (row 242 4) (row 245 4) :=
  rise_pair (by decide) root242 root245 (by decide +kernel)

theorem pair242Gap4 :
    RootTracking.OrderedPair (242/4) (row 242 4) (row 246 4) :=
  rise_pair (by decide) root242 root246 (by decide +kernel)

theorem pair243Gap1 :
    RootTracking.OrderedPair (243/4) (row 243 4) (row 244 4) :=
  rise_pair (by decide) root243 root244 (by decide +kernel)

theorem pair243Gap2 :
    RootTracking.OrderedPair (243/4) (row 243 4) (row 245 4) :=
  rise_pair (by decide) root243 root245 (by decide +kernel)

theorem pair243Gap3 :
    RootTracking.OrderedPair (243/4) (row 243 4) (row 246 4) :=
  rise_pair (by decide) root243 root246 (by decide +kernel)

theorem pair243Gap4 :
    RootTracking.OrderedPair (243/4) (row 243 4) (row 247 4) :=
  rise_pair (by decide) root243 root247 (by decide +kernel)

theorem pair244Gap1 :
    RootTracking.OrderedPair (244/4) (row 244 4) (row 245 4) :=
  stay_pair (by decide) root244 root245 (by decide +kernel)

theorem pair244Gap2 :
    RootTracking.OrderedPair (244/4) (row 244 4) (row 246 4) :=
  stay_pair (by decide) root244 root246 (by decide +kernel)

theorem pair244Gap3 :
    RootTracking.OrderedPair (244/4) (row 244 4) (row 247 4) :=
  stay_pair (by decide) root244 root247 (by decide +kernel)

theorem pair244Gap4 :
    RootTracking.OrderedPair (244/4) (row 244 4) (row 248 4) :=
  rise_pair (by decide) root244 root248 (by decide +kernel)

theorem pair245Gap1 :
    RootTracking.OrderedPair (245/4) (row 245 4) (row 246 4) :=
  stay_pair (by decide) root245 root246 (by decide +kernel)

theorem pair245Gap2 :
    RootTracking.OrderedPair (245/4) (row 245 4) (row 247 4) :=
  stay_pair (by decide) root245 root247 (by decide +kernel)

theorem pair245Gap3 :
    RootTracking.OrderedPair (245/4) (row 245 4) (row 248 4) :=
  rise_pair (by decide) root245 root248 (by decide +kernel)

theorem pair245Gap4 :
    RootTracking.OrderedPair (245/4) (row 245 4) (row 249 4) :=
  rise_pair (by decide) root245 root249 (by decide +kernel)

theorem pair246Gap1 :
    RootTracking.OrderedPair (246/4) (row 246 4) (row 247 4) :=
  stay_pair (by decide) root246 root247 (by decide +kernel)

theorem pair246Gap2 :
    RootTracking.OrderedPair (246/4) (row 246 4) (row 248 4) :=
  rise_pair (by decide) root246 root248 (by decide +kernel)

theorem pair246Gap3 :
    RootTracking.OrderedPair (246/4) (row 246 4) (row 249 4) :=
  rise_pair (by decide) root246 root249 (by decide +kernel)

theorem pair246Gap4 :
    RootTracking.OrderedPair (246/4) (row 246 4) (row 250 4) :=
  rise_pair (by decide) root246 root250 (by decide +kernel)

theorem pair247Gap1 :
    RootTracking.OrderedPair (247/4) (row 247 4) (row 248 4) :=
  rise_pair (by decide) root247 root248 (by decide +kernel)

theorem pair247Gap2 :
    RootTracking.OrderedPair (247/4) (row 247 4) (row 249 4) :=
  rise_pair (by decide) root247 root249 (by decide +kernel)

theorem pair247Gap3 :
    RootTracking.OrderedPair (247/4) (row 247 4) (row 250 4) :=
  rise_pair (by decide) root247 root250 (by decide +kernel)

theorem pair247Gap4 :
    RootTracking.OrderedPair (247/4) (row 247 4) (row 251 4) :=
  rise_pair (by decide) root247 root251 (by decide +kernel)

theorem range240Gap1 (n : ℕ) (lo : 240 ≤ n) (hi : n ≤ 247) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair240Gap1
  · exact pair241Gap1
  · exact pair242Gap1
  · exact pair243Gap1
  · exact pair244Gap1
  · exact pair245Gap1
  · exact pair246Gap1
  · exact pair247Gap1

theorem range240Gap2 (n : ℕ) (lo : 240 ≤ n) (hi : n ≤ 247) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair240Gap2
  · exact pair241Gap2
  · exact pair242Gap2
  · exact pair243Gap2
  · exact pair244Gap2
  · exact pair245Gap2
  · exact pair246Gap2
  · exact pair247Gap2

theorem range240Gap3 (n : ℕ) (lo : 240 ≤ n) (hi : n ≤ 247) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair240Gap3
  · exact pair241Gap3
  · exact pair242Gap3
  · exact pair243Gap3
  · exact pair244Gap3
  · exact pair245Gap3
  · exact pair246Gap3
  · exact pair247Gap3

theorem range240Gap4 (n : ℕ) (lo : 240 ≤ n) (hi : n ≤ 247) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair240Gap4
  · exact pair241Gap4
  · exact pair242Gap4
  · exact pair243Gap4
  · exact pair244Gap4
  · exact pair245Gap4
  · exact pair246Gap4
  · exact pair247Gap4


#print axioms range240Gap1
#print axioms range240Gap2
#print axioms range240Gap3
#print axioms range240Gap4

end OrderedPartitions.FourPoleFinite
