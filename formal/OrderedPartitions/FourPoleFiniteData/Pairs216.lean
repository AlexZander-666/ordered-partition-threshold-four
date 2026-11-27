import OrderedPartitions.FourPoleFiniteData.Roots216
import OrderedPartitions.FourPoleFiniteData.Roots224

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair216Gap1 :
    RootTracking.OrderedPair (216/4) (row 216 4) (row 217 4) :=
  stay_pair (by decide) root216 root217 (by decide +kernel)

theorem pair216Gap2 :
    RootTracking.OrderedPair (216/4) (row 216 4) (row 218 4) :=
  stay_pair (by decide) root216 root218 (by decide +kernel)

theorem pair216Gap3 :
    RootTracking.OrderedPair (216/4) (row 216 4) (row 219 4) :=
  stay_pair (by decide) root216 root219 (by decide +kernel)

theorem pair216Gap4 :
    RootTracking.OrderedPair (216/4) (row 216 4) (row 220 4) :=
  rise_pair (by decide) root216 root220 (by decide +kernel)

theorem pair217Gap1 :
    RootTracking.OrderedPair (217/4) (row 217 4) (row 218 4) :=
  stay_pair (by decide) root217 root218 (by decide +kernel)

theorem pair217Gap2 :
    RootTracking.OrderedPair (217/4) (row 217 4) (row 219 4) :=
  stay_pair (by decide) root217 root219 (by decide +kernel)

theorem pair217Gap3 :
    RootTracking.OrderedPair (217/4) (row 217 4) (row 220 4) :=
  rise_pair (by decide) root217 root220 (by decide +kernel)

theorem pair217Gap4 :
    RootTracking.OrderedPair (217/4) (row 217 4) (row 221 4) :=
  rise_pair (by decide) root217 root221 (by decide +kernel)

theorem pair218Gap1 :
    RootTracking.OrderedPair (218/4) (row 218 4) (row 219 4) :=
  stay_pair (by decide) root218 root219 (by decide +kernel)

theorem pair218Gap2 :
    RootTracking.OrderedPair (218/4) (row 218 4) (row 220 4) :=
  rise_pair (by decide) root218 root220 (by decide +kernel)

theorem pair218Gap3 :
    RootTracking.OrderedPair (218/4) (row 218 4) (row 221 4) :=
  rise_pair (by decide) root218 root221 (by decide +kernel)

theorem pair218Gap4 :
    RootTracking.OrderedPair (218/4) (row 218 4) (row 222 4) :=
  rise_pair (by decide) root218 root222 (by decide +kernel)

theorem pair219Gap1 :
    RootTracking.OrderedPair (219/4) (row 219 4) (row 220 4) :=
  rise_pair (by decide) root219 root220 (by decide +kernel)

theorem pair219Gap2 :
    RootTracking.OrderedPair (219/4) (row 219 4) (row 221 4) :=
  rise_pair (by decide) root219 root221 (by decide +kernel)

theorem pair219Gap3 :
    RootTracking.OrderedPair (219/4) (row 219 4) (row 222 4) :=
  rise_pair (by decide) root219 root222 (by decide +kernel)

theorem pair219Gap4 :
    RootTracking.OrderedPair (219/4) (row 219 4) (row 223 4) :=
  rise_pair (by decide) root219 root223 (by decide +kernel)

theorem pair220Gap1 :
    RootTracking.OrderedPair (220/4) (row 220 4) (row 221 4) :=
  stay_pair (by decide) root220 root221 (by decide +kernel)

theorem pair220Gap2 :
    RootTracking.OrderedPair (220/4) (row 220 4) (row 222 4) :=
  stay_pair (by decide) root220 root222 (by decide +kernel)

theorem pair220Gap3 :
    RootTracking.OrderedPair (220/4) (row 220 4) (row 223 4) :=
  stay_pair (by decide) root220 root223 (by decide +kernel)

theorem pair220Gap4 :
    RootTracking.OrderedPair (220/4) (row 220 4) (row 224 4) :=
  rise_pair (by decide) root220 root224 (by decide +kernel)

theorem pair221Gap1 :
    RootTracking.OrderedPair (221/4) (row 221 4) (row 222 4) :=
  stay_pair (by decide) root221 root222 (by decide +kernel)

theorem pair221Gap2 :
    RootTracking.OrderedPair (221/4) (row 221 4) (row 223 4) :=
  stay_pair (by decide) root221 root223 (by decide +kernel)

theorem pair221Gap3 :
    RootTracking.OrderedPair (221/4) (row 221 4) (row 224 4) :=
  rise_pair (by decide) root221 root224 (by decide +kernel)

theorem pair221Gap4 :
    RootTracking.OrderedPair (221/4) (row 221 4) (row 225 4) :=
  rise_pair (by decide) root221 root225 (by decide +kernel)

theorem pair222Gap1 :
    RootTracking.OrderedPair (222/4) (row 222 4) (row 223 4) :=
  stay_pair (by decide) root222 root223 (by decide +kernel)

theorem pair222Gap2 :
    RootTracking.OrderedPair (222/4) (row 222 4) (row 224 4) :=
  rise_pair (by decide) root222 root224 (by decide +kernel)

theorem pair222Gap3 :
    RootTracking.OrderedPair (222/4) (row 222 4) (row 225 4) :=
  rise_pair (by decide) root222 root225 (by decide +kernel)

theorem pair222Gap4 :
    RootTracking.OrderedPair (222/4) (row 222 4) (row 226 4) :=
  rise_pair (by decide) root222 root226 (by decide +kernel)

theorem pair223Gap1 :
    RootTracking.OrderedPair (223/4) (row 223 4) (row 224 4) :=
  rise_pair (by decide) root223 root224 (by decide +kernel)

theorem pair223Gap2 :
    RootTracking.OrderedPair (223/4) (row 223 4) (row 225 4) :=
  rise_pair (by decide) root223 root225 (by decide +kernel)

theorem pair223Gap3 :
    RootTracking.OrderedPair (223/4) (row 223 4) (row 226 4) :=
  rise_pair (by decide) root223 root226 (by decide +kernel)

theorem pair223Gap4 :
    RootTracking.OrderedPair (223/4) (row 223 4) (row 227 4) :=
  rise_pair (by decide) root223 root227 (by decide +kernel)

theorem range216Gap1 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair216Gap1
  · exact pair217Gap1
  · exact pair218Gap1
  · exact pair219Gap1
  · exact pair220Gap1
  · exact pair221Gap1
  · exact pair222Gap1
  · exact pair223Gap1

theorem range216Gap2 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair216Gap2
  · exact pair217Gap2
  · exact pair218Gap2
  · exact pair219Gap2
  · exact pair220Gap2
  · exact pair221Gap2
  · exact pair222Gap2
  · exact pair223Gap2

theorem range216Gap3 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair216Gap3
  · exact pair217Gap3
  · exact pair218Gap3
  · exact pair219Gap3
  · exact pair220Gap3
  · exact pair221Gap3
  · exact pair222Gap3
  · exact pair223Gap3

theorem range216Gap4 (n : ℕ) (lo : 216 ≤ n) (hi : n ≤ 223) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair216Gap4
  · exact pair217Gap4
  · exact pair218Gap4
  · exact pair219Gap4
  · exact pair220Gap4
  · exact pair221Gap4
  · exact pair222Gap4
  · exact pair223Gap4


#print axioms range216Gap1
#print axioms range216Gap2
#print axioms range216Gap3
#print axioms range216Gap4

end OrderedPartitions.FourPoleFinite
