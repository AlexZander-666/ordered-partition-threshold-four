import OrderedPartitions.FourPoleFiniteData.Roots256
import OrderedPartitions.FourPoleFiniteData.Roots264

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair256Gap1 :
    RootTracking.OrderedPair (256/4) (row 256 4) (row 257 4) :=
  stay_pair (by decide) root256 root257 (by decide +kernel)

theorem pair256Gap2 :
    RootTracking.OrderedPair (256/4) (row 256 4) (row 258 4) :=
  stay_pair (by decide) root256 root258 (by decide +kernel)

theorem pair256Gap3 :
    RootTracking.OrderedPair (256/4) (row 256 4) (row 259 4) :=
  stay_pair (by decide) root256 root259 (by decide +kernel)

theorem pair256Gap4 :
    RootTracking.OrderedPair (256/4) (row 256 4) (row 260 4) :=
  rise_pair (by decide) root256 root260 (by decide +kernel)

theorem pair257Gap1 :
    RootTracking.OrderedPair (257/4) (row 257 4) (row 258 4) :=
  stay_pair (by decide) root257 root258 (by decide +kernel)

theorem pair257Gap2 :
    RootTracking.OrderedPair (257/4) (row 257 4) (row 259 4) :=
  stay_pair (by decide) root257 root259 (by decide +kernel)

theorem pair257Gap3 :
    RootTracking.OrderedPair (257/4) (row 257 4) (row 260 4) :=
  rise_pair (by decide) root257 root260 (by decide +kernel)

theorem pair257Gap4 :
    RootTracking.OrderedPair (257/4) (row 257 4) (row 261 4) :=
  rise_pair (by decide) root257 root261 (by decide +kernel)

theorem pair258Gap1 :
    RootTracking.OrderedPair (258/4) (row 258 4) (row 259 4) :=
  stay_pair (by decide) root258 root259 (by decide +kernel)

theorem pair258Gap2 :
    RootTracking.OrderedPair (258/4) (row 258 4) (row 260 4) :=
  rise_pair (by decide) root258 root260 (by decide +kernel)

theorem pair258Gap3 :
    RootTracking.OrderedPair (258/4) (row 258 4) (row 261 4) :=
  rise_pair (by decide) root258 root261 (by decide +kernel)

theorem pair258Gap4 :
    RootTracking.OrderedPair (258/4) (row 258 4) (row 262 4) :=
  rise_pair (by decide) root258 root262 (by decide +kernel)

theorem pair259Gap1 :
    RootTracking.OrderedPair (259/4) (row 259 4) (row 260 4) :=
  rise_pair (by decide) root259 root260 (by decide +kernel)

theorem pair259Gap2 :
    RootTracking.OrderedPair (259/4) (row 259 4) (row 261 4) :=
  rise_pair (by decide) root259 root261 (by decide +kernel)

theorem pair259Gap3 :
    RootTracking.OrderedPair (259/4) (row 259 4) (row 262 4) :=
  rise_pair (by decide) root259 root262 (by decide +kernel)

theorem pair259Gap4 :
    RootTracking.OrderedPair (259/4) (row 259 4) (row 263 4) :=
  rise_pair (by decide) root259 root263 (by decide +kernel)

theorem pair260Gap1 :
    RootTracking.OrderedPair (260/4) (row 260 4) (row 261 4) :=
  stay_pair (by decide) root260 root261 (by decide +kernel)

theorem pair260Gap2 :
    RootTracking.OrderedPair (260/4) (row 260 4) (row 262 4) :=
  stay_pair (by decide) root260 root262 (by decide +kernel)

theorem pair260Gap3 :
    RootTracking.OrderedPair (260/4) (row 260 4) (row 263 4) :=
  stay_pair (by decide) root260 root263 (by decide +kernel)

theorem pair260Gap4 :
    RootTracking.OrderedPair (260/4) (row 260 4) (row 264 4) :=
  rise_pair (by decide) root260 root264 (by decide +kernel)

theorem pair261Gap1 :
    RootTracking.OrderedPair (261/4) (row 261 4) (row 262 4) :=
  stay_pair (by decide) root261 root262 (by decide +kernel)

theorem pair261Gap2 :
    RootTracking.OrderedPair (261/4) (row 261 4) (row 263 4) :=
  stay_pair (by decide) root261 root263 (by decide +kernel)

theorem pair261Gap3 :
    RootTracking.OrderedPair (261/4) (row 261 4) (row 264 4) :=
  rise_pair (by decide) root261 root264 (by decide +kernel)

theorem pair261Gap4 :
    RootTracking.OrderedPair (261/4) (row 261 4) (row 265 4) :=
  rise_pair (by decide) root261 root265 (by decide +kernel)

theorem pair262Gap1 :
    RootTracking.OrderedPair (262/4) (row 262 4) (row 263 4) :=
  stay_pair (by decide) root262 root263 (by decide +kernel)

theorem pair262Gap2 :
    RootTracking.OrderedPair (262/4) (row 262 4) (row 264 4) :=
  rise_pair (by decide) root262 root264 (by decide +kernel)

theorem pair262Gap3 :
    RootTracking.OrderedPair (262/4) (row 262 4) (row 265 4) :=
  rise_pair (by decide) root262 root265 (by decide +kernel)

theorem pair262Gap4 :
    RootTracking.OrderedPair (262/4) (row 262 4) (row 266 4) :=
  rise_pair (by decide) root262 root266 (by decide +kernel)

theorem pair263Gap1 :
    RootTracking.OrderedPair (263/4) (row 263 4) (row 264 4) :=
  rise_pair (by decide) root263 root264 (by decide +kernel)

theorem pair263Gap2 :
    RootTracking.OrderedPair (263/4) (row 263 4) (row 265 4) :=
  rise_pair (by decide) root263 root265 (by decide +kernel)

theorem pair263Gap3 :
    RootTracking.OrderedPair (263/4) (row 263 4) (row 266 4) :=
  rise_pair (by decide) root263 root266 (by decide +kernel)

theorem pair263Gap4 :
    RootTracking.OrderedPair (263/4) (row 263 4) (row 267 4) :=
  rise_pair (by decide) root263 root267 (by decide +kernel)

theorem range256Gap1 (n : ℕ) (lo : 256 ≤ n) (hi : n ≤ 263) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair256Gap1
  · exact pair257Gap1
  · exact pair258Gap1
  · exact pair259Gap1
  · exact pair260Gap1
  · exact pair261Gap1
  · exact pair262Gap1
  · exact pair263Gap1

theorem range256Gap2 (n : ℕ) (lo : 256 ≤ n) (hi : n ≤ 263) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair256Gap2
  · exact pair257Gap2
  · exact pair258Gap2
  · exact pair259Gap2
  · exact pair260Gap2
  · exact pair261Gap2
  · exact pair262Gap2
  · exact pair263Gap2

theorem range256Gap3 (n : ℕ) (lo : 256 ≤ n) (hi : n ≤ 263) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair256Gap3
  · exact pair257Gap3
  · exact pair258Gap3
  · exact pair259Gap3
  · exact pair260Gap3
  · exact pair261Gap3
  · exact pair262Gap3
  · exact pair263Gap3

theorem range256Gap4 (n : ℕ) (lo : 256 ≤ n) (hi : n ≤ 263) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair256Gap4
  · exact pair257Gap4
  · exact pair258Gap4
  · exact pair259Gap4
  · exact pair260Gap4
  · exact pair261Gap4
  · exact pair262Gap4
  · exact pair263Gap4


#print axioms range256Gap1
#print axioms range256Gap2
#print axioms range256Gap3
#print axioms range256Gap4

end OrderedPartitions.FourPoleFinite
