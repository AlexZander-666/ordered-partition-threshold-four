import OrderedPartitions.FourPoleFiniteData.Roots104
import OrderedPartitions.FourPoleFiniteData.Roots112

namespace OrderedPartitions.FourPoleFinite

set_option maxRecDepth 65536
set_option maxHeartbeats 0

theorem pair104Gap1 :
    RootTracking.OrderedPair (104/4) (row 104 4) (row 105 4) :=
  stay_pair (by decide) root104 root105 (by decide +kernel)

theorem pair104Gap2 :
    RootTracking.OrderedPair (104/4) (row 104 4) (row 106 4) :=
  stay_pair (by decide) root104 root106 (by decide +kernel)

theorem pair104Gap3 :
    RootTracking.OrderedPair (104/4) (row 104 4) (row 107 4) :=
  stay_pair (by decide) root104 root107 (by decide +kernel)

theorem pair104Gap4 :
    RootTracking.OrderedPair (104/4) (row 104 4) (row 108 4) :=
  rise_pair (by decide) root104 root108 (by decide +kernel)

theorem pair105Gap1 :
    RootTracking.OrderedPair (105/4) (row 105 4) (row 106 4) :=
  stay_pair (by decide) root105 root106 (by decide +kernel)

theorem pair105Gap2 :
    RootTracking.OrderedPair (105/4) (row 105 4) (row 107 4) :=
  stay_pair (by decide) root105 root107 (by decide +kernel)

theorem pair105Gap3 :
    RootTracking.OrderedPair (105/4) (row 105 4) (row 108 4) :=
  rise_pair (by decide) root105 root108 (by decide +kernel)

theorem pair105Gap4 :
    RootTracking.OrderedPair (105/4) (row 105 4) (row 109 4) :=
  rise_pair (by decide) root105 root109 (by decide +kernel)

theorem pair106Gap1 :
    RootTracking.OrderedPair (106/4) (row 106 4) (row 107 4) :=
  stay_pair (by decide) root106 root107 (by decide +kernel)

theorem pair106Gap2 :
    RootTracking.OrderedPair (106/4) (row 106 4) (row 108 4) :=
  rise_pair (by decide) root106 root108 (by decide +kernel)

theorem pair106Gap3 :
    RootTracking.OrderedPair (106/4) (row 106 4) (row 109 4) :=
  rise_pair (by decide) root106 root109 (by decide +kernel)

theorem pair106Gap4 :
    RootTracking.OrderedPair (106/4) (row 106 4) (row 110 4) :=
  rise_pair (by decide) root106 root110 (by decide +kernel)

theorem pair107Gap1 :
    RootTracking.OrderedPair (107/4) (row 107 4) (row 108 4) :=
  rise_pair (by decide) root107 root108 (by decide +kernel)

theorem pair107Gap2 :
    RootTracking.OrderedPair (107/4) (row 107 4) (row 109 4) :=
  rise_pair (by decide) root107 root109 (by decide +kernel)

theorem pair107Gap3 :
    RootTracking.OrderedPair (107/4) (row 107 4) (row 110 4) :=
  rise_pair (by decide) root107 root110 (by decide +kernel)

theorem pair107Gap4 :
    RootTracking.OrderedPair (107/4) (row 107 4) (row 111 4) :=
  rise_pair (by decide) root107 root111 (by decide +kernel)

theorem pair108Gap1 :
    RootTracking.OrderedPair (108/4) (row 108 4) (row 109 4) :=
  stay_pair (by decide) root108 root109 (by decide +kernel)

theorem pair108Gap2 :
    RootTracking.OrderedPair (108/4) (row 108 4) (row 110 4) :=
  stay_pair (by decide) root108 root110 (by decide +kernel)

theorem pair108Gap3 :
    RootTracking.OrderedPair (108/4) (row 108 4) (row 111 4) :=
  stay_pair (by decide) root108 root111 (by decide +kernel)

theorem pair108Gap4 :
    RootTracking.OrderedPair (108/4) (row 108 4) (row 112 4) :=
  rise_pair (by decide) root108 root112 (by decide +kernel)

theorem pair109Gap1 :
    RootTracking.OrderedPair (109/4) (row 109 4) (row 110 4) :=
  stay_pair (by decide) root109 root110 (by decide +kernel)

theorem pair109Gap2 :
    RootTracking.OrderedPair (109/4) (row 109 4) (row 111 4) :=
  stay_pair (by decide) root109 root111 (by decide +kernel)

theorem pair109Gap3 :
    RootTracking.OrderedPair (109/4) (row 109 4) (row 112 4) :=
  rise_pair (by decide) root109 root112 (by decide +kernel)

theorem pair109Gap4 :
    RootTracking.OrderedPair (109/4) (row 109 4) (row 113 4) :=
  rise_pair (by decide) root109 root113 (by decide +kernel)

theorem pair110Gap1 :
    RootTracking.OrderedPair (110/4) (row 110 4) (row 111 4) :=
  stay_pair (by decide) root110 root111 (by decide +kernel)

theorem pair110Gap2 :
    RootTracking.OrderedPair (110/4) (row 110 4) (row 112 4) :=
  rise_pair (by decide) root110 root112 (by decide +kernel)

theorem pair110Gap3 :
    RootTracking.OrderedPair (110/4) (row 110 4) (row 113 4) :=
  rise_pair (by decide) root110 root113 (by decide +kernel)

theorem pair110Gap4 :
    RootTracking.OrderedPair (110/4) (row 110 4) (row 114 4) :=
  rise_pair (by decide) root110 root114 (by decide +kernel)

theorem pair111Gap1 :
    RootTracking.OrderedPair (111/4) (row 111 4) (row 112 4) :=
  rise_pair (by decide) root111 root112 (by decide +kernel)

theorem pair111Gap2 :
    RootTracking.OrderedPair (111/4) (row 111 4) (row 113 4) :=
  rise_pair (by decide) root111 root113 (by decide +kernel)

theorem pair111Gap3 :
    RootTracking.OrderedPair (111/4) (row 111 4) (row 114 4) :=
  rise_pair (by decide) root111 root114 (by decide +kernel)

theorem pair111Gap4 :
    RootTracking.OrderedPair (111/4) (row 111 4) (row 115 4) :=
  rise_pair (by decide) root111 root115 (by decide +kernel)

theorem range104Gap1 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+1) 4) := by
  interval_cases n
  · exact pair104Gap1
  · exact pair105Gap1
  · exact pair106Gap1
  · exact pair107Gap1
  · exact pair108Gap1
  · exact pair109Gap1
  · exact pair110Gap1
  · exact pair111Gap1

theorem range104Gap2 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+2) 4) := by
  interval_cases n
  · exact pair104Gap2
  · exact pair105Gap2
  · exact pair106Gap2
  · exact pair107Gap2
  · exact pair108Gap2
  · exact pair109Gap2
  · exact pair110Gap2
  · exact pair111Gap2

theorem range104Gap3 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+3) 4) := by
  interval_cases n
  · exact pair104Gap3
  · exact pair105Gap3
  · exact pair106Gap3
  · exact pair107Gap3
  · exact pair108Gap3
  · exact pair109Gap3
  · exact pair110Gap3
  · exact pair111Gap3

theorem range104Gap4 (n : ℕ) (lo : 104 ≤ n) (hi : n ≤ 111) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+4) 4) := by
  interval_cases n
  · exact pair104Gap4
  · exact pair105Gap4
  · exact pair106Gap4
  · exact pair107Gap4
  · exact pair108Gap4
  · exact pair109Gap4
  · exact pair110Gap4
  · exact pair111Gap4


#print axioms range104Gap1
#print axioms range104Gap2
#print axioms range104Gap3
#print axioms range104Gap4

end OrderedPartitions.FourPoleFinite
