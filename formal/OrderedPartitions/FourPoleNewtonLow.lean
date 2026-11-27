import OrderedPartitions.FourPoleNewtonSeries

noncomputable section
namespace OrderedPartitions.ExpInterpolation
open Complex Finset

def powers (i : ℕ) (a b c d z : ℂ) := a^i+b^i+c^i+d^i+z^i
def powerCap (i : ℕ) : ℝ := 17*(72/25:ℝ)^(i-2)

theorem powers_le (i : ℕ) (hi : 2 ≤ i) {a b c d z : ℂ}
    (ha : ‖a‖≤72/25) (hb : ‖b‖≤72/25) (hc : ‖c‖≤72/25) (hd : ‖d‖≤72/25)
    (hz : ‖z‖≤72/25) (v : ‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2+‖z‖^2≤17) :
    ‖powers i a b c d z‖ ≤ powerCap i := by
  have single (w : ℂ) (h : ‖w‖≤72/25) : ‖w^i‖≤‖w‖^2*(72/25:ℝ)^(i-2) := by
    rw [norm_pow,show i=2+(i-2) by omega,pow_add]
    simp only [Nat.add_sub_cancel_left]
    gcongr
  have tri : ‖powers i a b c d z‖≤‖a^i‖+‖b^i‖+‖c^i‖+‖d^i‖+‖z^i‖ := by
    unfold powers
    exact (norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)
  calc
    _ ≤ _ := tri
    _ ≤ _ := add_le_add (add_le_add (add_le_add (add_le_add (single _ ha) (single _ hb))
                (single _ hc)) (single _ hd)) (single _ hz)
    _ = (‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2+‖z‖^2)*(72/25:ℝ)^(i-2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right v (by positivity)

set_option maxHeartbeats 2000000 in
theorem centered_word0 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 4 [a,b,c,d] z=1 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]

set_option maxHeartbeats 2000000 in
theorem centered_word1 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 5 [a,b,c,d] z=0 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]

set_option maxHeartbeats 2000000 in
theorem centered_word2 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 6 [a,b,c,d] z=(powers 2 a b c d z)/2 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]
  ring

set_option maxHeartbeats 2000000 in
theorem centered_word3 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 7 [a,b,c,d] z=(powers 3 a b c d z)/3 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]
  ring

set_option maxHeartbeats 2000000 in
theorem centered_word4 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 8 [a,b,c,d] z=(powers 2 a b c d z)^2/8+(powers 4 a b c d z)/4 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]
  ring

set_option maxHeartbeats 2000000 in
theorem centered_word5 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 9 [a,b,c,d] z=(powers 2 a b c d z)*(powers 3 a b c d z)/6+(powers 5 a b c d z)/5 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]
  ring

set_option maxHeartbeats 2000000 in
theorem centered_word6 (a b c d z : ℂ) (hs : a+b+c+d+z=0) :
    word 10 [a,b,c,d] z=(powers 2 a b c d z)^3/48+(powers 2 a b c d z)*(powers 4 a b c d z)/8+(powers 3 a b c d z)^2/18+(powers 6 a b c d z)/6 := by
  obtain rfl : z=-(a+b+c+d) := by linear_combination hs
  norm_num [word,powers]
  ring

#print axioms powers_le
#print axioms centered_word6
end OrderedPartitions.ExpInterpolation
