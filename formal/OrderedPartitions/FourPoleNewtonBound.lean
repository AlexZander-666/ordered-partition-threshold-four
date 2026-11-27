import OrderedPartitions.FourPoleNewtonLow
noncomputable section
namespace OrderedPartitions.ExpInterpolation
open Complex Finset
private theorem factorial_tail (m : ℕ) :
    (72/25:ℝ)^(m+7)/((m+7).factorial:ℝ) ≤
    ((72/25:ℝ)^7/(7:ℕ).factorial)*(9/25:ℝ)^m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [show m+1+7=(m+7)+1 by omega,pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add_one]
    calc
      _ = ((72/25:ℝ)^(m+7)/((m+7).factorial:ℝ))*((72/25:ℝ)/((m+7:ℕ)+1:ℝ)) := by rw [div_mul_div_comm,mul_comm ((m+7).factorial:ℝ)]
      _ ≤ _ := mul_le_mul ih (show (72/25:ℝ)/((m+7:ℕ)+1:ℝ)≤9/25 by
                              apply (div_le_iff₀ (by positivity)).mpr
                              push_cast
                              linarith [Nat.cast_nonneg (α:=ℝ) m]) (by positivity) (by positivity)
      _ = _ := by rw [pow_succ];ring

private theorem tail11 (a b c d z : ℂ) (bd : ∀ u∈[a,b,c,d], ‖u‖≤72/25)
    (hz : ‖z‖≤72/25) :
    ‖∑' n : ℕ, word (n+11) [a,b,c,d] z /((n+11).factorial:ℂ)‖ ≤
      ((72/25:ℝ)^7/(7:ℕ).factorial/24)*(1-(9/25:ℝ))⁻¹ := by
  have hg := (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤9/25)
      (by norm_num : (9/25:ℝ)<1)).mul_left ((72/25:ℝ)^7/(7:ℕ).factorial/24)
  apply tsum_of_norm_bounded hg
  intro n
  have h := normalized_word_bound (n+7) [a,b,c,d] rfl z (72/25) (by norm_num) bd hz
  change 24*‖word (n+11) [a,b,c,d] z/((n+11).factorial:ℂ)‖ ≤ _ at h
  nlinarith only [h,factorial_tail n]

theorem centered_kernel_bound {a b c d z : ℂ} (distinct : [a,b,c,d].Nodup)
    (avoid : z∉[a,b,c,d]) (hs : a+b+c+d+z=0)
    (ha : ‖a‖≤72/25) (hb : ‖b‖≤72/25) (hc : ‖c‖≤72/25) (hd : ‖d‖≤72/25)
    (hz : ‖z‖≤72/25) (v : ‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2+‖z‖^2≤17) :
    3/50 ≤ 24*‖kernel [a,b,c,d] z 1‖ := by
  let f := fun n : ℕ ↦ word n [a,b,c,d] z/(n.factorial:ℂ)
  have sums : HasSum f (kernel [a,b,c,d] z 1) := kernel_series _ distinct _ avoid
  have eqn := sums.summable.sum_add_tsum_nat_add 11
  rw [sums.tsum_eq] at eqn
  have bd : ∀ u∈[a,b,c,d], ‖u‖≤72/25 := by
    intro u hu
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl <;> assumption
  have tail := tail11 a b c d z bd hz
  change ‖∑' n : ℕ, f (n+11)‖ ≤ _ at tail
  have p2 := powers_le 2 (by decide) ha hb hc hd hz v
  have p3 := powers_le 3 (by decide) ha hb hc hd hz v
  have p4 := powers_le 4 (by decide) ha hb hc hd hz v
  have p5 := powers_le 5 (by decide) ha hb hc hd hz v
  have p6 := powers_le 6 (by decide) ha hb hc hd hz v
  have pc2 : 0≤powerCap 2 := (norm_nonneg _).trans p2
  have b2 : ‖f 6‖ ≤ ((powerCap 2)/2)/(6:ℕ).factorial := by
    dsimp only [f];rw [centered_word2 a b c d z hs,norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    all_goals simp only [norm_div,Complex.norm_ofNat]
    all_goals gcongr
  have b3 : ‖f 7‖ ≤ ((powerCap 3)/3)/(7:ℕ).factorial := by
    dsimp only [f];rw [centered_word3 a b c d z hs,norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    all_goals simp only [norm_div,Complex.norm_ofNat]
    all_goals gcongr
  have b4 : ‖f 8‖ ≤ ((powerCap 2)^2/8+(powerCap 4)/4)/(8:ℕ).factorial := by
    dsimp only [f];rw [centered_word4 a b c d z hs,norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (norm_add_le _ _).trans
    apply add_le_add
    all_goals simp only [norm_pow,norm_div,Complex.norm_ofNat]
    all_goals gcongr
  have b5 : ‖f 9‖ ≤ ((powerCap 2)*(powerCap 3)/6+(powerCap 5)/5)/(9:ℕ).factorial := by
    dsimp only [f];rw [centered_word5 a b c d z hs,norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (norm_add_le _ _).trans
    apply add_le_add
    all_goals simp only [norm_mul,norm_div,Complex.norm_ofNat]
    all_goals gcongr
  have b6 : ‖f 10‖ ≤ ((powerCap 2)^3/48+(powerCap 2)*(powerCap 4)/8+(powerCap 3)^2/18+(powerCap 6)/6)/(10:ℕ).factorial := by
    dsimp only [f];rw [centered_word6 a b c d z hs,norm_div,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)) ?_)
    · rw [norm_div,norm_pow,Complex.norm_ofNat];gcongr
    · rw [norm_div,norm_mul,Complex.norm_ofNat];gcongr
    · rw [norm_div,norm_pow,Complex.norm_ofNat];gcongr
    · rw [norm_div,Complex.norm_ofNat];gcongr
  have finite : ∑ n∈range 11, f n =
      1/24+f 6+f 7+f 8+f 9+f 10 := by
    norm_num [sum_range_succ,f,show word 4 [a,b,c,d] z=1 from centered_word0 _ _ _ _ _ hs,
      show word 5 [a,b,c,d] z=0 from centered_word1 _ _ _ _ _ hs,word,Nat.factorial]
    linear_combination hs
  rw [finite] at eqn
  let t := ∑' n : ℕ, f (n+11)
  change 1/24+f 6+f 7+f 8+f 9+f 10+t=kernel _ z 1 at eqn
  have tri : ‖(1/24:ℂ)‖≤‖kernel [a,b,c,d] z 1‖ + ‖t‖ + ‖f 10‖+‖f 9‖+‖f 8‖+‖f 7‖+‖f 6‖ := by
    rw [show (1/24:ℂ)= kernel [a,b,c,d] z 1-t-f 10-f 9-f 8-f 7-f 6 by linear_combination eqn]
    exact ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl))
  norm_num [powerCap,Nat.factorial,Complex.norm_ofNat] at b2 b3 b4 b5 b6 tail tri ⊢
  change ‖t‖≤_ at tail
  linarith

#print axioms centered_kernel_bound
end OrderedPartitions.ExpInterpolation
