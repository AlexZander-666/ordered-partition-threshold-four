import OrderedPartitions.FourPoleFunction
import OrderedPartitions.CriticalEdgeActivity

/-! Exact degree and Taylor normalization for the fourth-threshold pole equation. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex Polynomial Finset

theorem G_eq_poleDen (q : ℝ) (z : ℂ) : G q z=CriticalEdge.poleDen 4 (q:ℂ) z := by
  unfold G CriticalEdge.poleDen
  norm_num [Finset.sum_range_succ,Nat.factorial]
  ring

theorem iteratedDeriv_inv_G_at_zero {q : ℝ} (hq : q<1) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ ↦ (G q z)⁻¹) 0 / (n.factorial:ℂ) =
      Complex.ofReal ((row n 4).eval (-q/(1-q))) / ((1-(q:ℂ))*(n.factorial:ℂ)) := by
  simp only [G_eq_poleDen]
  rw [CriticalEdge.poleDen_coeff (by decide) (by exact_mod_cast hq.ne)]
  congr 1
  have h := Polynomial.eval₂_hom (p:=row n 4) Complex.ofRealHom (-q/(1-q))
  simpa using h
private theorem top_count_positive (n : ℕ) : 0 < count n 4 (n/4) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases low : n < 4
    · rw [Nat.div_eq_of_lt low]
      exact count_zero_positive n (by decide)
    · have two : 4 ≤ n := by omega
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have index : (k+1)/4 - 1 = (k+1-4)/4 := by omega
      have dr : (k+1)/4 ≠ 0 := by omega
      have prev := ih (k+1-4) (by omega)
      rw [count_recurrence k (by decide)]
      apply lt_of_lt_of_le _ (single_le_sum (f := fun r ↦ (k+1).choose r *
        (if 4 ≤ r then (if (k+1)/4 = 0 then 0 else count (k+1-r) 4 ((k+1)/4-1))
          else count (k+1-r) 4 ((k+1)/4))) (fun _ _ ↦ Nat.zero_le _)
        (mem_Icc.mpr (by omega : 1 ≤ 4 ∧ 4 ≤ k+1)))
      simpa only [le_rfl, if_true, if_neg dr, index] using
        Nat.mul_pos (Nat.choose_pos two) prev

/-- Exact degree and positive leading and constant terms for every true row
with threshold four, including the constant ranks. -/
theorem original_shape (n : ℕ) :
    (row n 4).natDegree = n/4 ∧ 0 < (row n 4).leadingCoeff ∧ 0 < (row n 4).eval 0 := by
  have top : 0 < (row n 4).coeff (n/4) := by
    rw [coeff_row (by decide)]
    exact_mod_cast top_count_positive n
  have degree : (row n 4).natDegree = n/4 := by
    apply natDegree_eq_of_le_of_coeff_ne_zero _ top.ne'
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    rw [coeff_row (by decide), count_above_degree (by decide) (by omega), Nat.cast_zero]
  refine ⟨degree, by rwa [leadingCoeff, degree], ?_⟩
  rw [← coeff_zero_eq_eval_zero, coeff_row (by decide)]
  exact_mod_cast count_zero_positive n (by decide : 2≤4)


#print axioms G_eq_poleDen
#print axioms iteratedDeriv_inv_G_at_zero
#print axioms original_shape
end OrderedPartitions.FourPole
