import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A circle bound for the exponential function near its positive real crossing of 2. -/

noncomputable section

namespace OrderedPartitions.CriticalEdgeCircle

open Real Finset

private theorem exp_sub_one_le_chord {t b : ℝ} (hb : 0 < b) (ht : 0 ≤ t) (hle : t ≤ b) :
    exp t - 1 ≤ (t / b) * (exp b - 1) := by
  have h₀ : 0 ≤ t / b := div_nonneg ht hb.le
  have h₁ : 0 ≤ 1 - t / b := sub_nonneg.mpr ((div_le_one hb).mpr hle)
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ b) h₁ h₀
    (show 1 - t / b + t / b = 1 by ring)
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_zero, zero_add, div_mul_cancel₀ _ hb.ne',
    exp_zero] at h
  linarith

private theorem exp_one_le_upper : exp 1 ≤ 68 / 25 :=
  exp_one_lt_d9.le.trans (by norm_num)

private theorem exp_half_le_upper : exp (1 / 2) ≤ 33 / 20 := by
  have hs : exp (1 / 2) ^ 2 = exp 1 := by
    rw [sq, ← exp_add]
    norm_num
  nlinarith [exp_pos (1 / 2), exp_one_le_upper]

private theorem cos_gap {v : ℝ} (hv : |v| ≤ 1) : (43 / 96 : ℝ) * v ^ 2 ≤ 1 - cos v := by
  have p : |v| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) hv
  have q : |v| ^ 4 ≤ v ^ 2 := calc
    _ = |v| ^ 2 * |v| ^ 2 := by ring
    _ ≤ 1 * |v| ^ 2 := mul_le_mul_of_nonneg_right p (sq_nonneg |v|)
    _ = _ := by rw [one_mul, sq_abs]
  nlinarith [(abs_le.mp (cos_bound hv)).2]

private theorem norm_sub_exp_sq (z : ℂ) :
    ‖(2 : ℂ) - Complex.exp z‖ ^ 2 =
      4 + exp z.re ^ 2 - 4 * exp z.re * cos z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num only [Complex.sub_re, Complex.sub_im, Complex.re_ofNat, Complex.im_ofNat,
    Complex.exp_re, Complex.exp_im]
  have h := congrArg (fun y : ℝ ↦ exp z.re ^ 2 * y) (sin_sq_add_cos_sq z.im)
  linear_combination h

private theorem weighted_defect_lt {x u : ℝ} (hx : log 2 ≤ x) (hx₁ : x ≤ 1)
    (hu : 0 ≤ u) (hux : u < x) :
    (exp (x - u) - 1) * (exp x + exp u - 4) < (43 / 24 : ℝ) * (x + u) * (x - u) := by
  have hd : 0 < x - u := sub_pos.mpr hux
  have hdl : 0 ≤ exp (x - u) - 1 := sub_nonneg.mpr (one_le_exp hd.le)
  have hxlo : (69 / 100 : ℝ) ≤ x := (le_trans (by norm_num) log_two_gt_d9.le).trans hx
  have hxe : exp x ≤ 68 / 25 := (exp_le_exp.mpr hx₁).trans exp_one_le_upper
  by_cases hlo : u ≤ (11 / 20 : ℝ) * x
  · have hdu := exp_sub_one_le_chord zero_lt_one hd.le (by linarith : x - u ≤ 1)
    have hue := exp_sub_one_le_chord zero_lt_one hu (hux.le.trans hx₁)
    simp only [div_one] at hdu hue
    have cap : exp x + exp u - 4 ≤ 2 / 3 := by
      have hprod := mul_le_mul_of_nonneg_left exp_one_le_upper hu
      nlinarith
    have hd' : exp (x - u) - 1 ≤ (43 / 25 : ℝ) * (x - u) := by
      have hprod := mul_le_mul_of_nonneg_left exp_one_le_upper hd.le
      nlinarith
    calc
      _ ≤ (exp (x - u) - 1) * (2 / 3) := mul_le_mul_of_nonneg_left cap hdl
      _ ≤ ((43 / 25 : ℝ) * (x - u)) * (2 / 3) :=
        mul_le_mul_of_nonneg_right hd' (by norm_num)
      _ = (86 / 75 : ℝ) * (x - u) := by ring
      _ < _ := mul_lt_mul_of_pos_right (by nlinarith) hd
  · have hhi : (11 / 20 : ℝ) * x < u := lt_of_not_ge hlo
    have hdu := exp_sub_one_le_chord (show (0 : ℝ) < 1 / 2 by norm_num) hd.le
      (by linarith : x - u ≤ 1 / 2)
    have cap : exp x + exp u - 4 ≤ 36 / 25 := by
      linarith [(exp_le_exp.mpr hux.le).trans hxe]
    have hd' : exp (x - u) - 1 ≤ (13 / 10 : ℝ) * (x - u) := by
      have hprod := mul_le_mul_of_nonneg_left exp_half_le_upper hd.le
      nlinarith
    calc
      _ ≤ (exp (x - u) - 1) * (36 / 25) := mul_le_mul_of_nonneg_left cap hdl
      _ ≤ ((13 / 10 : ℝ) * (x - u)) * (36 / 25) :=
        mul_le_mul_of_nonneg_right hd' (by norm_num)
      _ = (234 / 125 : ℝ) * (x - u) := by ring
      _ < _ := mul_lt_mul_of_pos_right (by nlinarith) hd

/-- Off the positive real point of the circle, the exponential distance from 2 is
strictly greater than its value there. -/
theorem norm_sub_exp_circle_strict {x : ℝ} (hx : log 2 ≤ x) (hx₁ : x ≤ 1)
    {z : ℂ} (hz : ‖z‖ = x) (hne : z ≠ (x : ℂ)) :
    exp x - 2 < ‖(2 : ℂ) - Complex.exp z‖ := by
  have hxexp : 2 ≤ exp x := by
    rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact exp_le_exp.mpr hx
  have hu : z.re < x := by
    refine lt_of_le_of_ne ((Complex.re_le_norm z).trans_eq hz) fun hr ↦ ?_
    have hv := Complex.sq_norm_sub_sq_re z
    rw [hz, hr, sub_self] at hv
    have hi : z.im = 0 := by nlinarith
    exact hne (Complex.ext (by simpa using hr) (by simpa using hi))
  have hd : (exp x - exp z.re) * (exp x + exp z.re - 4) <
      4 * exp z.re * (1 - cos z.im) := by
    by_cases h₀ : z.re ≤ 0
    · have h₁ : exp z.re ≤ 1 := (exp_le_exp.mpr h₀).trans_eq exp_zero
      have h₂ : exp x < 3 := (exp_le_exp.mpr hx₁).trans_lt exp_one_lt_three
      exact (mul_neg_of_pos_of_neg (sub_pos.mpr (exp_lt_exp.mpr hu)) (by linarith)).trans_le
        (mul_nonneg (by positivity) (sub_nonneg.mpr (cos_le_one _)))
    · have hexp : exp x - exp z.re = exp z.re * (exp (x - z.re) - 1) := by
        rw [mul_sub, mul_one, ← exp_add]
        ring_nf
      have hs := Complex.sq_norm_sub_sq_re z
      rw [hz] at hs
      have hs' : z.im ^ 2 = (x + z.re) * (x - z.re) := by nlinarith
      have hc := cos_gap ((Complex.abs_im_le_norm z).trans (hz.trans_le hx₁))
      calc
        _ = exp z.re * ((exp (x - z.re) - 1) * (exp x + exp z.re - 4)) := by
          rw [hexp, mul_assoc]
        _ < exp z.re * ((43 / 24 : ℝ) * (x + z.re) * (x - z.re)) :=
          mul_lt_mul_of_pos_left (weighted_defect_lt hx hx₁ (le_of_lt (lt_of_not_ge h₀)) hu)
            (exp_pos _)
        _ = (4 * exp z.re) * ((43 / 96 : ℝ) * z.im ^ 2) := by rw [hs']; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity)
  apply (sq_lt_sq₀ (sub_nonneg.mpr hxexp) (norm_nonneg _)).mp
  rw [norm_sub_exp_sq]
  nlinarith only [hd]

/-- On a circle of radius between `log 2` and 1, the distance from `exp z` to 2
is minimized at the positive real point. -/
theorem norm_sub_exp_circle {x : ℝ} (hx : log 2 ≤ x) (hx₁ : x ≤ 1)
    {z : ℂ} (hz : ‖z‖ = x) :
    exp x - 2 ≤ ‖(2 : ℂ) - Complex.exp z‖ := by
  by_cases heq : z = (x : ℂ)
  · subst z
    have hxexp : 2 ≤ exp x := by
      rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
      exact exp_le_exp.mpr hx
    have he : (2 : ℂ) - Complex.exp (x : ℂ) = ((2 - exp x : ℝ) : ℂ) := by
      simp [Complex.ofReal_exp]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hxexp)]
    ring_nf
    exact le_rfl
  · exact (norm_sub_exp_circle_strict hx hx₁ hz heq).le

/-- The exponential generating function of one labelled block of size at least `j`. -/
def tailComplex (j : ℕ) (z : ℂ) : ℂ :=
  Complex.exp z - ∑ n ∈ range j, z ^ n / (n.factorial : ℂ)

/-- The real restriction uses the same exponential truncation as the scalar critical point. -/
theorem tailComplex_ofReal (j : ℕ) (x : ℝ) :
    tailComplex j (x : ℂ) = ((exp x - ∑ n ∈ range j, x ^ n / (n.factorial : ℝ) : ℝ) : ℂ) := by
  push_cast
  simp [tailComplex]

private theorem hasSum_tailComplex (j : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ ↦ z ^ (n + j) / ((n + j).factorial : ℂ)) (tailComplex j z) := by
  apply (hasSum_nat_add_iff (f := fun n : ℕ ↦ z ^ n / (n.factorial : ℂ)) j).mpr
  have h := NormedSpace.expSeries_div_hasSum_exp z
  rw [← Complex.exp_eq_exp_ℂ] at h
  simpa only [tailComplex, sub_add_cancel] using h

/-- On a circle the positive real value bounds the modulus of the large-block tail. -/
theorem norm_tailComplex_le (j : ℕ) (z : ℂ) :
    ‖tailComplex j z‖ ≤ exp ‖z‖ - ∑ n ∈ range j, ‖z‖ ^ n / (n.factorial : ℝ) := by
  let x := ‖z‖
  have h := NormedSpace.expSeries_div_hasSum_exp x
  rw [← Real.exp_eq_exp_ℝ] at h
  have hr : HasSum (fun n : ℕ ↦ x ^ (n + j) / ((n + j).factorial : ℝ))
      (exp x - ∑ n ∈ range j, x ^ n / (n.factorial : ℝ)) := by
    apply (hasSum_nat_add_iff (f := fun n : ℕ ↦ x ^ n / (n.factorial : ℝ)) j).mpr
    simpa only [sub_add_cancel] using h
  exact (hasSum_tailComplex j z).norm_le_of_bounded hr fun n ↦ by
    rw [norm_div, norm_pow]
    simp [x]

/-- The denominator of the labelled ordered-block generating function in `s = 1 - t`. -/
def denominator (j : ℕ) (s z : ℂ) : ℂ := (2 : ℂ) - Complex.exp z + s * tailComplex j z

/-- A critical real value gives strict Rouché domination at every point on its circle except
possibly the positive real point at the endpoint of the parameter disk. -/
theorem boundary_dominance {j : ℕ} {a C : ℝ} {s z : ℂ} (ha : log 2 < a) (ha₁ : a ≤ 1)
    (hz : ‖z‖ = a) (hC : C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = exp a - 2)
    (hs : ‖s‖ ≤ C) (strict : ‖s‖ < C ∨ z ≠ (a : ℂ)) :
    ‖s * tailComplex j z‖ < ‖(2 : ℂ) - Complex.exp z‖ := by
  have he : 0 < exp a - 2 := by
    apply sub_pos.mpr
    rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact exp_lt_exp.mpr ha
  have ht := norm_tailComplex_le j z
  rw [hz] at ht
  have htp : 0 < exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ) := by
    by_contra! hh
    have hneg := mul_nonpos_of_nonneg_of_nonpos ((norm_nonneg s).trans hs) hh
    linarith
  rw [norm_mul]
  rcases strict with hl | hn
  · calc
      _ ≤ ‖s‖ * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left ht (norm_nonneg s)
      _ < C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) :=
        mul_lt_mul_of_pos_right hl htp
      _ = exp a - 2 := hC
      _ ≤ _ := norm_sub_exp_circle ha.le ha₁ hz
  · calc
      _ ≤ C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) :=
        mul_le_mul hs ht (norm_nonneg _) ((norm_nonneg s).trans hs)
      _ = exp a - 2 := hC
      _ < _ := norm_sub_exp_circle_strict ha.le ha₁ hz hn

theorem denominator_ne_zero_on_circle {j : ℕ} {a C : ℝ} {s z : ℂ}
    (ha : log 2 < a) (ha₁ : a ≤ 1) (hz : ‖z‖ = a)
    (hC : C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = exp a - 2)
    (hs : ‖s‖ ≤ C) (strict : ‖s‖ < C ∨ z ≠ (a : ℂ)) : denominator j s z ≠ 0 := by
  intro h
  have he : (2 : ℂ) - Complex.exp z = -(s * tailComplex j z) := eq_neg_of_add_eq_zero_left h
  have hd := boundary_dominance ha ha₁ hz hC hs strict
  exact (lt_irrefl _) (by simpa only [he, norm_neg] using hd)

/-- A uniform positive lower bound on the full contour for any smaller parameter disk. -/
theorem norm_denominator_lower_on_circle {j : ℕ} {a C : ℝ} {s z : ℂ}
    (ha : log 2 ≤ a) (ha₁ : a ≤ 1) (hz : ‖z‖ = a)
    (hC : C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = exp a - 2) :
    (C - ‖s‖) * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) ≤
      ‖denominator j s z‖ := by
  have hb := norm_tailComplex_le j z
  rw [hz] at hb
  have ht := mul_le_mul_of_nonneg_left hb (norm_nonneg s)
  have he := norm_sub_exp_circle ha ha₁ hz
  have htri := norm_sub_norm_le ((2 : ℂ) - Complex.exp z) (-(s * tailComplex j z))
  rw [norm_neg, norm_mul, sub_neg_eq_add, ← denominator] at htri
  linarith only [hC, ht, he, htri]

/-- The only possible zero on the critical circle and in the closed parameter disk is
the positive real tangency point at the positive real parameter. -/
theorem denominator_zero_on_circle_iff {j : ℕ} {a C : ℝ} {s z : ℂ}
    (ha : log 2 < a) (ha₁ : a ≤ 1) (hz : ‖z‖ = a)
    (hC : C * (exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)) = exp a - 2)
    (hs : ‖s‖ ≤ C) : denominator j s z = 0 ↔ z = (a : ℂ) ∧ s = (C : ℂ) := by
  have he : 0 < exp a - 2 := by
    apply sub_pos.mpr
    rw [← exp_log (show (0 : ℝ) < 2 by norm_num)]
    exact exp_lt_exp.mpr ha
  let b := exp a - ∑ n ∈ range j, a ^ n / (n.factorial : ℝ)
  have hb : b ≠ 0 := by
    intro h
    change C * b = exp a - 2 at hC
    rw [h, mul_zero] at hC
    exact he.ne' hC.symm
  have h₁ : denominator j s (a : ℂ) = (s - (C : ℂ)) * (b : ℂ) := by
    have hC' : C * b = exp a - 2 := hC
    have hcast : (C : ℂ) * (b : ℂ) = (exp a : ℂ) - 2 := by exact_mod_cast hC'
    unfold denominator
    rw [tailComplex_ofReal, ← Complex.ofReal_exp]
    change (2 : ℂ) - (exp a : ℂ) + s * (b : ℂ) = _
    linear_combination hcast
  constructor
  · intro h
    have hz' : z = (a : ℂ) := by
      by_contra hn
      exact denominator_ne_zero_on_circle ha ha₁ hz hC hs (.inr hn) h
    refine ⟨hz', ?_⟩
    rw [hz', h₁] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (by exact_mod_cast hb))
  · rintro ⟨rfl, rfl⟩
    simp [h₁]

#print axioms norm_sub_exp_circle_strict
#print axioms norm_sub_exp_circle
#print axioms tailComplex_ofReal
#print axioms norm_tailComplex_le
#print axioms boundary_dominance
#print axioms denominator_ne_zero_on_circle
#print axioms norm_denominator_lower_on_circle
#print axioms denominator_zero_on_circle_iff

end OrderedPartitions.CriticalEdgeCircle
