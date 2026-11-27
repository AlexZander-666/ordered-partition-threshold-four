import OrderedPartitions.FiniteSimplePoles
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Cauchy coefficients in the presence of one simple pole strictly inside a circle. -/

noncomputable section

namespace OrderedPartitions.CriticalEdge

open Complex Metric Set Filter
open scoped Topology

/-- The outer circle integral for the Taylor coefficient of a reciprocal. -/
def circleRemainder (g : ℂ → ℂ) (a : ℝ) (n : ℕ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(0, a), (z ^ (n + 1) * g z)⁻¹

private theorem norm_of_sphere {a : ℝ} {z : ℂ} (hz : z ∈ sphere (0 : ℂ) a) : ‖z‖ = a := by
  simpa only [mem_sphere, dist_zero_right] using hz

private theorem off_center {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : z ∈ sphere (0 : ℂ) a) : z ≠ 0 :=
  norm_pos_iff.mp ((norm_of_sphere hz).symm ▸ ha)

private theorem off_pole {a : ℝ} {p z : ℂ} (hp : ‖p‖ < a) (hz : z ∈ sphere (0 : ℂ) a) : z ≠ p :=
  fun h ↦ hp.ne (h ▸ norm_of_sphere hz)

private def poleKernel (p : ℂ) (n : ℕ) (z : ℂ) : ℂ := (z ^ (n + 1))⁻¹ * (z - p)⁻¹

private theorem invPow_integrable {a : ℝ} (ha : 0 < a) (m : ℕ) :
    CircleIntegrable (fun z : ℂ ↦ (z ^ m)⁻¹) 0 a :=
  ((continuousOn_id.pow m).inv₀ (fun _ hz ↦ pow_ne_zero _ (off_center ha hz))).circleIntegrable ha.le

private theorem subInv_integrable {a : ℝ} {p : ℂ} (ha : 0 < a) (hp : ‖p‖ < a) :
    CircleIntegrable (fun z : ℂ ↦ (z - p)⁻¹) 0 a :=
  ((continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz ↦
    sub_ne_zero.mpr (off_pole hp hz))).circleIntegrable ha.le

private theorem poleKernel_integrable {a : ℝ} {p : ℂ} (ha : 0 < a) (hp : ‖p‖ < a) (n : ℕ) :
    CircleIntegrable (poleKernel p n) 0 a :=
  (((continuousOn_id.pow _).inv₀ (fun _ hz ↦ pow_ne_zero _ (off_center ha hz))).mul
    ((continuousOn_id.sub continuousOn_const).inv₀ (fun _ hz ↦
      sub_ne_zero.mpr (off_pole hp hz)))).circleIntegrable ha.le

private theorem circle_poleKernel_zero {a : ℝ} {p : ℂ} (ha : 0 < a) (hp : ‖p‖ < a) (hp0 : p ≠ 0)
    (n : ℕ) : (∮ z in C(0, a), poleKernel p n z) = 0 := by
  induction n with
  | zero =>
    have inside : p ∈ ball (0 : ℂ) a := by simpa only [mem_ball, dist_zero_right] using hp
    calc
      _ = ∮ z in C(0, a), p⁻¹ * ((z - p)⁻¹ - z⁻¹) := by
        apply circleIntegral.integral_congr ha.le
        intro z hz
        simp only [poleKernel, zero_add, pow_one]
        field_simp [hp0, off_center ha hz, sub_ne_zero.mpr (off_pole hp hz)]
        ring
      _ = 0 := by
        rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub
          (subInv_integrable ha hp) (by simpa only [pow_one] using invPow_integrable ha 1),
          circleIntegral.integral_sub_inv_of_mem_ball inside]
        have base := circleIntegral.integral_sub_center_inv (0 : ℂ) ha.ne'
        simp only [sub_zero] at base
        rw [base, sub_self, mul_zero]
  | succ n ih =>
    calc
      _ = ∮ z in C(0, a), p⁻¹ * (poleKernel p n z - (z ^ (n + 1 + 1))⁻¹) := by
        apply circleIntegral.integral_congr ha.le
        intro z hz
        simp only [poleKernel, pow_succ _ (n + 1)]
        field_simp [hp0, off_center ha hz, sub_ne_zero.mpr (off_pole hp hz)]
        ring
      _ = 0 := by
        have base := circleIntegral.integral_sub_zpow_of_ne
          (n := -((n + 1 + 1 : ℕ) : ℤ)) (by omega) (0 : ℂ) (0 : ℂ) a
        simp only [sub_zero, zpow_neg, zpow_natCast] at base
        rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub
          (poleKernel_integrable ha hp n) (invPow_integrable ha (n + 1 + 1)), ih, base,
          sub_zero, mul_zero]

private theorem pole_series {p A : ℂ} (pn : p ≠ 0) :
    HasFPowerSeriesAt (fun z : ℂ ↦ A * (z - p)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun m ↦ -A / p ^ (m + 1)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [ball_mem_nhds (0 : ℂ) (norm_pos_iff.mpr pn)] with z hz
  have lt : ‖z‖ < ‖p‖ := by simpa only [mem_ball, dist_zero_right] using hz
  have zp : z - p ≠ 0 := sub_ne_zero.mpr (fun e ↦ lt.ne (congrArg norm e))
  have small : ‖z / p‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.mpr pn)]; exact lt
  convert! (hasSum_geometric_of_norm_lt_one small).mul_left (-A / p) using 1
  · ext m
    rw [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, div_pow, pow_succ]
    field_simp
  · rw [zero_add, show 1 - z / p = -(z - p) / p by field_simp; ring]
    field_simp

/-- The Taylor coefficient is the outer circle integral minus the contribution of the pole. -/
theorem coefficient_one_pole {g : ℂ → ℂ} (hg : Differentiable ℂ g) {a : ℝ} (ha : 0 < a) {p : ℂ}
    (hp : ‖p‖ < a) (hp0 : p ≠ 0) (gp : g p = 0) (gp' : deriv g p ≠ 0)
    (uniq : ∀ w : ℂ, ‖w‖ ≤ a → g w = 0 → w = p) (n : ℕ) :
    iteratedDeriv n (fun z ↦ (g z)⁻¹) 0 / (n.factorial : ℂ) =
      circleRemainder g a n - (deriv g p)⁻¹ / p ^ (n + 1) := by
  classical
  let U := ball (0 : ℂ) a ∪ {w : ℂ | g w ≠ 0}
  have openU : IsOpen U := isOpen_ball.union (isOpen_ne_fun hg.continuous continuous_const)
  have hclosed : closedBall (0 : ℂ) a ⊆ U := by
    intro w hw
    have hw' : ‖w‖ ≤ a := by simpa only [mem_closedBall, dist_zero_right] using hw
    by_cases h : g w = 0
    · have wi := uniq w hw' h
      exact Or.inl (by simpa only [wi, mem_ball, dist_zero_right] using hp)
    · exact Or.inr h
  obtain ⟨H, hH, hsplit⟩ := FiniteSimplePoles.remove hg openU {p}
    (by simpa using gp) (by simpa using gp') (fun z hz e ↦ by
      have hball : z ∈ ball (0 : ℂ) a := hz.resolve_right (fun hn ↦ hn e)
      have hnorm : ‖z‖ ≤ a := by simpa only [mem_ball, dist_zero_right] using (mem_ball.mp hball).le
      have h := uniq z hnorm e
      simpa using h)
  let A := (deriv g p)⁻¹
  let F := fun z : ℂ ↦ (g z)⁻¹
  have split (z : ℂ) (h : z ≠ p) : F z = H z + A * (z - p)⁻¹ := by
    simpa only [F, A, Finset.sum_singleton, FiniteSimplePoles.term] using hsplit z (by simpa using h)
  have near : ∀ᶠ w : ℂ in 𝓝 0, w ≠ p := isOpen_ne.mem_nhds hp0.symm
  have he : (fun z : ℂ ↦ H z + A * (z - p)⁻¹) =ᶠ[𝓝 0] F :=
    near.mono fun w hw ↦ (split w hw).symm
  let R : NNReal := ⟨a, ha.le⟩
  have hPs := ((hH.mono hclosed).hasFPowerSeriesOnBall (R := R) ha).hasFPowerSeriesAt
  have hF := (hPs.add (pole_series (A := A) hp0)).congr he
  have coeff := congrArg (fun q : FormalMultilinearSeries ℂ ℂ ℂ ↦ q.coeff n)
    (hF.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries hF)
  change (FormalMultilinearSeries.ofScalars ℂ
    (fun m ↦ iteratedDeriv m F 0 / (m.factorial : ℂ))).coeff n =
      (cauchyPowerSeries H 0 a).coeff n +
      (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ -A / p ^ (m + 1))).coeff n at coeff
  simp only [FormalMultilinearSeries.coeff_ofScalars] at coeff
  have hcoeff : (cauchyPowerSeries H 0 a).coeff n =
      (2 * (Real.pi : ℂ) * I)⁻¹ • ∮ z in C(0, a), (z ^ (n + 1))⁻¹ * H z := by
    change (cauchyPowerSeries H 0 a n) (fun _ ↦ (1 : ℂ)) = _
    rw [cauchyPowerSeries_apply]
    simp only [sub_zero, one_div, smul_eq_mul, ← mul_assoc, ← pow_succ, ← inv_pow]
  let f := fun z : ℂ ↦ (z ^ (n + 1))⁻¹ * H z
  have fint : CircleIntegrable f 0 a :=
    (((continuousOn_id.pow _).inv₀ (fun _ hz ↦ pow_ne_zero _ (off_center ha hz))).mul
      (hH.continuousOn.mono (sphere_subset_closedBall.trans hclosed))).circleIntegrable ha.le
  have pint : CircleIntegrable (fun z ↦ A * poleKernel p n z) 0 a :=
    (poleKernel_integrable ha hp n).const_mul _
  have heq : (∮ z in C(0, a), (z ^ (n + 1) * g z)⁻¹) = ∮ z in C(0, a), f z := by
    calc
      _ = ∮ z in C(0, a), f z + A * poleKernel p n z := by
        apply circleIntegral.integral_congr ha.le
        intro z hz
        change (z ^ (n + 1) * g z)⁻¹ = f z + A * poleKernel p n z
        rw [mul_inv_rev, show (g z)⁻¹ = _ from split z (off_pole hp hz)]
        dsimp only [f, poleKernel]
        ring
      _ = _ := by
        rw [circleIntegral.integral_add fint pint, circleIntegral.integral_const_mul,
          circle_poleKernel_zero ha hp hp0 n, mul_zero, add_zero]
  rw [hcoeff, ← heq, ← circleRemainder, neg_div] at coeff
  simpa only [F, A, sub_eq_add_neg] using coeff

/-- A pointwise lower bound for the denominator on the circle gives an explicit tail bound. -/
theorem norm_circleRemainder_le {g : ℂ → ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (lower : ∀ z : ℂ, ‖z‖ = a → b ≤ ‖g z‖) (n : ℕ) :
    ‖circleRemainder g a n‖ ≤ 1 / (b * a ^ n) := by
  have hh : ‖circleRemainder g a n‖ ≤ a * (a ^ (n + 1) * b)⁻¹ := by
    unfold circleRemainder
    apply circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const ha.le
    intro z hz
    rw [norm_inv, norm_mul, norm_pow, norm_of_sphere hz]
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (lower z (norm_of_sphere hz)) (by positivity))
  convert hh using 1
  rw [pow_succ]
  field_simp [ha.ne', hb.ne']

#print axioms coefficient_one_pole
#print axioms norm_circleRemainder_le

end OrderedPartitions.CriticalEdge
