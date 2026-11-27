import OrderedPartitions.FourPoleCornerLimits
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! Derivative of a selected quartic branch, using only its scaled zero equation. -/
namespace OrderedPartitions.FourPole
open Filter Topology Complex

/-- No smooth selection of the zeros is required. The Laurent coordinate w=z/epsilon
satisfies 1+w^4+epsilon*(w^5/5-w)+error=0 and error/epsilon tends to zero. -/
theorem root_velocity {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w err : ι→ℂ} {ω : ℂ}
    (root : ω^4 = -1) (W : Tendsto w l (𝓝 ω)) (nz : ∀ᶠ i in l, e i ≠ 0)
    (small : Tendsto (fun i ↦ err i/(e i:ℂ)) l (𝓝 0))
    (zero : ∀ᶠ i in l, 1+(w i)^4+(e i:ℂ)*(w i^5/5-w i)+err i=0) :
    Tendsto (fun i ↦ (w i-ω)/(e i:ℂ)) l (𝓝 (-(3/10)*ω^2)) := by
  have ωne : ω ≠ 0 := by intro h; simp [h] at root
  let f (v : ℂ) := v^3+v^2*ω+v*ω^2+ω^3
  have F : Tendsto (fun i ↦ f (w i)) l (𝓝 (4*ω^3)) := by
    have eq : f ω = 4*ω^3 := by dsimp [f]; ring
    rw [← eq]
    exact (show Continuous f by unfold f; fun_prop).continuousAt.tendsto.comp W
  have denom : 4*ω^3 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ ωne)
  have h := (((W.pow 5).div_const (5:ℂ) |>.sub W).neg.sub small).div F denom
  have endval : (-(ω^5/5-ω)-0)/(4*ω^3) = -(3/10)*ω^2 := by
    field_simp [ωne]
    linear_combination (50*ω)*root
  rw [endval] at h
  refine h.congr' ?_
  filter_upwards [nz,zero,F.eventually_ne denom] with i ei zi fi
  have ec : (e i:ℂ) ≠ 0 := by exact_mod_cast ei
  change (-(w i^5/5-w i)-err i/(e i:ℂ))/f (w i)=(w i-ω)/(e i:ℂ)
  apply (div_eq_div_iff fi ec).2
  rw [sub_mul,div_mul_cancel₀ _ ec]
  dsimp [f]
  linear_combination -zi + root

/-- An explicit conversion from scaled complex motion to angle and logarithmic
radius. The potential logarithmic cut is kept as an explicit hypothesis. -/
theorem polar_velocity {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w : ι→ℂ} {ω u : ℂ}
    (W : Tendsto w l (𝓝 ω)) (regular : ω ∈ Complex.slitPlane)
    (slope : Tendsto (fun i ↦ (w i-ω)/(e i:ℂ)) l (𝓝 u)) :
    Tendsto (fun i ↦ (Complex.arg (w i)-Complex.arg ω)/e i) l (𝓝 (ω⁻¹*u).im) ∧
    Tendsto (fun i ↦ (Real.log ‖w i‖-Real.log ‖ω‖)/e i) l (𝓝 (ω⁻¹*u).re) := by
  have der := Complex.hasDerivAt_log regular
  have ds := ((continuousAt_dslope_same.mpr der.differentiableAt).tendsto.comp W)
  rw [dslope_same,der.deriv] at ds
  have motion : Tendsto (fun i ↦ (Complex.log (w i)-Complex.log ω)/(e i:ℂ)) l
      (𝓝 (ω⁻¹*u)) := by
    refine (ds.mul slope).congr (fun i ↦ ?_)
    simp only [Function.comp_apply]
    rw [← sub_smul_dslope Complex.log ω (w i),smul_eq_mul]
    ring
  constructor
  · convert (Complex.continuous_im.continuousAt.tendsto.comp motion) using 1
    ext i
    simp [Complex.div_ofReal_im,Complex.log_im]
  · convert (Complex.continuous_re.continuousAt.tendsto.comp motion) using 1
    ext i
    simp [Complex.div_ofReal_re,Complex.log_re]

#print axioms root_velocity
#print axioms polar_velocity
end OrderedPartitions.FourPole
