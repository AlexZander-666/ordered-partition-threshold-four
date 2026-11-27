import OrderedPartitions.FourPoleCornerLimits
import Mathlib.Analysis.Real.Pi.Bounds

/-! Uniformity at the edge is simultaneous in the real parameter and the row number. -/
namespace OrderedPartitions.FourPole
open Real Filter Topology

noncomputable def cornerSpeed : ℝ := 3/(10*√2)

theorem speed_window : 21/100 < cornerSpeed ∧ 3*cornerSpeed < π/4 := by
  have p : 0 < √(2:ℝ) := Real.sqrt_pos.2 (by norm_num)
  have sq := Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)
  have hi : √(2:ℝ) < 10/7 := by nlinarith
  have lo : 6/5 < √(2:ℝ) := by nlinarith
  unfold cornerSpeed
  constructor
  · apply (lt_div_iff₀ (by positivity)).2
    linarith
  · have bound : (3:ℝ)/(10*√2) < 1/4 := by
      apply (div_lt_iff₀ (by positivity)).2
      linarith
    linarith [Real.pi_gt_three]

/-- Every large-enough corner point works for *all* n with n epsilon at least three.
Only the derivatives of the pole coordinates and a quadratic contour majorant enter. -/
theorem uniform_fourth {ι : Type*} {l : Filter ι} {e θ φ v A : ι → ℝ}
    (he : Tendsto e l (𝓝 0)) (ep : ∀ᶠ i in l, 0<e i) (vp : ∀ᶠ i in l, 0<v i)
    (ht : Tendsto (fun i ↦ (θ i-π/4)/e i) l (𝓝 (-cornerSpeed)))
    (hf : Tendsto (fun i ↦ (φ i-3*π/4)/e i) l (𝓝 (-cornerSpeed)))
    (hv : Tendsto (fun i ↦ (v i-1)/e i) l (𝓝 (-2*cornerSpeed)))
    (ha : Tendsto A l (𝓝 1)) :
    ∀ᶠ i in l, ∀ n : ℕ, 3 ≤ (n:ℝ)*e i → ∀ ψ χ E F : ℝ,
      |E| ≤ e i^2 → |F| ≤ e i^2 → model ψ χ (A i*v i^(n+1)) E = 0 →
      0 < sin ψ * model (ψ+4*θ i) (χ+4*φ i) ((A i*v i^(n+1))*v i^4) F := by
  have b := speed_window.1
  have bp : 0 < cornerSpeed := by linarith
  obtain ⟨st,ct,ft,lt'⟩ := corner_slopes he ep bp ht hf hv
  have hmain := ct.eventually_lt (st.div_const 40) (by linarith : 0 < 4*cornerSpeed/40)
  have hside := ft.eventually_lt ((tendsto_const_nhds (x:=(31/10:ℝ))).mul st)
    (by linarith : 12*cornerSpeed < 31/10*(4*cornerSpeed))
  have htail := ((tendsto_const_nhds (x:=(2:ℝ))).mul he).eventually_lt (st.div_const 50)
    (by linarith : 2*0 < 4*cornerSpeed/50)
  have hlog := lt'.eventually_lt_const (show -2*cornerSpeed < -(21/50) by linarith)
  have hamp := ha.abs.eventually_lt_const (show |(1:ℝ)| < 101/100 by norm_num)
  have he2 := (he.pow 2).eventually_lt_const (show (0:ℝ)^2<1/100 by norm_num)
  filter_upwards [ep,vp,hmain,hside,htail,hlog,hamp,he2] with i pos vi main side tail lg amp tiny
  intro n window ψ χ E F eOld eNew zero
  have mass := damped_mass n vi pos ((div_le_iff₀ pos).1 lg.le) window amp.le
  have m := (mul_lt_mul_of_pos_right main pos)
  have s := (mul_lt_mul_of_pos_right side pos)
  have t := (mul_lt_mul_of_pos_right tail pos)
  field_simp [pos.ne'] at m s t
  have zeroSin : 0 < sin (4*θ i) := by nlinarith [sq_nonneg (e i)]
  exact fourth_sign zero mass (eOld.trans tiny.le) zeroSin (by linarith only [m])
    (by linarith only [s]) (by nlinarith only [t,eOld,eNew])

#print axioms speed_window
#print axioms uniform_fourth
end OrderedPartitions.FourPole
