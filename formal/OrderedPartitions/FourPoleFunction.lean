import OrderedPartitions.FourPoleRootResponse
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Filter Topology

/-- Denominator multiplied by 1-q after t=-q/(1-q). -/
def G (q : ℝ) (z : ℂ) : ℂ := 1-2*(q:ℂ)-z-z^2/2-z^3/6+(q:ℂ)*Complex.exp z
def first (q : ℝ) (z : ℂ) : ℂ := (q:ℂ)*Complex.exp z-1-z-z^2/2

theorem hasDerivAt_G (q : ℝ) (z : ℂ) : HasDerivAt (G q) (first q z) z := by
  have h := ((((hasDerivAt_const z (1-2*(q:ℂ))).sub (hasDerivAt_id z)).sub
      (((hasDerivAt_id z).pow 2).div_const 2)).sub (((hasDerivAt_id z).pow 3).div_const 6)).add
      ((Complex.hasDerivAt_exp z).const_mul (q:ℂ))
  unfold G first
  convert h using 1 <;> first | rfl | (simp only [id_eq]; ring)

theorem first_at_root {q : ℝ} {z : ℂ} (zero : G q z=0) :
    first q z=z^3/6-2*(1-(q:ℂ)) := by
  unfold G at zero
  unfold first
  linear_combination zero

private def rem (m : ℕ) (z : ℂ) : ℂ :=
  Complex.exp z - ∑ a ∈ Finset.range (m+1), z^a/a.factorial

private theorem moving_remainder {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w : ι→ℂ} {ω : ℂ}
    (he : Tendsto e l (𝓝 0)) (W : Tendsto w l (𝓝 ω)) (hn : ω ≠ 0) (m : ℕ) :
    Tendsto (fun i ↦ rem m ((e i:ℂ)*w i)/(e i:ℂ)^m) l (𝓝 0) := by
  have E : Tendsto (fun i ↦ (e i:ℂ)) l (𝓝 0) := by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp he
  have Z := E.mul W
  rw [zero_mul] at Z
  have lim := (((Complex.exp_sub_sum_range_succ_isLittleO_pow m).tendsto_div_nhds_zero.comp Z).mul (W.pow m))
  rw [zero_mul] at lim
  refine lim.congr' ?_
  filter_upwards [W.eventually_ne hn] with i wi
  change rem m ((e i:ℂ)*w i)/((e i:ℂ)*w i)^m*w i^m=_
  rw [mul_pow,div_mul_eq_div_div,div_mul_cancel₀ _ (pow_ne_zero _ wi)]

/-- On any branch tending to a quartic pole in z/epsilon coordinates the actual
exponential denominator forces the required first-order velocity. -/
theorem physical_root_velocity {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w : ι→ℂ} {ω : ℂ}
    (quartic : ω^4 = -1) (he : Tendsto e l (𝓝 0)) (W : Tendsto w l (𝓝 ω))
    (en : ∀ᶠ i in l, e i ≠ 0)
    (zeros : ∀ᶠ i in l, G (1-e i^4/24) ((e i:ℂ)*w i)=0) :
    Tendsto (fun i ↦ (w i-ω)/(e i:ℂ)) l (𝓝 (-(3/10)*ω^2)) := by
  have nz : ω ≠ 0 := by intro eqn; simp [eqn] at quartic
  let err (i : ι) : ℂ := 24*rem 5 ((e i:ℂ)*w i)/(e i:ℂ)^4-rem 1 ((e i:ℂ)*w i)
  apply root_velocity (err:=err) quartic W en
  · have h := ((moving_remainder he W nz 5).const_mul 24).sub (moving_remainder he W nz 1)
    rw [mul_zero,sub_zero] at h
    refine h.congr (fun i ↦ ?_)
    dsimp [err]
    ring
  · filter_upwards [en,zeros] with i ei eqn
    have ei' : (e i:ℂ)≠0 := by exact_mod_cast ei
    unfold G at eqn
    push_cast at eqn
    dsimp [err,rem]
    norm_num [Finset.sum_range_succ,Nat.factorial]
    field_simp [ei']
    rw [mul_comm (w i) (e i:ℂ)]
    linear_combination 172800*eqn

#print axioms hasDerivAt_G
#print axioms first_at_root
#print axioms physical_root_velocity
end OrderedPartitions.FourPole
