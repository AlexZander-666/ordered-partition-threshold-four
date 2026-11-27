import OrderedPartitions.FourPoleCornerSign
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Relative angular and radial errors at a coalescing pair of conjugate pole pairs. -/
namespace OrderedPartitions.FourPole
open Real Filter Topology

theorem scaled_chain {ι : Type*} {l : Filter ι} {e u : ι → ℝ} {x b a : ℝ} {f : ℝ → ℝ}
    (he : Tendsto e l (𝓝 0)) (pos : ∀ᶠ i in l, 0 < e i)
    (slope : Tendsto (fun i ↦ (u i-x)/e i) l (𝓝 b)) (hf : HasDerivAt f a x) :
    Tendsto (fun i ↦ (f (u i)-f x)/e i) l (𝓝 (a*b)) := by
  have hu : Tendsto u l (𝓝 x) := by
    have h := (slope.mul he).add (tendsto_const_nhds (x:=x))
    rw [mul_zero,zero_add] at h
    refine h.congr' ?_
    filter_upwards [pos] with i hi
    field_simp [hi.ne']
    ring
  have hD := ((continuousAt_dslope_same.mpr hf.differentiableAt).tendsto.comp hu)
  rw [dslope_same,hf.deriv] at hD
  refine (hD.mul slope).congr (fun i ↦ ?_)
  simp only [Function.comp_apply]
  rw [← sub_smul_dslope f x (u i),smul_eq_mul]
  ring

theorem corner_slopes {ι : Type*} {l : Filter ι} {e θ φ v : ι → ℝ} {b : ℝ}
    (he : Tendsto e l (𝓝 0)) (pos : ∀ᶠ i in l, 0 < e i) (hb : 0 < b)
    (ht : Tendsto (fun i ↦ (θ i-π/4)/e i) l (𝓝 (-b)))
    (hf : Tendsto (fun i ↦ (φ i-3*π/4)/e i) l (𝓝 (-b)))
    (hv : Tendsto (fun i ↦ (v i-1)/e i) l (𝓝 (-2*b))) :
    Tendsto (fun i ↦ sin (4*θ i)/e i) l (𝓝 (4*b)) ∧
    Tendsto (fun i ↦ |1+cos (4*θ i)|/e i) l (𝓝 0) ∧
    Tendsto (fun i ↦ (|v i^4-1|+|4*φ i-3*π|)/e i) l (𝓝 (12*b)) ∧
    Tendsto (fun i ↦ log (v i)/e i) l (𝓝 (-2*b)) := by
  have turn : HasDerivAt (fun t : ℝ ↦ 4*t) 4 (π/4) := by simpa using (hasDerivAt_id (π/4)).const_mul 4
  have cancel : 4*(π/4)=π := by ring
  have st := scaled_chain he pos ht turn.sin
  simp only [cancel,sin_pi,cos_pi,sub_zero,neg_one_mul,neg_mul_neg] at st
  have ct := scaled_chain he pos ht turn.cos
  simp only [cancel,sin_pi,cos_pi,neg_zero,zero_mul,sub_neg_eq_add] at ct
  have pt := scaled_chain he pos hv ((hasDerivAt_id (1:ℝ)).pow 4)
  norm_num at pt
  have lt' := scaled_chain he pos hv (Real.hasDerivAt_log one_ne_zero)
  simp only [log_one,sub_zero,inv_one,one_mul] at lt'
  refine ⟨st,?_,?_,lt'⟩
  · have h := ct.abs
    rw [abs_zero] at h
    refine h.congr' ?_
    filter_upwards [pos] with i hi
    simp [abs_div,abs_of_pos hi,add_comm]
  · have pabs := pt.abs
    have fabs := ((tendsto_const_nhds (x:=(4:ℝ))).mul hf).abs
    have h := pabs.add fabs
    convert h.congr' (f₂:=fun i ↦ (|v i^4-1|+|4*φ i-3*π|)/e i) ?_ using 2
    · rw [abs_of_nonpos (by linarith : -(4*(2*b))≤0),abs_of_nonpos (by linarith : 4*(-b)≤0)]
      ring
    · filter_upwards [pos] with i hi
      rw [abs_div,abs_of_pos hi,show 4*((φ i-3*π/4)/e i)=(4*φ i-3*π)/e i by ring,
        abs_div,abs_of_pos hi,add_div]

/-- The estimate holds with no upper restriction on n times epsilon. -/
theorem damped_mass {v e A : ℝ} (n : ℕ) (ve : 0 < v) (ep : 0 < e)
    (logcap : log v ≤ -(21/50)*e) (window : 3 ≤ (n:ℝ)*e)
    (amp : |A| ≤ 101/100) : |A*v^(n+1)| ≤ 29/100 := by
  have cut : ((n+1:ℕ):ℝ)*log v ≤ -(63/50) := by
    push_cast
    have h := mul_le_mul_of_nonneg_left logcap (show 0≤(n:ℝ)+1 by positivity)
    linarith only [h,window,ep]
  have small : 7/2 ≤ exp (63/50) := by
    refine le_trans ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤63/50) 6)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have bound : v^(n+1) ≤ 2/7 := by
    calc
      v^(n+1) = exp (((n+1:ℕ):ℝ)*log v) := by rw [Real.exp_nat_mul,Real.exp_log ve]
      _ ≤ exp (-(63/50)) := Real.exp_le_exp.mpr cut
      _ ≤ 2/7 := by rw [exp_neg,inv_le_comm₀ (exp_pos _) (by norm_num)]; norm_num; linarith
  rw [abs_mul,abs_of_nonneg (pow_nonneg ve.le _)]
  have h := mul_le_mul amp bound (pow_nonneg ve.le _) (by norm_num)
  linarith only [h]

#print axioms scaled_chain
#print axioms corner_slopes
#print axioms damped_mass
end OrderedPartitions.FourPole
