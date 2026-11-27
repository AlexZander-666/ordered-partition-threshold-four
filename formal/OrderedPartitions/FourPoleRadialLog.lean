import OrderedPartitions.FourPoleSmallTaylor
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

noncomputable section
namespace OrderedPartitions.FourPole
open Complex

/-- Quadratic error after taking the logarithm in the rotating frame of a
unit fourth root. The imaginary and real parts bound argument and radial
displacement simultaneously. -/
theorem corrected_log {w ω : ℂ} {e H r u : ℝ} (ep : 0<e) (sm : e≤H)
    (rp : 0≤r) (un : ‖ω‖=1) (us : 3/10+r*H≤u) (small : u*H<1)
    (disk : ‖w-(ω-(3/10:ℂ)*ω^2*e)‖≤r*e^2) :
    ‖Complex.log (w/ω)+(3/10:ℂ)*ω*e‖≤
      (r+u^2/(2*(1-u*H)))*e^2 := by
  have oz : ω≠0 := by intro h; simp [h] at un
  have up : 0≤u := by nlinarith [mul_nonneg rp (ep.le.trans sm)]
  let d := w/ω-1
  have smallD : ‖d+(3/10:ℂ)*ω*e‖≤r*e^2 := by
    rw [show d+(3/10:ℂ)*ω*e=(w-(ω-(3/10:ℂ)*ω^2*e))/ω by dsimp [d];field_simp;ring,
      norm_div,un,div_one]
    exact disk
  have bias : ‖(3/10:ℂ)*ω*e‖=3/10*e := by simp [un,abs_of_pos ep]
  have D : ‖d‖≤u*e := by
    have h := norm_sub_le (d+(3/10:ℂ)*ω*e) ((3/10:ℂ)*ω*e)
    rw [add_sub_cancel_right,bias] at h
    nlinarith only [h,smallD,mul_le_mul_of_nonneg_right us ep.le,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right sm ep.le) rp]
  have U := mul_le_mul_of_nonneg_left sm up
  have ds : ‖d‖<1 := lt_of_le_of_lt (D.trans U) small
  have dn : 0<1-‖d‖ := by linarith
  have hn : 0<1-u*H := by linarith
  have logD := Complex.norm_log_one_add_sub_self_le ds
  have e2 : ‖d‖^2≤(u*e)^2 := by gcongr
  have rat : ‖d‖^2/(1-‖d‖) ≤ (u*e)^2/(1-u*H) := by
    apply div_le_div₀ (sq_nonneg _) e2 hn
    linarith
  have tr := norm_add_le (Complex.log (1+d)-d) (d+(3/10:ℂ)*ω*e)
  rw [show Complex.log (1+d)-d+(d+3/10*ω*e)=Complex.log (1+d)+3/10*ω*e by ring] at tr
  rw [←show 1+d=w/ω by simp [d]]
  rw [← div_eq_mul_inv] at logD
  have endB : (u*e)^2/(1-u*H)/2+r*e^2=(r+u^2/(2*(1-u*H)))*e^2 := by field_simp [hn.ne'];ring
  rw [←endB]
  linarith

#print axioms corrected_log
end OrderedPartitions.FourPole
