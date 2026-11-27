import OrderedPartitions.FourPoleShiftChord

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Real

/-- In the upper π/4 sector only shifts one and four can attain the
smallest sine among the first four shifts. The normalized pole lies inside
the unit disk, giving polynomial coordinate lower bounds. -/
theorem bulk_sine {w : ℂ} (iw : 0<w.im) (rw' : w.im<w.re) (wu : ‖w‖<1)
    {s : ℝ} (sp : 0≤s) (one : s≤w.im) (four : s≤4*(w.re*w.im*(w.re-w.im)*(w.re+w.im)))
    {h : ℕ} (lo : 1≤h) (hi : h≤4) : s≤Real.sin ((h:ℝ)*w.arg) := by
  have wn : w≠0 := by intro h;simp [h] at iw
  have wp : 0<‖w‖ := norm_pos_iff.mpr wn
  have eqn := (polynomial_chord (z:=w) (v:=1) one_ne_zero h).2
  have sv : Real.sin ((h:ℝ)*w.arg)=(w^h).im/‖w‖^h := (eq_div_iff (pow_ne_zero h wp.ne')).mpr (by rw [mul_comm];exact eqn)
  rw [sv]
  apply (le_div_iff₀ (pow_pos wp h)).mpr
  have xr : 0<w.re := iw.trans rw'
  have x1 : w.re≤1 := (le_abs_self _).trans ((abs_re_le_norm _).trans wu.le)
  have sq : ‖w‖^2=w.re^2+w.im^2 := by rw [Complex.sq_norm];simp [normSq,pow_two]
  have diff := mul_pos (sub_pos.mpr rw') (add_pos xr iw)
  have twob : ‖w‖^2≤2*w.re := by nlinarith only [sq,diff,mul_le_mul_of_nonneg_left x1 xr.le]
  have threeb : ‖w‖^3≤3*w.re^2-w.im^2 := by
    nlinarith only [sq,diff,mul_le_mul_of_nonneg_left wu.le (sq_nonneg ‖w‖)]
  interval_cases h
  · simpa using (mul_le_mul_of_nonneg_left wu.le sp).trans (by simpa using one)
  · have im : (w^2).im=2*w.re*w.im := by simp [pow_two,Complex.mul_im];ring
    rw [im];nlinarith only [mul_le_mul_of_nonneg_right one (sq_nonneg ‖w‖),mul_le_mul_of_nonneg_right twob iw.le]
  · have im : (w^3).im=w.im*(3*w.re^2-w.im^2) := by simp [pow_succ,mul_im,mul_re];ring
    rw [im];nlinarith only [mul_le_mul_of_nonneg_right one (pow_nonneg wp.le 3),mul_le_mul_of_nonneg_right threeb iw.le]
  · have im : (w^4).im=4*(w.re*w.im*(w.re-w.im)*(w.re+w.im)) := by simp [pow_succ,mul_im,mul_re];ring
    rw [im]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ wp.le wu.le) sp).trans (by simpa using four)

#print axioms bulk_sine
end OrderedPartitions.FourPole
