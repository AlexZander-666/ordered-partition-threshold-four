import OrderedPartitions.FourPoleShiftChord

noncomputable section
namespace OrderedPartitions.FourPole
open Real Complex

theorem chord_short {δ η L : ℝ} (lp : 0≤L) (lu : L≤1) : shiftChord δ η L≤2 := by
  unfold shiftChord
  apply (norm_sub_le _ _).trans
  rw [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg lp,show ‖dir η‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one]
  linarith [Real.abs_cos_le_one δ]

/-- Chord estimate for a secondary rotation measured from the odd multiple 3π. -/
theorem chord_fourth {a b L : ℝ} (lp : 0≤L) (lu : L≤1) :
    shiftChord (π-a) (3*π-b) L ≤ a^2/2+(1-L)+|b| := by
  have turn : dir (3*π-b)= -dir (-b) := by
    unfold dir
    rw [show (↑(3*π-b):ℂ)*I = π*I+(2*π*I+ ↑(-b)*I) by push_cast;ring,
      Complex.exp_add,Complex.exp_add,Complex.exp_pi_mul_I,Complex.exp_two_pi_mul_I];ring
  have bd : ‖dir (-b)-1‖≤|b| := by
    unfold dir;rw [mul_comm];simpa only [Real.norm_eq_abs,abs_neg] using
      (Real.norm_exp_I_mul_ofReal_sub_one_le (x:= -b))
  have h := norm_add_le_of_le
    (norm_add_le ((1:ℂ)-(↑(Real.cos a):ℂ)) ((↑L:ℂ)-1))
    (le_refl ‖(↑L:ℂ)*(dir (-b)-1)‖)
  have t : ‖(1:ℂ)-(↑(Real.cos a):ℂ)‖=1-Real.cos a := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [Real.cos_le_one a])]
  have u : ‖(L:ℂ)-1‖=1-L := by
    rw [←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)];ring
  rw [t,u,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg lp] at h
  unfold shiftChord
  rw [Real.cos_pi_sub,turn,Complex.ofReal_neg,show -(↑(Real.cos a):ℂ)-↑L * -dir (-b) =
    (1-↑(Real.cos a)+(↑L-1))+(↑L:ℂ)*(dir (-b)-1) by ring]
  linarith only [h,Real.one_sub_sq_div_two_le_cos (x:=a),mul_le_mul_of_nonneg_left bd lp,
    mul_le_mul_of_nonneg_right lu (abs_nonneg b)]

theorem sine_short {q e θ : ℝ} {h : ℕ} (hh : 1≤h) (hi : h≤3)
    (l : 0≤π/4-θ) (r : π/4-θ≤q*e) : 7/10-3*q*e≤Real.sin ((h:ℝ)*θ) := by
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have b : (7/10:ℝ)≤Real.sqrt 2/2 := by nlinarith [Real.sqrt_nonneg 2]
  have ref : (7/10:ℝ)≤Real.sin ((h:ℝ)*(π/4)) := by
    interval_cases h <;> norm_num [show 2*(π/4)=π/2 by ring, show 3*(π/4)=π-π/4 by ring,
      Real.sin_pi_sub,Real.sin_pi_div_four] <;> linarith
  have d := (abs_le.mp (Real.abs_sin_sub_sin_le ((h:ℝ)*(π/4)) ((h:ℝ)*θ))).2
  rw [←mul_sub,abs_mul,abs_of_nonneg (by positivity : 0≤(h:ℝ)),abs_of_nonneg l] at d
  have a := mul_le_mul (show (h:ℝ)≤3 by exact_mod_cast hi) r l (by norm_num : (0:ℝ)≤3)
  linarith

theorem sine_fourth {l H e θ : ℝ} (positive : 0≤l*e) (lb : l*e≤π/4-θ)
    (ub : π/4-θ≤H*e) :
    4*l*e-(4*H*e)^3/6≤Real.sin (4*θ) := by
  let a := 4*(π/4-θ)
  have ap : 0≤a := by dsimp [a];linarith
  have au : a≤4*H*e := by dsimp [a];linarith
  rw [show 4*θ=π-a by dsimp [a];ring,Real.sin_pi_sub]
  nlinarith only [Real.sin_ge_sub_cube ap,pow_le_pow_left₀ ap au 3,lb,
    show a=4*(π/4-θ) from rfl]

#print axioms chord_short
#print axioms chord_fourth
#print axioms sine_short
#print axioms sine_fourth
end OrderedPartitions.FourPole
