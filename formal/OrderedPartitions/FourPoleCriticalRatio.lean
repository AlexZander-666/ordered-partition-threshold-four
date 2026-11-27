import OrderedPartitions.FourPoleFunction

/-! Effective derivative control all the way to the merged right-hand poles. -/
namespace OrderedPartitions.FourPole
open Complex

private theorem physical_coordinates {q : ℝ} {z : ℂ} (hz : G q z=0) :
    q*Real.exp z.re*Real.sin z.im = z.im*(1+z.re+z.re^2/2-z.im^2/6) ∧
    (first q z).re = q*Real.exp z.re*Real.cos z.im - (1+z.re+z.re^2/2-z.im^2/2) ∧
    (first q z).im = (3*z.re^2*z.im-z.im^3)/6 := by
  have im := congrArg Complex.im hz
  constructor
  · simp [G,pow_succ,Complex.mul_im,Complex.mul_re,Complex.div_ofNat_im,Complex.exp_im] at im
    linarith only [im]
  constructor
  · simp [first,pow_two,Complex.mul_re,Complex.div_ofNat_re,Complex.exp_re]
    ring
  · rw [first_at_root hz]
    simp [pow_succ,Complex.div_ofNat_im,Complex.mul_im,Complex.mul_re]
    ring

/-- At a true upper right pole the first derivative vanishes at least
linearly in its imaginary part. No root-separation hypothesis is required. -/
theorem critical_derivative_bound {q : ℝ} {z : ℂ} (hz : G q z=0)
    (xr : 0≤z.re) (xh : z.re≤6/5) (yi : 0<z.im) (yh : z.im≤6/5) :
    ‖first q z‖≤5*z.im := by
  let x := z.re
  let y := z.im
  let B := 1+x+x^2/2-y^2/6
  obtain ⟨imag,re,im⟩ := physical_coordinates hz
  change q*Real.exp x*Real.sin y=y*B at imag
  change (first q z).re=q*Real.exp x*Real.cos y-(1+x+x^2/2-y^2/2) at re
  change (first q z).im=(3*x^2*y-y^3)/6 at im
  change 0≤x at xr
  change x≤6/5 at xh
  change 0<y at yi
  change y≤6/5 at yh
  have y2 : y^2≤(6/5:ℝ)^2 := by gcongr
  have x2 : x^2≤(6/5:ℝ)^2 := by gcongr
  have bpos : 0≤B := by dsimp [B]; nlinarith [sq_nonneg x]
  have bcap : B≤3 := by dsimp [B]; nlinarith [sq_nonneg y]
  have sy := Real.sin_ge_sub_cube yi.le
  have cy := Real.one_sub_sq_div_two_le_cos (x:=y)
  have sylo : 3*y/4≤Real.sin y := by nlinarith [mul_le_mul_of_nonneg_right y2 yi.le]
  have yp : 0<Real.sin y := by linarith
  have err : |y*Real.cos y-Real.sin y|≤y^3/2 := by
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left cy yi.le,Real.sin_le yi.le]
    · nlinarith [mul_le_mul_of_nonneg_left (Real.cos_le_one y) yi.le,pow_nonneg yi.le 3]
  have numb : |y*Real.cos y / Real.sin y - 1|≤2*y^2/3 := by
    rw [div_sub_one yp.ne',abs_div,abs_of_pos yp]
    apply (div_le_iff₀ yp).mpr
    nlinarith only [err,mul_le_mul_of_nonneg_left sylo (sq_nonneg y)]
  have cancel : (first q z).re = (y*Real.cos y/Real.sin y-1)*B+y^2/3 := by
    rw [re]
    field_simp [yp.ne']
    dsimp [B] at *
    linear_combination 6*Real.cos y*imag
  have rb : |(first q z).re|≤7*y^2/3 := by
    rw [cancel]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_of_nonneg bpos,abs_of_nonneg (by positivity : 0≤y^2/3)]
    nlinarith only [mul_le_mul numb bcap bpos (by positivity)]
  have ib : |(first q z).im|≤y := by
    rw [im]
    apply abs_le.mpr
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left y2 yi.le,mul_nonneg (sq_nonneg x) yi.le]
    · nlinarith [mul_le_mul_of_nonneg_left x2 yi.le,pow_nonneg yi.le 3]
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  change _ ≤ 5*y
  nlinarith only [rb,ib,mul_le_mul_of_nonneg_right yh yi.le]

#print axioms critical_derivative_bound
end OrderedPartitions.FourPole
