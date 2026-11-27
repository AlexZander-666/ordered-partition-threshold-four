import OrderedPartitions.FourPoleSixIntervals
import OrderedPartitions.FourPoleOscillatoryWindow

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals
open Complex

private theorem b_window :
    2121320/10000000<(3/10:ℝ)*(Real.sqrt 2/2) ∧
    (3/10:ℝ)*(Real.sqrt 2/2)<2121321/10000000 := by
  have := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  constructor <;> nlinarith [Real.sqrt_nonneg 2]

/-- A single actual small pole returns its signed radial and angular chart,
with the explicit six-cell loss. -/
theorem small_chart (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (eh : e≤(p.hi:ℝ)) {α : ℝ} (choice : α=Real.pi/4 ∨ α=3*Real.pi/4)
    {w : ℂ} (disk : ‖w-(dir α-(3/10:ℂ)*(dir α)^2*e)‖≤(p.radius:ℝ)*e^2) :
    (low p:ℝ)*e≤α-w.arg ∧ α-w.arg≤(high p:ℝ)*e ∧
    |Real.log ‖w‖+(3/10)*Real.cos α*e|≤(B p:ℝ)*e^2 := by
  obtain val := id ▸ valid i
  have hp : 0≤(p.hi:ℝ) := ep.le.trans eh
  have rp : 0≤(p.radius:ℝ) := by rcases val.disk with ⟨r,_⟩|⟨r,_⟩ <;> rw [r] <;> norm_num
  have un : ‖dir α‖=1 := Complex.norm_exp_ofReal_mul_I _
  have us : (u p:ℝ)=3/10+(p.radius:ℝ)*(p.hi:ℝ) := by unfold u;push_cast;rfl
  have upr : 0≤(u p:ℝ) := by rw [us];positivity
  have sm : (u p:ℝ)*(p.hi:ℝ)<1 := by exact_mod_cast val.logr
  have BP : (B p:ℝ)=(p.radius:ℝ)+(u p:ℝ)^2/(2*(1-(u p:ℝ)*(p.hi:ℝ))) := by
    unfold B;push_cast;rfl
  have Bp : 0≤(B p:ℝ) := by rw [BP];exact add_nonneg rp (div_nonneg (sq_nonneg _) (by linarith))
  have la := corrected_log ep eh rp un (le_of_eq us.symm) sm disk
  rw [←BP] at la
  have trig : (dir α).re=Real.cos α ∧ (dir α).im=Real.sin α := by
    change (Complex.exp (↑α*Complex.I)).re=_ ∧ (Complex.exp (↑α*Complex.I)).im=_
    simp [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have sin : Real.sin α=Real.sqrt 2/2 := by
    rcases choice with f|f <;> rw [f]
    · exact Real.sin_pi_div_four
    · rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.sin_pi_sub,Real.sin_pi_div_four]
  have arg : (dir α).arg=α := by
    unfold dir;rw [Complex.exp_mul_I];apply Complex.arg_cos_add_sin_mul_I
    rcases choice with f|f <;> subst α <;> constructor <;> linarith [Real.pi_pos]
  have re := (abs_re_le_norm _).trans la
  have im := (abs_im_le_norm _).trans la
  have fs : (3/10:ℂ)=↑(3/10:ℝ) := by push_cast;rfl
  rw [add_re,re_mul_ofReal,fs,re_ofReal_mul,trig.1,Complex.log_re,norm_div,un,div_one] at re
  rw [add_im,im_mul_ofReal,fs,im_ofReal_mul,trig.2,sin,Complex.log_im] at im
  let β := (w/dir α).arg
  change |β+3/10*(Real.sqrt 2/2)*e|≤_ at im
  have shrink := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eh ep.le) Bp
  have LL : (low p:ℝ)=2121320/10000000-(B p:ℝ)*(p.hi:ℝ) := by unfold low;push_cast;rfl
  have UU : (high p:ℝ)=2121321/10000000+(B p:ℝ)*(p.hi:ℝ) := by unfold high;push_cast;rfl
  have lower : (low p:ℝ)*e ≤ -β := by
    rw [LL];nlinarith only [(abs_le.mp im).2,shrink,mul_le_mul_of_nonneg_right b_window.1.le ep.le]
  have upper : -β≤(high p:ℝ)*e := by
    rw [UU];nlinarith only [(abs_le.mp im).1,shrink,mul_le_mul_of_nonneg_right b_window.2.le ep.le]
  have loPos : (0:ℝ)<low p := by exact_mod_cast val.lower
  have hiPos : (0:ℝ)≤high p := by rw [UU]; positivity
  have βneg : β<0 := by nlinarith only [lower,mul_pos loPos ep]
  have tiny : (high p:ℝ)*(p.hi:ℝ)<1/25 := by
    have tmp := (Rat.cast_lt (K:=ℝ)).mpr val.upper
    push_cast at tmp;exact tmp
  have βlo : -(1/25:ℝ)<β := by linarith only [upper,mul_le_mul_of_nonneg_left eh hiPos,tiny]
  have nz : w/dir α≠0 := by intro h;dsimp [β] at βneg;rw [h,arg_zero] at βneg;linarith
  have addA := Complex.arg_mul (show dir α≠0 from Complex.exp_ne_zero _) nz (show (dir α).arg+β∈Set.Ioc (-Real.pi) Real.pi by
    rw [arg]; rcases choice with f|f <;> rw [f] <;> constructor <;> linarith [Real.pi_gt_three])
  rw [show dir α*(w/dir α)=w by field_simp [show dir α≠0 from Complex.exp_ne_zero _],arg] at addA
  change w.arg=α+β at addA
  exact ⟨by linarith,by linarith,re⟩

#print axioms small_chart
end OrderedPartitions.FourPole.SixIntervals
