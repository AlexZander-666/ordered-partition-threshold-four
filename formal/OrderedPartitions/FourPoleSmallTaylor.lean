import OrderedPartitions.FourPolePhysicalDisks
noncomputable section
namespace OrderedPartitions.FourPole
open Complex Finset

def truncExp (N : ℕ) (z : ℂ) := ∑ i∈range N,z^i/i.factorial
def smallPoly (e : ℝ) (z : ℂ) := 1+z^4+(e:ℂ)*(z^5/5-z)

/-- An unscaled quadratic error, uniform throughout the whole scaled disk. -/
theorem small_poly_error {e W : ℝ} (ep : 0<e) (cap : e*W≤1) {z : ℂ} (hz : ‖z‖≤W) :
    ‖scaledG e z-smallPoly e z‖ ≤ e^2*(W^2/2+2*e*W^3/9+7*W^6/180) := by
  let x : ℂ := (e:ℂ)*z
  have size : ‖x‖≤e*W := by
    dsimp [x]
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    gcongr
  have xcap := size.trans cap
  have h3 := Complex.exp_bound xcap (by decide : 0<3)
  have h6 := Complex.exp_bound xcap (by decide : 0<6)
  change ‖exp x-truncExp 3 x‖≤_ at h3
  change ‖exp x-truncExp 6 x‖≤_ at h6
  norm_num [Nat.factorial] at h3 h6
  have idn : scaledG e z-smallPoly e z =
      (24/(e:ℂ)^4)*(exp x-truncExp 6 x) - ((exp x-truncExp 3 x)+x^2/2) := by
    dsimp [x,scaledG,G,smallPoly,truncExp]
    push_cast;norm_num [sum_range_succ,Nat.factorial]
    field_simp [show (e:ℂ)≠0 by exact_mod_cast ep.ne'];ring
  rw [idn]
  have tri := (norm_sub_le ((24/(e:ℂ)^4)*(exp x-truncExp 6 x)) ((exp x-truncExp 3 x)+x^2/2)).trans
    (add_le_add le_rfl (norm_add_le _ _))
  rw [norm_mul,norm_div,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ep,norm_div,norm_pow,Complex.norm_ofNat] at tri
  have h6' : ‖exp x-truncExp 6 x‖ ≤ (e*W)^6*(7/4320) := by
    apply h6.trans
    gcongr
  have h3' : ‖exp x-truncExp 3 x‖ ≤ (e*W)^3*(2/9) := by
    apply h3.trans
    gcongr
  have h2 := pow_le_pow_left₀ (norm_nonneg _) size 2
  have pos : 0≤24/e^4 := by positivity
  have ex : 24/e^4*((e*W)^6*(7/4320)) = e^2*(7*W^6/180) := by field_simp;ring
  have bnd := mul_le_mul_of_nonneg_left h6' pos
  rw [ex] at bnd
  nlinarith only [tri,bnd,h3',h2]

private theorem power_lip (n : ℕ) {a b : ℂ} {M : ℝ} (ha : ‖a‖≤M) (hb : ‖b‖≤M) :
    ‖a^(n+1)-b^(n+1)‖ ≤ (n+1:ℕ)*M^n*‖a-b‖ := by
  have m0 := (norm_nonneg _).trans ha
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show a^(n+1+1)-b^(n+1+1) = a^(n+1)*(a-b)+b*(a^(n+1)-b^(n+1)) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_pow]
    calc
      _ ≤ M^(n+1)*‖a-b‖+M*((n+1:ℕ)*M^n*‖a-b‖) := by gcongr
      _ = _ := by push_cast;ring

/-- The analytic test retains the first displacement of each quartic root;
all constants are rational at the two application thresholds. -/
theorem corrected_disk {e H r u W : ℝ} (ep : 0<e) (small : e≤H) (rp : 0<r)
    (cu : u=3/10+r*H) (cw : W=1+u*H) (size : H*W≤1)
    (budget : (6+4*u*H+(u*H)^2)*u^2+u*(W^4+1)+W^2/2+2*H*W^3/9+7*W^6/180<4*r)
    {ω : ℂ} (quartic : ω^4= -1) (unit : ‖ω‖=1) :
    ∃ w : ℂ, ‖w-(ω-(3/10:ℂ)*ω^2*e)‖ < r*e^2 ∧ G (1-e^4/24) ((e:ℂ)*w)=0 := by
  let c : ℂ := ω-(3/10:ℂ)*ω^2*e
  let L := fun z : ℂ ↦ 4*ω^3*(z-c)
  have Hpos := ep.trans_le small
  have up : 0<u := by rw [cu];positivity
  have oneW : 1≤W := by rw [cw];nlinarith only [mul_nonneg up.le Hpos.le]
  have diff : Differentiable ℂ (scaledG e) := by unfold scaledG G;fun_prop
  obtain ⟨w,wi,wz⟩ := ThreePole.exists_zero_of_boundary_dominance (G:=scaledG e) (P:=L)
    (c:=c) (r:=r*e^2) (by positivity) diff (by dsimp [L];fun_prop) (by simp [L]) (by
      intro z zh
      have boundary : ‖z-c‖=r*e^2 := by simpa [dist_eq_norm] using Metric.mem_sphere.mp zh
      let y := z-ω
      have cn : ‖c-ω‖=3/10*e := by
        dsimp [c];rw [sub_sub_cancel_left,norm_neg,norm_mul,norm_mul,norm_div,
          Complex.norm_ofNat,Complex.norm_ofNat,norm_pow,unit,one_pow,mul_one,
          Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
      have Y : ‖y‖≤u*e := by
        have t := norm_add_le (z-c) (c-ω)
        rw [sub_add_sub_cancel,boundary,cn] at t
        dsimp [y];rw [cu];nlinarith only [t,mul_le_mul_of_nonneg_left small (mul_nonneg rp.le ep.le)]
      have YH := Y.trans (mul_le_mul_of_nonneg_left small up.le)
      have Z : ‖z‖≤W := by
        have t := norm_add_le (z-ω) ω
        rw [sub_add_cancel,unit] at t
        change ‖z-ω‖≤_ at YH
        rw [cw];linarith
      have eW := (mul_le_mul_of_nonneg_right small (by linarith : 0≤W)).trans size
      have approx := small_poly_error ep eW Z
      have lip := power_lip 4 Z (unit.le.trans oneW)
      norm_num at lip
      have delta : ‖((z^5-ω^5)/5-(z-ω))‖≤(W^4+1)*(u*e) := by
        have t := norm_sub_le ((z^5-ω^5)/5) (z-ω)
        rw [norm_div,Complex.norm_ofNat] at t
        change ‖z-ω‖≤_ at Y
        nlinarith only [t,lip,Y,mul_le_mul_of_nonneg_left Y (pow_nonneg (by linarith : 0≤W) 4)]
      have quart : ‖6*ω^2*y^2+4*ω*y^3+y^4‖≤(6+4*u*H+(u*H)^2)*(u*e)^2 := by
        have t := (norm_add_le (6*ω^2*y^2+4*ω*y^3) (y^4)).trans (add_le_add (norm_add_le _ _) le_rfl)
        simp only [norm_mul,norm_pow,Complex.norm_ofNat,unit,one_pow,mul_one] at t
        have Y2 := pow_le_pow_left₀ (norm_nonneg _) Y 2
        have Y3 := mul_le_mul Y2 YH (norm_nonneg _) (by positivity)
        have Y4 := mul_le_mul Y2 (pow_le_pow_left₀ (norm_nonneg _) YH 2) (sq_nonneg _) (by positivity)
        nlinarith only [t,Y2,Y3,Y4]
      have eqn : smallPoly e z-L z =
          (6*ω^2*y^2+4*ω*y^3+y^4)+(e:ℂ)*((z^5-ω^5)/5-(z-ω)) := by
        dsimp [smallPoly,L,c,y]
        linear_combination (1-(e:ℂ)*ω)*quartic
      have cross := mul_le_mul_of_nonneg_left delta ep.le
      change e*‖(z^5-ω^5)/5-(z-ω)‖≤_ at cross
      have mixed : ‖(e:ℂ)*((z^5-ω^5)/5-(z-ω))‖≤e*((W^4+1)*(u*e)) := by
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep] using cross
      have rest := (norm_add_le (6*ω^2*y^2+4*ω*y^3+y^4) ((e:ℂ)*((z^5-ω^5)/5-(z-ω)))).trans
          (add_le_add quart mixed)
      rw [←eqn] at rest
      have tr := (norm_add_le (scaledG e z-smallPoly e z) (smallPoly e z-L z)).trans (add_le_add approx rest)
      rw [sub_add_sub_cancel] at tr
      have lin : ‖L z‖=4*(r*e^2) := by simp [L,norm_pow,unit,boundary]
      rw [lin]
      have bump := mul_le_mul_of_nonneg_right small (show 0≤e^2*W^3 by positivity)
      nlinarith only [tr,bump,mul_lt_mul_of_pos_right budget (sq_pos_of_pos ep)])
  exact ⟨w,by simpa [dist_eq_norm] using Metric.mem_ball.mp wi,
    (mul_eq_zero.mp wz).resolve_left (div_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast ep.ne')))⟩

theorem small_corrected {e : ℝ} (ep : 0<e) (sm : e≤1/32) {ω : ℂ}
    (quartic : ω^4= -1) (unit : ‖ω‖=1) :
    ∃ w : ℂ, ‖w-(ω-(3/10:ℂ)*ω^2*e)‖ < (1/2:ℝ)*e^2 ∧ G (1-e^4/24) ((e:ℂ)*w)=0 := by
  exact corrected_disk (u:=3/10+(1/2)*(1/32)) (W:=1+(3/10+(1/2)*(1/32))*(1/32))
    ep sm (by norm_num) rfl rfl (by norm_num) (by norm_num) quartic unit

theorem tenth_corrected {e : ℝ} (ep : 0<e) (sm : e≤1/10) {ω : ℂ}
    (quartic : ω^4= -1) (unit : ‖ω‖=1) :
    ∃ w : ℂ, ‖w-(ω-(3/10:ℂ)*ω^2*e)‖ < (3/5:ℝ)*e^2 ∧ G (1-e^4/24) ((e:ℂ)*w)=0 := by
  exact corrected_disk (u:=3/10+(3/5)*(1/10)) (W:=1+(3/10+(3/5)*(1/10))*(1/10))
    ep sm (by norm_num) rfl rfl (by norm_num) (by norm_num) quartic unit

#print axioms small_corrected
#print axioms tenth_corrected
end OrderedPartitions.FourPole
