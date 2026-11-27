import OrderedPartitions.FourPoleRadialLog
import OrderedPartitions.FourPoleCriticalPhase

noncomputable section
namespace OrderedPartitions.FourPole
open Complex

private theorem arg_near_one {Z : ℂ} {a : ℝ} (h : ‖Z-1‖≤a) (small : a≤1/2) :
    |Z.arg|≤3/2*a := by
  have b := norm_log_one_add_half_le_self (h.trans small)
  rw [show 1+(Z-1)=Z by ring] at b
  rw [←Complex.log_im]
  exact ((abs_im_le_norm (Complex.log Z)).trans b).trans (mul_le_mul_of_nonneg_left h (by norm_num))

private theorem derivative_ratio {w ω : ℂ} {e : ℝ} (un : ‖ω‖=1) (ep : 0<e) (sm : e≤1/96)
    (ww : ‖w-ω‖≤(31/100)*e) :
    ‖(w^3-(e:ℂ)/2)/ω^3-1‖≤(3/2)*e := by
  have oz : ω≠0 := by intro h;simp [h] at un
  have wh : ‖w‖≤101/100 := by
    have t := norm_add_le (w-ω) ω
    rw [sub_add_cancel,un] at t
    linarith
  have cap : ‖w^2+w*ω+ω^2‖≤31/10 := by
    calc
      _ ≤ (‖w‖^2+‖w‖*‖ω‖)+‖ω‖^2 := by
        rw [←Complex.norm_pow w 2,←Complex.norm_pow ω 2,←Complex.norm_mul w ω]
        exact norm_add_le_of_le (norm_add_le _ _) le_rfl
      _ ≤ _ := by rw [un];nlinarith [mul_self_le_mul_self (norm_nonneg w) wh]
  rw [show (w^3-(e:ℂ)/2)/ω^3-1=((w-ω)*(w^2+w*ω+ω^2)-(e:ℂ)/2)/ω^3 by field_simp;ring,
    norm_div,norm_pow,un,one_pow,div_one]
  have t := norm_sub_le ((w-ω)*(w^2+w*ω+ω^2)) ((e:ℂ)/2)
  rw [norm_mul] at t
  have h := mul_le_mul ww cap (norm_nonneg _) (by positivity)
  have e2 : ‖(e:ℂ)/2‖=e/2 := by simp [abs_of_pos ep]
  linarith

/-- The upper pole's phase at ε=3/n misses its limiting endpoint by
less than π/4 already at n=288. -/
theorem seam_phase {n : ℕ} (hn : 288≤n) {e : ℝ} (ep : 0<e) (seam : (n:ℝ)*e=3)
    {w : ℂ} (disk : let ω:=dir (Real.pi/4)
      ‖w-(ω-(3/10:ℂ)*ω^2*e)‖≤(1/2:ℝ)*e^2)
    (zero : G (1-e^4/24) ((e:ℂ)*w)=0) :
    |polarPhase n (1-e^4/24) ((e:ℂ)*w)-((n:ℝ)+4)*Real.pi/4|<Real.pi/4 := by
  let ω := dir (Real.pi/4)
  have un : ‖ω‖=1 := Complex.norm_exp_ofReal_mul_I _
  have oz : ω≠0 := by intro h;simp [h] at un
  change ‖w-(ω-(3/10:ℂ)*ω^2*e)‖≤_ at disk
  have S : e≤1/96 := by nlinarith only [mul_le_mul_of_nonneg_right (show (288:ℝ)≤n by exact_mod_cast hn) ep.le,seam]
  have se : e^2≤(1/96)*e := by nlinarith only [mul_le_mul_of_nonneg_right S ep.le]
  have pr := Real.pi_gt_three
  have oa : ω.arg=Real.pi/4 := by
    dsimp [ω,dir];rw [Complex.exp_mul_I];apply Complex.arg_cos_add_sin_mul_I
    constructor <;> linarith
  have oc : (ω^3).arg=3*Real.pi/4 := by
    dsimp [ω,dir];rw [←Complex.exp_nat_mul];norm_num only [Nat.cast_ofNat];rw [show (3:ℂ)*((↑(Real.pi/4):ℂ)*I)=↑(3*Real.pi/4)*I by push_cast;ring,Complex.exp_mul_I]
    apply Complex.arg_cos_add_sin_mul_I;constructor <;> linarith
  have oi : ω.im=Real.sqrt 2/2 := by
    change (Complex.exp ((↑(Real.pi/4):ℂ)*I)).im=_
    rw [Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos];simp
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have sl := Real.sqrt_nonneg 2
  have upper : Real.sqrt 2/2≤71/100 := by nlinarith
  have ww : ‖w-ω‖≤31/100*e := by
    have b := norm_sub_le (w-(ω-(3/10:ℂ)*ω^2*e)) ((3/10:ℂ)*ω^2*e)
    rw [show w-(ω-(3/10:ℂ)*ω^2*e)-3/10*ω^2*e=w-ω by ring] at b
    simp [un,abs_of_pos ep] at b
    linarith
  have small := corrected_log (H:=1/96) (u:=31/100) ep S (by norm_num) un (by norm_num) (by norm_num) disk
  have cb : ((1/2:ℝ)+(31/100)^2/(2*(1-31/100*(1/96))))≤11/20 := by norm_num
  have im := (abs_im_le_norm _).trans (small.trans (mul_le_mul_of_nonneg_right cb (sq_nonneg e)))
  change |(Complex.log (w/ω)+(3/10:ℂ)*ω*e).im|≤_ at im
  have ii : ((3/10:ℂ)*ω*e).im=(3/10:ℝ)*(Real.sqrt 2/2)*e := by
    rw [im_mul_ofReal,show (3/10:ℂ)=(↑(3/10:ℝ):ℂ) by push_cast;rfl,im_ofReal_mul,oi]
  rw [add_im,ii,Complex.log_im] at im
  have wa : |(w/ω).arg|≤11/50*e := by
    rcases abs_le.mp im with ⟨l,h⟩
    exact abs_le.mpr ⟨by nlinarith only [l,mul_le_mul_of_nonneg_right upper ep.le,se], by nlinarith only [h,mul_nonneg sl ep.le,se]⟩
  have hder := derivative_ratio un ep S ww
  let Z := (w^3-(e:ℂ)/2)/ω^3
  have za : |Z.arg|≤9/4*e := by
    exact (arg_near_one hder (by linarith)).trans_eq (by ring)
  have wn : w≠0 := by intro hw;rw [hw,zero_sub,norm_neg,un] at ww;linarith
  have zn : Z≠0 := by
    change ‖Z-1‖≤_ at hder
    intro hz;rw [hz,zero_sub,norm_neg,norm_one] at hder;linarith
  have aw : w.arg=Real.pi/4+(w/ω).arg := by
    have t := Complex.arg_mul oz (div_ne_zero wn oz) (by rw [oa]; constructor <;> linarith [(abs_le.mp wa).1,(abs_le.mp wa).2] : ω.arg+(w/ω).arg∈Set.Ioc (-Real.pi) Real.pi)
    rwa [show ω*(w/ω)=w by field_simp,oa] at t
  have az : (w^3-(e:ℂ)/2).arg=3*Real.pi/4+Z.arg := by
    have t := Complex.arg_mul (pow_ne_zero 3 oz) zn (by rw [oc]; constructor <;> linarith [(abs_le.mp za).1,(abs_le.mp za).2] : (ω^3).arg+Z.arg∈Set.Ioc (-Real.pi) Real.pi)
    rw [oc] at t
    convert t using 2
    dsimp [Z];field_simp
  have fac : first (1-e^4/24) ((e:ℂ)*w) = ((e^3/6:ℝ):ℂ)*(w^3-(e:ℂ)/2) := by
    rw [physical_residue_scale zero];unfold residueScale;push_cast;ring
  unfold polarPhase
  rw [fac,Complex.arg_real_mul _ ep,Complex.arg_real_mul _ (show 0<e^3/6 by positivity),aw,az]
  push_cast
  rw [show ((n:ℝ)+1)*(Real.pi/4+(w/ω).arg)+(3*Real.pi/4+Z.arg)-((n:ℝ)+4)*Real.pi/4=((n:ℝ)+1)*(w/ω).arg+Z.arg by ring]
  have h := abs_add_le (((n:ℝ)+1)*(w/ω).arg) Z.arg
  rw [abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤n+1)] at h
  nlinarith only [h,mul_le_mul_of_nonneg_left wa (show 0≤(n:ℝ)+1 by positivity),za,seam,S,pr]

/-- The effective phase endpoint holds for the unique physical upper-right pole
of *any* four-pole representation, so no choice of local branches is required. -/
theorem original_seam_phase {n : ℕ} (hn : 288≤n) {e : ℝ} (ep : 0<e) (seam : (n:ℝ)*e=3)
    {z v : ℂ} (poles : CirclePoles (1-e^4/24) 3 z v) :
    ((n/4:ℕ):ℝ)*Real.pi+3*Real.pi/4 < polarPhase n (1-e^4/24) z := by
  have S : e≤1/96 := by nlinarith only [mul_le_mul_of_nonneg_right (show (288:ℝ)≤n by exact_mod_cast hn) ep.le,seam]
  let ω := dir (Real.pi/4)
  have unit : ‖ω‖=1 := Complex.norm_exp_ofReal_mul_I _
  obtain ⟨w,disk,zero⟩ := small_corrected ep (by linarith [S]) quartic_dirs.1 unit
  have gap := seam_phase hn ep seam disk.le zero
  have W : ‖w-ω‖≤1/100 := by
    have b := norm_sub_le (w-(ω-(3/10:ℂ)*ω^2*e)) ((3/10:ℂ)*ω^2*e)
    rw [show w-(ω-(3/10:ℂ)*ω^2*e)-3/10*ω^2*e=w-ω by ring] at b
    simp [unit,abs_of_pos ep] at b
    nlinarith only [b,disk.le,mul_le_mul_of_nonneg_right S ep.le,S]
  have R : ω.re=Real.sqrt 2/2 ∧ ω.im=Real.sqrt 2/2 := by
    change (Complex.exp (↑(Real.pi/4)*I)).re=_ ∧ (Complex.exp (↑(Real.pi/4)*I)).im=_
    rw [Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos];simp
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have sl := Real.sqrt_nonneg 2
  have re := abs_le.mp ((abs_re_le_norm _).trans W)
  have im := abs_le.mp ((abs_im_le_norm _).trans W)
  rw [sub_re,R.1] at re
  rw [sub_im,R.2] at im
  let Z := (e:ℂ)*w
  have up : 0<Z.im := by change 0<((e:ℂ)*w).im;rw [im_ofReal_mul];exact mul_pos ep (by nlinarith [im.1])
  have right : 0<Z.re := by change 0<((e:ℂ)*w).re;rw [re_ofReal_mul];exact mul_pos ep (by nlinarith [re.1])
  have wz : ‖Z‖≤3 := by
    have h := norm_add_le (w-ω) ω
    rw [sub_add_cancel,unit] at h
    change ‖(e:ℂ)*w‖≤3
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    nlinarith only [mul_le_mul_of_nonneg_left (show ‖w‖≤2 by linarith) ep.le,S]
  obtain E|E|E|E := poles.exhaustive Z wz zero
  · change |polarPhase n _ Z-_|<_ at gap
    rw [E] at gap
    have bound : ((n/4:ℕ):ℝ)*4≤n := by exact_mod_cast Nat.div_mul_le_self n 4
    nlinarith only [(abs_lt.mp gap).1,mul_le_mul_of_nonneg_right bound Real.pi_pos.le]
  · rw [E] at up;change 0< -z.im at up;linarith [poles.upperRight]
  · rw [E] at right;linarith [poles.left]
  · rw [E] at up;change 0< -v.im at up;linarith [poles.upperLeft]

#print axioms seam_phase
#print axioms original_seam_phase
end OrderedPartitions.FourPole
