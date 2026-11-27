import OrderedPartitions.FourPoleBulkPair
import OrderedPartitions.FourPoleBulkSine
import OrderedPartitions.FourPoleCriticalRatio

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Real

private theorem residue_norm {a : ℂ} {e : ℝ} (ep : 0<e) (zero : G (1-e^4/24) ((e:ℂ)*a)=0) :
    ‖first (1-e^4/24) ((e:ℂ)*a)‖=e^3/6*‖a^3-(e:ℂ)/2‖ := by
  rw [physical_residue_scale zero,show residueScale e a=(1/6:ℂ)*(a^3-(e:ℂ)/2) by unfold residueScale;ring]
  simp [abs_of_pos ep];ring

/-- On each compact cell a single positive scale controls both the true
secondary mass and the contour error. It is one on regular cells and the
scaled primary height at the critical cell. -/
theorem bulk_budgets {e : ℝ} (elo : 101/1000≤e) (ehi : e≤1143/1000)
    {z v : ℂ} (pol : CirclePoles (1-e^4/24) 3 z v) {n h : ℕ} (hn : 288≤n)
    (hp : 1≤h) (hg : h≤4) :
    let q := 1-e^4/24
    ∃ s : ℝ, 0<s ∧ s≤1 ∧ s/50≤Real.sin ((h:ℝ)*z.arg) ∧
      |secondaryWeight n q z v|≤s/150 ∧
      ∀ m : ℕ, 288≤m → |circleError m q 3 z|≤s/1000 := by
  dsimp only
  obtain ⟨w,y,bp⟩ := Box.get_bulk_pair elo ehi pol
  have ep : 0<e := by linarith
  let q := 1-e^4/24
  let D := ‖first q z‖
  let V := ‖first q v‖
  let L := ‖z‖/‖v‖
  have er (s : ℂ) : ‖(e:ℂ)*s‖=e*‖s‖ := by simp [abs_of_pos ep]
  have Lw : L=‖w‖/‖y‖ := by dsimp [L];rw [bp.right_eq,bp.left_eq,er,er,mul_div_mul_left _ _ ep.ne']
  have L0 : 0≤L := by dsimp [L];positivity
  have L1 : L≤1 := by rw [Lw];linarith [bp.ratio]
  have zmag : ‖z‖≤6/5 := by rw [bp.right_eq,er];nlinarith only [mul_le_mul_of_nonneg_left bp.right_lt.le ep.le,ehi]
  have floor := circle_floor_of_sizes pol (by nlinarith only [pow_le_pow_left₀ ep.le ehi 4]) zmag bp.left_norm bp.left_real
  have D0 : 0≤D := norm_nonneg _
  have Vp : 0<V := norm_pos_iff.mpr pol.simpleLeft
  have en : ‖(e:ℂ)/2‖=e/2 := by simp [abs_of_pos ep]
  have wz := pol.zeroRight
  have yz := pol.zeroLeft
  rw [bp.right_eq] at wz
  rw [bp.left_eq] at yz
  have du : D≤e^3/6*(1+e/2) := by
    dsimp [D,q];rw [bp.right_eq,residue_norm ep wz]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have t := norm_sub_le (w^3) ((e:ℂ)/2)
    rw [Complex.norm_pow,en] at t
    linarith only [t,pow_le_one₀ (norm_nonneg w) bp.right_lt.le (n:=3)]
  have vl : e^3/6*(1-e/2)≤V := by
    dsimp [V,q];rw [bp.left_eq,residue_norm ep yz]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have t := norm_add_le (y^3-(e:ℂ)/2) ((e:ℂ)/2)
    rw [sub_add_cancel,Complex.norm_pow,en] at t
    linarith only [t,one_le_pow₀ bp.left_gt.le (n:=3)]
  have eratio : D/V≤4 := by
    apply (div_le_iff₀ Vp).mpr
    have f := mul_le_mul_of_nonneg_left (show 1+e/2≤4*(1-e/2) by linarith) (show 0≤e^3/6 by positivity)
    linarith only [du,vl,f]
  have d1 : D≤1 := by
    have a := pow_le_pow_left₀ ep.le (show e≤6/5 by linarith) 3
    nlinarith only [du,mul_le_mul a (show 1+e/2≤8/5 by linarith) (show 0≤1+e/2 by linarith) (by norm_num : (0:ℝ)≤(6/5)^3)]
  have rem (m : ℕ) (hm : 288≤m) : |circleError m q 3 z|≤D/10000 := by
    have raw := (circle_error_bound (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)<1/300)
      (fun w hw ↦ (floor w hw).le) m z).trans_eq (by ring :
      3/(2*(1/300))*D*(‖z‖/3)^(m+1)=450*D*(‖z‖/3)^(m+1))
    have base : 0≤‖z‖/3 := by positivity
    have p := (pow_le_pow_of_le_one base (by linarith : ‖z‖/3≤1) (by omega : 18≤m+1)).trans
      (pow_le_pow_left₀ base (by linarith : ‖z‖/3≤2/5) 18)
    have cut : 450*(‖z‖/3)^(m+1)≤1/10000 := by
      linarith only [p,show (450:ℝ)*(2/5)^18≤1/10000 by norm_num]
    nlinarith only [raw,mul_le_mul_of_nonneg_left cut D0]
  have amp : |secondaryWeight n q z v|=(D/V)*L^(n+1) := by
    dsimp [secondaryWeight,D,V,L];rw [abs_of_nonneg (by positivity)]
  have argz : z.arg=w.arg := by rw [bp.right_eq,Complex.arg_real_mul _ ep]
  rw [argz,amp]
  have pn := pow_le_pow_of_le_one L0 L1 (show 288≤n+1 by omega)
  rcases bp.modes with ⟨yreg,prod⟩|⟨e1,strong,xr,diff⟩
  · refine ⟨1,by norm_num,le_rfl,bulk_sine bp.upper bp.right bp.right_lt (by norm_num) yreg (by linarith) hp hg,?_,?_⟩
    · have base : L≤489/500 := by rw [Lw];exact bp.ratio
      have cap : (489/500:ℝ)^288≤1/600 := by
        have test : (489/500:ℚ)^288≤1/600 := by decide +kernel
        have tmp := (Rat.cast_le (K:=ℝ)).mpr test
        push_cast at tmp;exact tmp
      have power := pn.trans ((pow_le_pow_left₀ L0 base 288).trans cap)
      nlinarith only [mul_le_mul eratio power (pow_nonneg L0 _) (by norm_num : (0:ℝ)≤4)]
    · intro m hm;linarith only [rem m hm,d1]
  · have yy : w.im≤1 := (le_abs_self _).trans ((abs_im_le_norm _).trans bp.right_lt.le)
    have zg : z.im=e*w.im := by rw [bp.right_eq,im_ofReal_mul]
    have zrb : z.re≤6/5 := (le_abs_self _).trans ((abs_re_le_norm _).trans zmag)
    have zib : z.im≤6/5 := (le_abs_self _).trans ((abs_im_le_norm _).trans zmag)
    have der := critical_derivative_bound pol.zeroRight pol.right.le zrb pol.upperRight zib
    rw [zg] at der
    change D≤5*(e*w.im) at der
    have d6 : D≤6*w.im := by nlinarith only [der,mul_le_mul_of_nonneg_right (show e≤6/5 by linarith) bp.upper.le]
    have vlow : 1/15≤V := by
      have a := one_le_pow₀ e1 (n:=3)
      have b := mul_le_mul a (show 2/5≤1-e/2 by linarith) (by norm_num : (0:ℝ)≤2/5) (pow_nonneg ep.le 3)
      nlinarith only [b,vl]
    have quotient : D/V≤90*w.im := by
      apply (div_le_iff₀ Vp).mpr
      nlinarith only [d6,mul_le_mul_of_nonneg_left vlow bp.upper.le]
    have big : w.im/50≤4*(w.re*w.im*(w.re-w.im)*(w.re+w.im)) := by
      have lo1 : (13/20:ℝ)≤w.re+w.im := by linarith [bp.upper]
      have a := mul_le_mul xr diff (by norm_num) (by linarith : 0≤w.re)
      have b := mul_le_mul a lo1 (by norm_num) (mul_nonneg (by linarith) (sub_nonneg.mpr bp.right.le))
      nlinarith only [mul_le_mul_of_nonneg_right b bp.upper.le,bp.upper]
    refine ⟨w.im,bp.upper,yy,bulk_sine bp.upper bp.right bp.right_lt (div_nonneg bp.upper.le (by norm_num)) (by linarith [bp.upper]) big hp hg,?_,?_⟩
    · have base : L≤93/100 := by rw [Lw];exact strong
      have cap : (93/100:ℝ)^288≤1/100000 := by
        have test : (93/100:ℚ)^288≤1/100000 := by decide +kernel
        have tmp := (Rat.cast_le (K:=ℝ)).mpr test
        push_cast at tmp;exact tmp
      have power := pn.trans ((pow_le_pow_left₀ L0 base 288).trans cap)
      have m := mul_le_mul quotient power (pow_nonneg L0 _) (show 0≤90*w.im from mul_nonneg (by norm_num) bp.upper.le)
      linarith only [m,bp.upper]
    · intro m hm;linarith only [rem m hm,d6,bp.upper]

#print axioms bulk_budgets
end OrderedPartitions.FourPole
