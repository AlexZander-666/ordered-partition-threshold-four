import OrderedPartitions.FourPoleSmallRatio
import OrderedPartitions.FourPoleCircleFloor

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals
open Complex

private theorem numerical (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (eh : e≤(p.hi:ℝ)) {w ω : ℂ} (un : ‖ω‖=1)
    (disk : ‖w-(ω-(3/10:ℂ)*ω^2*e)‖≤(p.radius:ℝ)*e^2) :
    1-(u p:ℝ)*(p.hi:ℝ)≤‖w‖ ∧ ‖w‖≤1+(u p:ℝ)*(p.hi:ℝ) := by
  have val := id ▸ valid i
  have rp : 0≤(p.radius:ℝ) := by rcases val.disk with ⟨r,_⟩|⟨r,_⟩ <;> rw [r] <;> norm_num
  have du : (u p:ℝ)=3/10+(p.radius:ℝ)*(p.hi:ℝ) := by unfold u;push_cast;rfl
  have up : 0≤(u p:ℝ) := by rw [du];have := ep.le.trans eh;positivity
  have t := norm_sub_le (w-(ω-(3/10:ℂ)*ω^2*e)) ((3/10:ℂ)*ω^2*e)
  rw [show w-(ω-(3/10:ℂ)*ω^2*e)-3/10*ω^2*e=w-ω by ring] at t
  simp [un,abs_of_pos ep] at t
  have close : ‖w-ω‖≤(u p:ℝ)*e := by
    rw [du];nlinarith only [t,disk,mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eh ep.le) rp]
  have a := norm_sub_le w (w-ω)
  rw [sub_sub_cancel,un] at a
  have b := norm_add_le (w-ω) ω
  rw [sub_add_cancel,un] at b
  have edge := mul_le_mul_of_nonneg_left eh up
  exact ⟨by linarith,by linarith⟩

theorem residue_bounds (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (eh : e≤(p.hi:ℝ)) {z v : ℂ} (pol : CirclePoles (1-e^4/24) 3 z v) :
    ‖first (1-e^4/24) z‖≤e^3/6*(dMax p:ℝ) ∧
    e^3/6*(dMin p:ℝ)≤‖first (1-e^4/24) v‖ ∧
    ‖z‖≤e*(1+(u p:ℝ)*(p.hi:ℝ)) := by
  obtain ⟨w,y,ew,ey,wd,yd⟩ := small_pair i p id ep eh pol
  have W := numerical i p id ep eh (Complex.norm_exp_ofReal_mul_I _) wd
  have Y := numerical i p id ep eh (Complex.norm_exp_ofReal_mul_I _) yd
  have val := id ▸ valid i
  have sm : (u p:ℝ)*(p.hi:ℝ)<1 := by exact_mod_cast val.logr
  have y3 := pow_le_pow_left₀ (show 0≤1-(u p:ℝ)*(p.hi:ℝ) by linarith) Y.1 3
  have w3 := pow_le_pow_left₀ (norm_nonneg _) W.2 3
  have dn (a : ℂ) (az : G (1-e^4/24) ((e:ℂ)*a)=0) :
      ‖first (1-e^4/24) ((e:ℂ)*a)‖=e^3/6*‖a^3-(e:ℂ)/2‖ := by
    rw [physical_residue_scale az,show residueScale e a=(1/6:ℂ)*(a^3-(e:ℂ)/2) by unfold residueScale;ring]
    simp [abs_of_pos ep];ring
  have Vz := pol.zeroLeft
  have Zz := pol.zeroRight
  rw [ew] at Zz
  rw [ey] at Vz
  rw [ew,ey,dn _ Zz,dn _ Vz]
  have en : ‖(e:ℂ)/2‖=e/2 := by simp [abs_of_pos ep]
  have wa := norm_sub_le (w^3) ((e:ℂ)/2)
  rw [Complex.norm_pow,en] at wa
  have ya := norm_add_le (y^3-(e:ℂ)/2) ((e:ℂ)/2)
  rw [sub_add_cancel,Complex.norm_pow,en] at ya
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity);unfold dMax;push_cast;linarith
  constructor
  · apply mul_le_mul_of_nonneg_left _ (by positivity);unfold dMin;push_cast;linarith
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep];gcongr;exact W.2

theorem size_budgets (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (el : (p.lo:ℝ)≤e) (eh : e≤(p.hi:ℝ)) {z v : ℂ}
    (pol : CirclePoles (1-e^4/24) 3 z v) {n : ℕ} (hn : 288≤n) (vis : 3≤(n:ℝ)*e) :
    |secondaryWeight n (1-e^4/24) z v| ≤ (amplitude p:ℝ) ∧
    ∀ m : ℕ, 2≤m → |circleError m (1-e^4/24) 3 z|≤(residue p:ℝ)*e := by
  have val := id ▸ valid i
  have dpos : 0<(dMin p:ℝ) := by exact_mod_cast val.den
  obtain ⟨ds,dl,zu⟩ := residue_bounds i p id ep eh pol
  have dm : 0≤(dMax p:ℝ) := by
    by_contra! no
    exact (not_lt_of_ge (norm_nonneg _)) (ds.trans_lt (mul_neg_of_pos_of_neg (by positivity) no))
  have quotientBound := div_le_div₀ (mul_nonneg (show 0≤e^3/6 by positivity) dm) ds (mul_pos (by positivity) dpos) dl
  rw [mul_div_mul_left _ _ (show e^3/6≠0 by positivity)] at quotientBound
  have rat := (ratio_powers i p id ep el eh pol hn vis).1
  have amp := mul_le_mul quotientBound rat (by positivity) (div_nonneg dm dpos.le)
  refine ⟨?_,?_⟩
  · unfold secondaryWeight;rw [abs_of_nonneg (by positivity)];unfold amplitude;push_cast
    exact amp.trans_eq (by ring)
  intro m hm
  have cap : e≤101/1000 := eh.trans (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr val.bounds.2.2)
  have near : (u p:ℝ)*(p.hi:ℝ)<1 := by exact_mod_cast val.logr
  obtain ⟨w,y,_,ey,_,yd⟩ := small_pair i p id ep eh pol
  have yb := (numerical i p id ep eh (Complex.norm_exp_ofReal_mul_I _) yd).2
  have bv : ‖v‖≤6/5 := by
    rw [ey,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    nlinarith only [mul_le_mul_of_nonneg_left (show ‖y‖≤2 by linarith) ep.le,cap]
  have az : ‖z‖≤6/5 := by
    have h : e*(1+(u p:ℝ)*(p.hi:ℝ))≤2*e := by nlinarith only [mul_le_mul_of_nonneg_left near.le ep.le]
    linarith
  have floor := circle_floor_of_sizes pol (by nlinarith only [pow_le_pow_left₀ ep.le cap 4]) az (by linarith)
    ((abs_re_le_norm _).trans bv)
  have cr := (circle_error_bound (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)<1/300)
    (fun w hw ↦ (floor w hw).le) m z).trans_eq (by ring :
    3/(2*(1/300))*‖first (1-e^4/24) z‖*(‖z‖/3)^(m+1)=450*‖first (1-e^4/24) z‖*(‖z‖/3)^(m+1))
  have base0 : 0≤‖z‖/3 := by positivity
  have base1 : ‖z‖/3≤1 := by linarith [pol.radiusRight]
  have short := pow_le_pow_of_le_one base0 base1 (show 2≤m+1 by omega)
  have upper : ‖z‖/3≤(p.hi:ℝ)*(1+(u p:ℝ)*(p.hi:ℝ))/3 := by
    have up : 0≤1+(u p:ℝ)*(p.hi:ℝ) := by
      by_contra! no;exact (not_lt_of_ge (norm_nonneg _)) (zu.trans_lt (mul_neg_of_pos_of_neg ep no))
    linarith only [zu,mul_le_mul_of_nonneg_right eh up]
  have cont := (Rat.cast_le (K:=ℝ)).mpr val.contour
  push_cast at cont
  have sq := pow_le_pow_left₀ base0 upper 2
  have cost : 450*(‖z‖/3)^(m+1)≤3/2 := by nlinarith only [short,cont,sq]
  have bound := mul_le_mul ds cost (by positivity) (mul_nonneg (by positivity) dm)
  have final := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ep.le eh 2) dm) ep.le
  unfold residue;push_cast
  nlinarith only [cr,bound,final]

#print axioms residue_bounds
#print axioms size_budgets
end OrderedPartitions.FourPole.SixIntervals
