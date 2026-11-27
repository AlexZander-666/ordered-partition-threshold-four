import OrderedPartitions.FourPoleSmallAngles

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals
open Complex

/-- Both local Rouché disks identify the poles in any representation of
the original EGF. This gives the two log charts the same physical parameter. -/
theorem small_pair (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (eh : e≤(p.hi:ℝ)) {z v : ℂ} (pol : CirclePoles (1-e^4/24) 3 z v) :
    ∃ w y : ℂ, z=(e:ℂ)*w ∧ v=(e:ℂ)*y ∧
      ‖w-(dir (Real.pi/4)-(3/10:ℂ)*(dir (Real.pi/4))^2*e)‖≤(p.radius:ℝ)*e^2 ∧
      ‖y-(dir (3*Real.pi/4)-(3/10:ℂ)*(dir (3*Real.pi/4))^2*e)‖≤(p.radius:ℝ)*e^2 := by
  have val := id ▸ valid i
  have cap : e≤101/1000 := eh.trans (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr val.bounds.2.2)
  have find (α : ℝ) (quartic : (dir α)^4= -1) :
      ∃ w : ℂ, ‖w-(dir α-(3/10:ℂ)*(dir α)^2*e)‖≤(p.radius:ℝ)*e^2 ∧
        G (1-e^4/24) ((e:ℂ)*w)=0 ∧ ‖w-dir α‖≤1/10 ∧ ‖(e:ℂ)*w‖≤3 := by
    have un : ‖dir α‖=1 := Complex.norm_exp_ofReal_mul_I _
    have raw : ∃ w : ℂ, ‖w-(dir α-(3/10:ℂ)*(dir α)^2*e)‖<(p.radius:ℝ)*e^2 ∧
        G (1-e^4/24) ((e:ℂ)*w)=0 := by
      rcases val.disk with ⟨r,h⟩|⟨r,_⟩
      · have eq : (p.radius:ℝ)=1/2 := by rw [r];norm_num
        rw [eq];exact small_corrected ep (eh.trans (by simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_le (K:=ℝ)).mpr h)) quartic un
      · have eq : (p.radius:ℝ)=3/5 := by rw [r];norm_num
        rw [eq]
        exact corrected_disk (H:=101/1000) (u:=3/10+(3/5)*(101/1000))
          (W:=1+(3/10+(3/5)*(101/1000))*(101/1000)) ep cap
          (by norm_num) rfl rfl (by norm_num) (by norm_num) quartic un
    obtain ⟨w,wc,wz⟩ := raw
    have t := norm_sub_le (w-(dir α-(3/10:ℂ)*(dir α)^2*e)) ((3/10:ℂ)*(dir α)^2*e)
    rw [show w-(dir α-(3/10:ℂ)*(dir α)^2*e)-3/10*(dir α)^2*e=w-dir α by ring] at t
    simp [un,abs_of_pos ep] at t
    have rh : (p.radius:ℝ)≤3/5 := by rcases val.disk with ⟨r,_⟩|⟨r,_⟩ <;> rw [r] <;> norm_num
    have close : ‖w-dir α‖≤1/10 := by
      nlinarith only [wc,t,mul_le_mul_of_nonneg_right rh (sq_nonneg e),pow_le_pow_left₀ ep.le cap 2,cap]
    have wh := norm_add_le (w-dir α) (dir α)
    rw [sub_add_cancel,un] at wh
    refine ⟨w,wc.le,wz,close,?_⟩
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    nlinarith only [mul_le_mul_of_nonneg_left (show ‖w‖≤2 by linarith) ep.le,cap]
  obtain ⟨w,wc,wz,ww,wr⟩ := find (Real.pi/4) quartic_dirs.1
  obtain ⟨y,yc,yz,yy,yr⟩ := find (3*Real.pi/4) quartic_dirs.2
  have trig (a : ℝ) : (dir a).re=Real.cos a ∧ (dir a).im=Real.sin a := by
    change (Complex.exp (↑a*Complex.I)).re=_ ∧ (Complex.exp (↑a*Complex.I)).im=_
    simp [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have wr1 := abs_le.mp ((abs_re_le_norm _).trans ww)
  have wi1 := abs_le.mp ((abs_im_le_norm _).trans ww)
  have yr1 := abs_le.mp ((abs_re_le_norm _).trans yy)
  have yi1 := abs_le.mp ((abs_im_le_norm _).trans yy)
  rw [sub_re,(trig _).1,Real.cos_pi_div_four] at wr1
  rw [sub_im,(trig _).2,Real.sin_pi_div_four] at wi1
  rw [sub_re,(trig _).1,show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.cos_pi_div_four] at yr1
  rw [sub_im,(trig _).2,show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.sin_pi_sub,Real.sin_pi_div_four] at yi1
  have rt : 1<Real.sqrt 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have tr : 0<((e:ℂ)*w).re := by rw [re_ofReal_mul];exact mul_pos ep (by linarith [wr1.1])
  have ti : 0<((e:ℂ)*w).im := by rw [im_ofReal_mul];exact mul_pos ep (by linarith [wi1.1])
  have sr : ((e:ℂ)*y).re<0 := by rw [re_ofReal_mul];exact mul_neg_of_pos_of_neg ep (by linarith [yr1.2])
  have si : 0<((e:ℂ)*y).im := by rw [im_ofReal_mul];exact mul_pos ep (by linarith [yi1.1])
  have no {Z V : ℂ} (a : 0<Z.im) (b : 0<V.im) : Z≠star V := by
    intro hz;rw [hz] at a;change 0< -V.im at a;linarith
  refine ⟨w,y,?_,?_,wc,yc⟩
  · obtain E|E|E|E := pol.exhaustive _ wr wz
    · exact E.symm
    · exact (no ti pol.upperRight E).elim
    · rw [E] at tr;linarith [pol.left]
    · exact (no ti pol.upperLeft E).elim
  · obtain E|E|E|E := pol.exhaustive _ yr yz
    · rw [E] at sr;linarith [pol.right]
    · exact (no si pol.upperRight E).elim
    · exact E.symm
    · exact (no si pol.upperLeft E).elim

#print axioms small_pair
end OrderedPartitions.FourPole.SixIntervals
