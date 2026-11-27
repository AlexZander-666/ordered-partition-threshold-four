import OrderedPartitions.FourPolePolynomialError
import OrderedPartitions.FourPoleDiskCheck

/-! Each finite rational comparison places a zero of the real-parameter
scaled fourth-threshold denominator in the stated complex disk. -/
noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex Finset Metric

private theorem gaussian_scale (a : ℚ) (u : ℚ×ℚ) :
    gaussian (a*u.1,a*u.2)=(a:ℂ)*gaussian u := by
  apply Complex.ext <;> simp [gaussian,Complex.mul_re,Complex.mul_im]
private theorem gaussian_sum {ι : Type*} (s : Finset ι) (v : ι→ℚ×ℚ) :
    gaussian (∑ i∈s,v i)=∑ i∈s,gaussian (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [gaussian]
  | @insert a s ha ih =>
    rw [sum_insert ha,sum_insert ha,←ih]
    apply Complex.ext <;> simp [gaussian,Complex.add_re,Complex.add_im]
private theorem gaussian_pow (D : Disc) (i : ℕ) : gaussian (ratPower D i)=center D^i := by
  induction i with
  | zero => simp [ratPower,gaussian]
  | succ i ih =>
    rw [pow_succ,←ih]
    apply Complex.ext <;> simp [gaussian,ratPower,center,Complex.mul_re,Complex.mul_im]
private theorem cast_poly (e : ℚ) (i : ℕ) :
    (polyCoeff e i:ℝ)=activeCoeff (e:ℝ) i := by
  unfold polyCoeff activeCoeff
  split_ifs <;> push_cast <;> rfl
private theorem ratShift_true (D : Disc) (e : ℚ) (h : ℕ) :
    gaussian (ratShift D e h) =
    PolynomialDisk.shift 29 (fun i ↦ (activeCoeff (e:ℝ) i:ℂ)) (center D) h := by
  unfold ratShift PolynomialDisk.shift
  rw [gaussian_sum]
  apply sum_congr rfl
  intro i _
  dsimp only
  rw [gaussian_scale,gaussian_pow,←cast_poly]
  push_cast
  rfl
private theorem normShift (D : Disc) (e : ℚ) (h : ℕ) :
    ‖gaussian (ratShift D e h)‖ ≤ (upperShift D e h:ℝ) := by
  simpa [gaussian,upperShift] using norm_le_abs_re_add_abs_im (gaussian (ratShift D e h))
private theorem swing_cast (lo hi e : ℚ) (i : ℕ) :
    (ratSwing lo hi e i:ℝ)=swing (lo:ℝ) (hi:ℝ) (e:ℝ) i := by
  unfold ratSwing swing powerSwing
  split_ifs <;> push_cast <;> rfl

/-- The full closed epsilon cell, including either endpoint. No assumption
on the location of a zero or on any derivative is needed. -/
theorem real_disk_zero {cell : Cell} {D : Disc} {cap L : ℚ} (ok : flatDisk cell D cap L)
    {e : ℝ} (low : (cell.lo:ℝ)≤e) (high : e≤(cell.hi:ℝ)) :
    ∃ z ∈ ball (center D) (D.r:ℝ), scaledG e z=0 := by
  let mid := (cell.lo+cell.hi)/2
  let W := cap+D.r
  obtain ⟨rad,cpos,csq,wle,lp,lh,hh,mp,mn,lpos,lsq,budget⟩ := ok
  have rpos : 0<(D.r:ℝ) := by exact_mod_cast rad
  have lpos' : 0<(cell.lo:ℝ) := by exact_mod_cast lp
  have he := lpos'.trans_le low
  have capSq : (D.x:ℝ)^2+(D.y:ℝ)^2≤(cap:ℝ)^2 := by exact_mod_cast csq
  have capPos : 0<(cap:ℝ) := by exact_mod_cast cpos
  have nrm : ‖center D‖^2=(D.x:ℝ)^2+(D.y:ℝ)^2 := by
    rw [Complex.sq_norm];simp [center,Complex.normSq,pow_two]
  have ccap : ‖center D‖≤(cap:ℝ) := by nlinarith [norm_nonneg (center D)]
  have cw : ‖center D‖+(D.r:ℝ)≤(W:ℝ) := by push_cast [W];linarith
  have wsmall : (W:ℝ)≤2 := by exact_mod_cast wle
  have esmall : e≤6/5 := by
    have hh' : (cell.hi:ℝ)≤((6/5:ℚ):ℝ) := by exact_mod_cast hh
    norm_num at hh';exact high.trans hh'
  have midLo : cell.lo≤mid := by dsimp [mid];linarith
  have midHi : mid≤cell.hi := by dsimp [mid];linarith
  apply PolynomialDisk.contains_zero mn mp rpos cw (fun i ↦ (activeCoeff e i:ℂ))
    (fun i ↦ (activeCoeff (mid:ℝ) i:ℂ)) (fun i ↦ (ratSwing cell.lo cell.hi mid i:ℝ))
  · intro i _
    rw [swing_cast]
    exact actual_swing lpos'.le low high (by exact_mod_cast midLo) (by exact_mod_cast midHi) i
  · unfold scaledG G
    fun_prop
  · intro z hz
    have zr : ‖z-center D‖=(D.r:ℝ) := by simpa [dist_eq_norm] using mem_sphere.mp hz
    have zw := norm_add_le (z-center D) (center D)
    rw [sub_add_cancel,zr] at zw
    have zsmall : ‖z‖≤2 := by linarith
    rw [polynomial_at_zero he]
    have bound := partialJet_bound he esmall zsmall (m:=0) (by decide)
    rw [iteratedDeriv_zero] at bound
    exact bound.trans (show _≤(jetTail cell.hi 0:ℝ) by unfold jetTail; push_cast; gcongr)
  · have midEq : mid=(cell.lo+cell.hi)/2 := rfl
    change jetTail cell.hi 0 + _ + _ < L*D.r^D.mode at budget
    have eb : (jetTail cell.hi 0:ℝ)+
        (∑ i∈range 29,(ratSwing cell.lo cell.hi mid i:ℝ)*(W:ℝ)^i) +
        (∑ i∈(range 29).erase D.mode,(upperShift D mid i:ℝ)*(D.r:ℝ)^i) <
        (L:ℝ)*(D.r:ℝ)^D.mode := by exact_mod_cast budget
    have lower : (L:ℝ)≤‖gaussian (ratShift D mid D.mode)‖ := by
      let p := ratShift D mid D.mode
      have s : (L:ℝ)^2≤(p.1:ℝ)^2+(p.2:ℝ)^2 := by exact_mod_cast lsq
      have sq : ‖gaussian p‖^2=(p.1:ℝ)^2+(p.2:ℝ)^2 := by
        rw [Complex.sq_norm];simp [gaussian,Complex.normSq,pow_two]
      nlinarith [norm_nonneg (gaussian p)]
    simp_rw [←ratShift_true]
    apply lt_of_le_of_lt _ (eb.trans_le (mul_le_mul_of_nonneg_right lower (pow_nonneg rpos.le _)))
    gcongr with i _
    exact normShift D mid i

#print axioms real_disk_zero
end OrderedPartitions.FourPole.Box
