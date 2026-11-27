import OrderedPartitions.FourPolePhysicalCorner
import OrderedPartitions.ThreePoleDiskExistence

/-! Coarse shrinking disks suffice for the full first-order polar response. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex Metric Set Filter Topology

def scaledG (e : ℝ) (w : ℂ) : ℂ := 24/(e:ℂ)^4 * G (1-e^4/24) ((e:ℂ)*w)

private theorem coarse {e : ℝ} (he : 0<e) (sm : e ≤ 1/2) {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ‖scaledG e w-(1+w^4)‖ ≤ 12*e := by
  let x : ℂ := (e:ℂ)*w
  have size : ‖x‖ ≤ 2*e := by
    change ‖(e:ℂ)*w‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
    linarith only [mul_le_mul_of_nonneg_left hw he.le]
  have X : ‖x‖ ≤ 1 := by linarith
  let P : ℂ := ∑ a ∈ Finset.range 5, x^a/a.factorial
  have idn : scaledG e w - (1+w^4) = 24/(e:ℂ)^4*(Complex.exp x-P)-(Complex.exp x-1) := by
    unfold scaledG G
    dsimp [P,x]
    push_cast
    norm_num [Finset.sum_range_succ,Nat.factorial]
    field_simp [show (e:ℂ) ≠ 0 by exact_mod_cast he.ne']
    ring
  have firstError : ‖Complex.exp x-P‖ ≤ (2*e)^5/100 := by
    have h := Complex.exp_bound (n:=5) X (by decide)
    norm_num [Nat.factorial] at h
    change ‖Complex.exp x-∑ a ∈ Finset.range 5, x^a/a.factorial‖ ≤ _
    have p : ‖x‖^5 ≤ (2*e)^5 := by gcongr
    linarith only [h,p]
  have secondError := Complex.norm_exp_sub_one_le X
  rw [idn]
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  norm_num only [Complex.norm_ofNat]
  have prod := mul_le_mul_of_nonneg_left firstError (show 0≤24/e^4 by positivity)
  have val : 24/e^4*((2*e)^5/100) = 192/25*e := by field_simp; ring
  rw [val] at prod
  linarith only [prod,secondError,size,he]

/-- For 0<epsilon≤1/100, each fourth root of -1 labels an actual
zero of the true scaled denominator within 10 epsilon. -/
theorem small_disk_zero {e : ℝ} (he : 0<e) (sm : e≤1/100) {ω : ℂ}
    (quartic : ω^4 = -1) (unit : ‖ω‖=1) :
    ∃ w : ℂ, ‖w-ω‖ < 10*e ∧ G (1-e^4/24) ((e:ℂ)*w)=0 := by
  let L (w : ℂ) := 4*ω^3*(w-ω)
  have diff : Differentiable ℂ (scaledG e) := by unfold scaledG G; fun_prop
  obtain ⟨w,inside,zero⟩ := ThreePole.exists_zero_of_boundary_dominance (G:=scaledG e) (P:=L)
    (c:=ω) (r:=10*e) (by positivity) diff (by dsimp [L]; fun_prop) (by simp [L]) (by
      intro z hz
      have h : ‖z-ω‖=10*e := by simpa [dist_eq_norm] using mem_sphere.mp hz
      have hw : ‖z‖≤2 := by
        have v := norm_add_le (z-ω) ω
        rw [sub_add_cancel,h,unit] at v
        linarith
      have rem := coarse he (by linarith) hw
      let y := z-ω
      have yn : ‖y‖=10*e := h
      have form : (1+z^4)-L z = 6*ω^2*y^2+4*ω*y^3+y^4 := by
        dsimp [y,L]
        linear_combination quartic
      have lin : ‖L z‖=40*e := by simp [L,norm_pow,unit,h]; ring
      rw [lin,show scaledG e z-L z=(scaledG e z-(1+z^4))+((1+z^4)-L z) by ring,form]
      apply lt_of_le_of_lt (norm_add_le _ _)
      have rest := (norm_add_le (6*ω^2*y^2+4*ω*y^3) (y^4)).trans
        (add_le_add (norm_add_le _ _) (le_refl _))
      simp only [norm_mul,norm_pow,Complex.norm_ofNat,unit,one_pow,mul_one,yn] at rest
      have y0 : 0≤10*e := by positivity
      have y1 : 10*e≤1/10 := by linarith
      have bound (a : ℕ) : (10*e)^(a+1) ≤ 10*e := by
        rw [pow_succ]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (pow_le_one₀ y0 (by linarith : 10*e≤1)) y0
      have improved (a : ℕ) : (10*e)^(a+2) ≤ e := by
        rw [show a+2=(a+1)+1 by omega,pow_succ]
        linarith only [mul_le_mul (bound a) y1 y0 y0]
      obtain ⟨e2,e3,e4⟩ : (10*e)^2≤e ∧ (10*e)^3≤e ∧ (10*e)^4≤e := ⟨improved 0,improved 1,improved 2⟩
      linarith only [rem,rest,e2,e3,e4,he])
  refine ⟨w,by simpa [dist_eq_norm] using mem_ball.mp inside,?_⟩
  exact (mul_eq_zero.mp zero).resolve_left (div_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast he.ne')))

#print axioms small_disk_zero
end OrderedPartitions.FourPole
