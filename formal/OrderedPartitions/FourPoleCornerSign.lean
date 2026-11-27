import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic

/-! Signed four-step cancellation for two conjugate pairs in the fourth-threshold model. -/

namespace OrderedPartitions.FourPole
open Real

/-- Positive normalization, both pole pairs in their respective phases, and contour term. -/
noncomputable def model (ψ χ A E : ℝ) : ℝ := -cos ψ - A*cos χ + E

theorem old_cos {ψ χ A E : ℝ} (hz : model ψ χ A E = 0) (amplitude : |A| ≤ 29/100)
    (tail : |E| ≤ 1/100) : |cos ψ| ≤ 3/10 := by
  have eqn : cos ψ = -A*cos χ + E := by unfold model at hz; linarith
  rw [eqn]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul,abs_neg]
  linarith only [mul_le_mul_of_nonneg_left (abs_cos_le_one χ) (abs_nonneg A),amplitude,tail]

private theorem sign_of_error {ψ s v : ℝ} (hs : 0<s) (hc : |cos ψ|≤3/10)
    (err : |v-sin ψ*s| ≤ 19/20*s) : 0 < sin ψ*v := by
  have c2 : cos ψ^2 ≤ (3/10:ℝ)^2 := by rw [← sq_abs]; gcongr
  have large : 19/20 < |sin ψ| := by
    by_contra! bad
    have s2 : sin ψ^2 ≤ (19/20:ℝ)^2 := by rw [← sq_abs]; gcongr
    linarith [sin_sq_add_cos_sq ψ]
  obtain ⟨lower,upper⟩ := abs_le.mp err
  rcases le_or_gt (sin ψ) 0 with negative|positive
  · rw [abs_of_nonpos negative] at large
    apply mul_pos_of_neg_of_neg (by linarith)
    linarith only [upper,mul_lt_mul_of_pos_right (show sin ψ < -(19/20) by linarith) hs]
  · rw [abs_of_pos positive] at large
    exact mul_pos positive (by linarith only [lower,mul_lt_mul_of_pos_right large hs])

/-- A fourth shift nearly negates the secondary oscillation, uniformly in its phase. -/
theorem secondary_cancellation (χ θ v : ℝ) :
    |v*cos (χ+4*θ)+cos χ| ≤ |v-1|+|4*θ-3*π| := by
  have flip : cos (χ+3*π) = -cos χ := by
    rw [show χ+3*π = ((χ+π)+π)+π by ring,cos_add_pi,cos_add_pi,cos_add_pi]
    ring
  have turn := abs_cos_sub_cos_le (χ+4*θ) (χ+3*π)
  rw [flip,sub_neg_eq_add,show (χ+4*θ)-(χ+3*π)=4*θ-3*π by ring] at turn
  rw [show v*cos (χ+4*θ)+cos χ = (v-1)*cos (χ+4*θ)+(cos (χ+4*θ)+cos χ) by ring]
  refine (abs_add_le _ _).trans (add_le_add ?_ turn)
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (abs_cos_le_one (χ+4*θ)) (abs_nonneg (v-1))

/-- The critical fourth shift uses both signed pole contributions at the same old root. -/
theorem fourth_sign {ψ χ θ φ v A E F : ℝ}
    (hz : model ψ χ A E=0) (amp : |A|≤29/100) (oldTail : |E|≤1/100)
    (hs : 0<sin (4*θ)) (mainShift : |1+cos (4*θ)| ≤ sin (4*θ)/40)
    (sideShift : |v^4-1|+|4*φ-3*π| ≤ (31/10)*sin (4*θ))
    (contours : |E|+|F| ≤ sin (4*θ)/50) :
    0 < sin ψ * model (ψ+4*θ) (χ+4*φ) (A*v^4) F := by
  have hc := old_cos hz amp oldTail
  apply sign_of_error hs hc
  have hmain : |-(1+cos (4*θ))*cos ψ| ≤ sin (4*θ)/40 := by
    rw [abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one ψ) (abs_nonneg _)).trans (by simpa using mainShift)
  have hside : |-A*(v^4*cos (χ+4*φ)+cos χ)| ≤ (29/100)*((31/10)*sin (4*θ)) := by
    rw [abs_mul,abs_neg]
    exact mul_le_mul amp ((secondary_cancellation χ φ _).trans sideShift) (abs_nonneg _) (by norm_num)
  have e : model (ψ+4*θ) (χ+4*φ) (A*v^4) F - sin ψ*sin (4*θ) =
      (-(1+cos (4*θ))*cos ψ) + (-A*(v^4*cos (χ+4*φ)+cos χ)) + (E+F) := by
    unfold model at hz ⊢
    rw [cos_add]
    linarith only [hz]
  rw [e]
  have err := (abs_add_le ((-(1+cos (4*θ))*cos ψ)+(-A*(v^4*cos (χ+4*φ)+cos χ))) (E+F)).trans (add_le_add (abs_add_le _ _) (abs_add_le E F))
  exact err.trans (by linarith only [hmain,hside,contours,hs])

/-- The other shifts are separated in phase and use the undifferenced new error. -/
theorem short_sign {ψ χ Θ Φ A B E F : ℝ} (hz : model ψ χ A E=0)
    (ao : |A|≤29/100) (an : |B|≤29/100) (eo : |E|≤1/100) (en : |F|≤1/100)
    (angle : 2/3 ≤ sin Θ) : 0 < sin ψ * model (ψ+Θ) (χ+Φ) B F := by
  have hc := old_cos hz ao eo
  apply sign_of_error (by linarith : 0<sin Θ) hc
  have one : |-(cos ψ*cos Θ)|≤3/10 := by
    rw [abs_neg,abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one Θ) (abs_nonneg _)).trans (by simpa using hc)
  have two : |-B*cos (χ+Φ)|≤29/100 := by
    rw [abs_mul,abs_neg]
    exact (mul_le_mul_of_nonneg_left (abs_cos_le_one _) (abs_nonneg _)).trans (by simpa using an)
  rw [show model (ψ+Θ) (χ+Φ) B F-sin ψ*sin Θ = -(cos ψ*cos Θ)+(-B*cos (χ+Φ))+F by
    unfold model; rw [cos_add]; ring]
  exact ((abs_add_le (-(cos ψ*cos Θ)+(-B*cos (χ+Φ))) F).trans (add_le_add (abs_add_le _ _) (le_refl _))).trans
    (by linarith only [one,two,en,angle])

#print axioms secondary_cancellation
#print axioms fourth_sign
#print axioms short_sign
end OrderedPartitions.FourPole
