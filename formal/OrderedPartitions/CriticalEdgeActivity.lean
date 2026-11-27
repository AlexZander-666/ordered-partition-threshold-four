import OrderedPartitions.CriticalEdgeOriginal
import OrderedPartitions.CriticalEdgeCircle

/-! Common original-row Taylor normalization for all threshold pole models. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Finset
def poleDen (j : ℕ) (q z : ℂ) :=
  2*(1-q) - (∑ i ∈ range j,z^i/(i.factorial:ℂ)) + q*Complex.exp z

theorem generatingDen_eq (j : ℕ) (s z : ℂ) :
    generatingDen j s z = CriticalEdgeCircle.denominator j s z := rfl

theorem poleDen_normalization (j : ℕ) {q : ℂ} (hq : q≠1) (z : ℂ) :
    poleDen j q z=(1-q)*generatingDen j (1/(1-q)) z := by
  have nz : 1-q≠0 := sub_ne_zero.mpr hq.symm
  unfold poleDen generatingDen
  field_simp
  ring

theorem poleDen_coeff {j : ℕ} (hj : 1≤j) {q : ℂ} (hq : q≠1) (n : ℕ) :
    iteratedDeriv n (fun z ↦ (poleDen j q z)⁻¹) 0/(n.factorial:ℂ) =
    (row n j).eval₂ ofRealHom (-q/(1-q))/((1-q)*(n.factorial:ℂ)) := by
  have nz : 1-q≠0 := sub_ne_zero.mpr hq.symm
  have funEq : (fun z ↦ (poleDen j q z)⁻¹) =
      fun z ↦ (1-q)⁻¹*(generatingDen j (1/(1-q)) z)⁻¹ := by
    funext z
    rw [poleDen_normalization j hq,mul_inv_rev,mul_comm]
  have marker : 1-1/(1-q) = -q/(1-q) := by field_simp;ring
  rw [funEq, iteratedDeriv_const_mul_field, mul_div_assoc, inverse_den_coeff hj,marker]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

#print axioms poleDen_coeff
end OrderedPartitions.CriticalEdge
