import OrderedPartitions.FinitePoleCircle
import OrderedPartitions.FourPoleOriginalTaylor
import OrderedPartitions.FourPoleCornerSign

/-! The actual fourth-threshold row with two conjugate pairs inside a circle. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex
open scoped ComplexConjugate

structure CirclePoles (q R : ℝ) (z v : ℂ) : Prop where
  right : 0<z.re
  left : v.re<0
  upperRight : 0<z.im
  upperLeft : 0<v.im
  radiusRight : ‖z‖<R
  radiusLeft : ‖v‖<R
  zeroRight : G q z=0
  zeroLeft : G q v=0
  simpleRight : first q z≠0
  simpleLeft : first q v≠0
  exhaustive : ∀ w : ℂ, ‖w‖≤R → G q w=0 → w=z ∨ w=star z ∨ w=v ∨ w=star v

def principal (n : ℕ) (q : ℝ) (z : ℂ) : ℂ := (first q z)⁻¹/z^(n+1)
def polarMass (n : ℕ) (q : ℝ) (z : ℂ) : ℝ := ‖first q z‖*‖z‖^(n+1)/2
def polarPhase (n : ℕ) (q : ℝ) (z : ℂ) : ℝ := ((n+1:ℕ):ℝ)*z.arg+(first q z).arg
def circleError (n : ℕ) (q R : ℝ) (z : ℂ) : ℝ :=
  polarMass n q z * (CriticalEdge.circleRemainder (G q) R n).re

private theorem not_conj {w : ℂ} (h : 0<w.im) : w≠star w := by
  intro e
  have eq := congrArg Complex.im e
  change w.im = -w.im at eq
  linarith
private theorem first_conj (q : ℝ) (w : ℂ) : first q (star w)=star (first q w) := by simp [first,exp_conj]
private theorem G_conj' (q : ℝ) (w : ℂ) : G q (star w)=star (G q w) := by simp [G,exp_conj]

theorem circle_residue_row {q R : ℝ} {z v : ℂ} (hq : q<1) (h : CirclePoles q R z v) (n : ℕ) :
    (row n 4).eval (-q/(1-q))/((1-q)*n.factorial) =
      (CriticalEdge.circleRemainder (G q) R n).re - 2*(principal n q z).re - 2*(principal n q v).re := by
  classical
  let S : Finset ℂ := {z, star z, v, star v}
  have site (w : ℂ) : w∈S ↔ w=z ∨ w=star z ∨ w=v ∨ w=star v := by simp [S]
  have zero (a : ℂ) (hp : 0<a.im) : a≠0 := fun e ↦ hp.ne' (by simp [e])
  have z0 := zero z h.upperRight
  have v0 := zero v h.upperLeft
  have loc : ∀ w∈S, ‖w‖<R ∧ w≠0 := by
    intro w hw
    rcases (site w).mp hw with rfl|rfl|rfl|rfl
    · exact ⟨h.radiusRight,z0⟩
    · simpa using And.intro h.radiusRight z0
    · exact ⟨h.radiusLeft,v0⟩
    · simpa using And.intro h.radiusLeft v0
  have roots : ∀ w∈S,G q w=0 := by
    intro w hw
    rcases (site w).mp hw with rfl|rfl|rfl|rfl
    · exact h.zeroRight
    · rw [G_conj',h.zeroRight,star_zero]
    · exact h.zeroLeft
    · rw [G_conj',h.zeroLeft,star_zero]
  have simple : ∀ w∈S,deriv (G q) w≠0 := by
    intro w hw
    rw [(hasDerivAt_G _ _).deriv]
    rcases (site w).mp hw with rfl|rfl|rfl|rfl
    · exact h.simpleRight
    · simpa only [first_conj,ne_eq,star_eq_zero] using h.simpleRight
    · exact h.simpleLeft
    · simpa only [first_conj,ne_eq,star_eq_zero] using h.simpleLeft
  have raw := FinitePoleCircle.coefficient (g:=G q) (fun w ↦ (hasDerivAt_G _ w).differentiableAt)
    ((norm_nonneg z).trans_lt h.radiusRight) S loc roots simple (fun w hw gz ↦ (site w).mpr (h.exhaustive w hw gz)) n
  unfold FinitePoleCircle.coeff at raw
  rw [iteratedDeriv_inv_G_at_zero hq] at raw
  have separate (a b : ℂ) (ha : 0<a.re) (hb : b.re<0) : a≠b :=
    by intro eqn; rw [eqn] at ha; linarith
  have sz : 0<(star z).re := h.right
  have sv : (star v).re<0 := h.left
  have sum : (∑ p∈S,(deriv (G q) p)⁻¹/p^(n+1)) =
      principal n q z+conj (principal n q z)+principal n q v+conj (principal n q v) := by
    have m₁ : z∉({star z,v,star v}:Finset ℂ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨not_conj h.upperRight,separate _ _ h.right h.left,separate _ _ h.right sv⟩
    have m₂ : star z∉({v,star v}:Finset ℂ) := by
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      exact ⟨separate _ _ sz h.left,separate _ _ sz sv⟩
    have m₃ : v∉({star v}:Finset ℂ) := by simpa only [Finset.mem_singleton] using not_conj h.upperLeft
    unfold S
    rw [Finset.sum_insert m₁,Finset.sum_insert m₂,Finset.sum_insert m₃,Finset.sum_singleton]
    simp only [(hasDerivAt_G _ _).deriv]
    rw [first_conj,first_conj]
    simp only [principal,map_div₀,
      map_pow,map_inv₀,Complex.star_def]
    ring
  rw [sum] at raw
  have lhs : Complex.ofReal ((row n 4).eval (-q/(1-q)))/((1-(q:ℂ))*(n.factorial:ℂ)) =
      (((row n 4).eval (-q/(1-q))/((1-q)*n.factorial):ℝ):ℂ) := by push_cast; rfl
  rw [lhs] at raw
  have re := congrArg Complex.re raw
  simp only [Complex.ofReal_re,Complex.add_re,Complex.sub_re,Complex.conj_re] at re
  linarith

theorem circle_error_bound {q R b : ℝ} (hr : 0<R) (hb : 0<b)
    (lower : ∀ w : ℂ, ‖w‖=R → b≤‖G q w‖) (n : ℕ) (z : ℂ) :
    |circleError n q R z| ≤ R/(2*b)*‖first q z‖*(‖z‖/R)^(n+1) := by
  have eb := (Complex.abs_re_le_norm _).trans (CriticalEdge.norm_circleRemainder_le hr hb lower n)
  unfold circleError polarMass
  rw [abs_mul,abs_of_nonneg (show 0≤‖first q z‖*‖z‖^(n+1)/2 by positivity)]
  calc
    _ ≤ (‖first q z‖*‖z‖^(n+1)/2)*(1/(b*R^n)) := by gcongr
    _ = _ := by rw [div_pow,pow_succ R]; field_simp

#print axioms circle_residue_row
#print axioms circle_error_bound
end OrderedPartitions.FourPole
