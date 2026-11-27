import OrderedPartitions.ThreePoleDiskExistence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Rouché by a finite polynomial translation with independent coefficient perturbations. -/
noncomputable section
namespace OrderedPartitions.PolynomialDisk
open Finset Complex Metric Set

def eval (N : ℕ) (a : ℕ→ℂ) (z : ℂ) := ∑ i∈range N,a i*z^i
def shift (N : ℕ) (a : ℕ→ℂ) (c : ℂ) (h : ℕ) :=
  ∑ i∈range N,a i*(i.choose h:ℂ)*c^(i-h)

theorem translate (N : ℕ) (a : ℕ→ℂ) (c s : ℂ) :
    eval N a (c+s) = ∑ h∈range N,shift N a c h*s^h := by
  unfold eval shift
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have le : range (i+1) ⊆ range N := range_mono (mem_range.mp hi)
  have restr : (∑ h∈range (i+1), a i*(i.choose h:ℂ)*c^(i-h)*s^h) =
      ∑ h∈range N,a i*(i.choose h:ℂ)*c^(i-h)*s^h := by
    apply sum_subset le
    intro h _ hh
    have : i<h := by simp only [Finset.mem_range,not_lt] at hh; omega
    simp [Nat.choose_eq_zero_of_lt this]
  rw [← restr,add_comm c s,add_pow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- A certified disk contains a zero of the true holomorphic function. The
same assumptions give the pointwise strict dominance on its full boundary. -/
theorem dominance {N m : ℕ} (hm : m<N) {c : ℂ} {r W tail : ℝ} (_hr : 0<r)
    (wc : ‖c‖+r≤W) (a b : ℕ→ℂ) (v : ℕ→ℝ) (coeff : ∀ i<N, ‖a i-b i‖≤v i)
    (G : ℂ→ℂ) (truncation : ∀ z∈sphere c r, ‖G z-eval N a z‖≤tail)
    (budget : tail+∑ i∈range N,v i*W^i +
      ∑ h∈(range N).erase m, ‖shift N b c h‖*r^h < ‖shift N b c m‖*r^m)
    (z : ℂ) (hz : z∈sphere c r) :
    ‖G z-shift N b c m*(z-c)^m‖<‖shift N b c m*(z-c)^m‖ := by
  have zr : ‖z-c‖=r := by simpa [dist_eq_norm] using mem_sphere.mp hz
  have wz : ‖z‖≤W := by
    have t := norm_add_le (z-c) c
    rw [sub_add_cancel,zr] at t;linarith
  have var : ‖eval N a z-eval N b z‖ ≤ ∑ i∈range N,v i*W^i := by
    unfold eval
    rw [←Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (sum_le_sum fun i hi ↦ ?_)
    rw [←sub_mul,norm_mul,norm_pow]
    exact mul_le_mul (coeff i (mem_range.mp hi)) (pow_le_pow_left₀ (norm_nonneg _) wz i)
      (by positivity) ((norm_nonneg _).trans (coeff i (mem_range.mp hi)))
  have tr : eval N b z-shift N b c m*(z-c)^m =
      ∑ h∈(range N).erase m,shift N b c h*(z-c)^h := by
    have eqn := translate N b c (z-c)
    rw [add_sub_cancel] at eqn
    rw [eqn]
    exact sub_eq_of_eq_add (Finset.sum_erase_add _ _ (mem_range.mpr hm)).symm
  rw [norm_mul,norm_pow,zr]
  apply lt_of_le_of_lt _ budget
  calc
    _ = ‖(G z-eval N a z + (eval N a z-eval N b z)) + (eval N b z-shift N b c m*(z-c)^m)‖ := by congr 1; ring
    _ ≤ (‖G z-eval N a z‖+‖eval N a z-eval N b z‖) + ‖eval N b z-shift N b c m*(z-c)^m‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by
      rw [tr]
      refine add_le_add (add_le_add (truncation z hz) var) ?_
      simpa only [norm_mul,norm_pow,zr] using norm_sum_le ((range N).erase m)
        (fun h ↦ shift N b c h*(z-c)^h)

theorem contains_zero {N m : ℕ} (hm : m<N) (mp : 0<m) {c : ℂ} {r W tail : ℝ} (hr : 0<r)
    (wc : ‖c‖+r≤W) (a b : ℕ→ℂ) (v : ℕ→ℝ) (coeff : ∀ i<N, ‖a i-b i‖≤v i)
    (G : ℂ→ℂ) (hg : Differentiable ℂ G)
    (truncation : ∀ z∈sphere c r, ‖G z-eval N a z‖≤tail)
    (budget : tail+∑ i∈range N,v i*W^i +
      ∑ h∈(range N).erase m, ‖shift N b c h‖*r^h < ‖shift N b c m‖*r^m) :
    ∃ z∈ball c r, G z=0 := by
  apply ThreePole.exists_zero_of_boundary_dominance hr hg
    (P:=fun z ↦ shift N b c m*(z-c)^m) (by fun_prop) (by simp [mp.ne'])
  exact dominance hm hr wc a b v coeff G truncation budget

#print axioms dominance
#print axioms contains_zero
end OrderedPartitions.PolynomialDisk
