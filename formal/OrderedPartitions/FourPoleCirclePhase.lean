import OrderedPartitions.FourPoleCircleModel

/-! Positive real normalization and the full fourth-threshold two-frequency row. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex

private theorem inverse_product_re {w z : ℂ} (wn : w ≠ 0) (zn : z ≠ 0) (m : ℕ) :
    ((w*z^m)⁻¹).re =
      Real.cos ((m:ℝ)*z.arg+w.arg) / (‖w‖*‖z‖^m) := by
  let s := ‖w‖*‖z‖^m
  have sp : 0 < s := mul_pos (norm_pos_iff.mpr wn) (pow_pos (norm_pos_iff.mpr zn) _)
  have zp : z^m = (↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I)) := by
    rw [Complex.exp_nat_mul, ← mul_pow, Complex.norm_mul_exp_arg_mul_I]
  have polar : w*z^m = (s:ℂ)*exp (↑((m:ℝ)*z.arg+w.arg)*I) := by
    calc
      w*z^m = (↑‖w‖:ℂ) * exp (↑w.arg*I) *
          ((↑‖z‖:ℂ)^m * exp ((m:ℂ)*(↑z.arg*I))) := by
            rw [Complex.norm_mul_exp_arg_mul_I, zp]
      _ = _ := by
        simp only [s, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_add,
          Complex.ofReal_natCast, add_mul, mul_assoc, Complex.exp_add]
        ring
  have re : (w*z^m).re = s * Real.cos ((m:ℝ)*z.arg+w.arg) := by
    rw [polar, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.exp_re]
    simp
  have norm_eq : ‖w*z^m‖ = s := by rw [norm_mul, norm_pow]
  rw [Complex.inv_re, Complex.normSq_eq_norm_sq, norm_eq, re]
  field_simp [sp.ne']
  dsimp [s]
  ring

def scaleRow (n : ℕ) (q : ℝ) (z : ℂ) : ℝ :=
  polarMass n q z / ((1-q)*(n.factorial:ℝ))

def secondaryWeight (n : ℕ) (q : ℝ) (z v : ℂ) : ℝ :=
  ‖first q z‖/‖first q v‖*(‖z‖/‖v‖)^(n+1)

theorem scaleRow_positive {q R : ℝ} {z v : ℂ} (hq : q<1) (h : CirclePoles q R z v) (n : ℕ) :
    0<scaleRow n q z := by
  have zn := norm_pos_iff.mpr (show z≠0 from fun e ↦ h.upperRight.ne' (by simp [e]))
  have sd := norm_pos_iff.mpr h.simpleRight
  unfold scaleRow polarMass
  exact div_pos (by positivity) (mul_pos (sub_pos.mpr hq) (by positivity))

theorem original_circle_model {q R : ℝ} {z v : ℂ} (hq : q<1) (h : CirclePoles q R z v) (n : ℕ) :
    scaleRow n q z*(row n 4).eval (-q/(1-q)) =
    model (polarPhase n q z) (polarPhase n q v) (secondaryWeight n q z v) (circleError n q R z) := by
  have zn : z≠0 := fun e ↦ h.upperRight.ne' (by simp [e])
  have vn : v≠0 := fun e ↦ h.upperLeft.ne' (by simp [e])
  have part (u : ℂ) (fu : first q u≠0) (nu : u≠0) :
      (principal n q u).re = Real.cos (polarPhase n q u)/(‖first q u‖*‖u‖^(n+1)) := by
    unfold principal
    rw [show (first q u)⁻¹/u^(n+1)=(first q u*u^(n+1))⁻¹ by simp [div_eq_mul_inv,mul_comm]]
    exact inverse_product_re fu nu _
  have re := circle_residue_row hq h n
  rw [part z h.simpleRight zn,part v h.simpleLeft vn] at re
  unfold scaleRow
  rw [div_mul_eq_mul_div, mul_div_assoc, re]
  unfold polarMass secondaryWeight circleError model
  unfold polarMass
  rw [div_pow]
  field_simp [norm_ne_zero_iff.mpr h.simpleRight,norm_ne_zero_iff.mpr h.simpleLeft,
    norm_ne_zero_iff.mpr zn,norm_ne_zero_iff.mpr vn]
  ring

#print axioms scaleRow_positive
#print axioms original_circle_model
end OrderedPartitions.FourPole
