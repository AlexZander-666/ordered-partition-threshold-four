import OrderedPartitions.OriginalEGF
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! The original ordered rows at any complex marker, including the critical scaling. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Complex Polynomial Finset
open scoped Topology
def complexRows (j : ℕ) (t : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n ↦ (row n j).eval₂ Complex.ofRealHom t / n.factorial)

private def markedSizes (j : ℕ) (t : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun r ↦ if r=0 then 0 else
    (r.factorial : ℂ)⁻¹ * t^(if j ≤ r then 1 else 0))

private theorem block_coeff (j N : ℕ) (t : ℂ) (S : PowerSeries ℂ) :
    PowerSeries.coeff N (markedSizes j t * S) =
      ∑ r ∈ Icc 1 N, (r.factorial : ℂ)⁻¹ * t^(if j ≤ r then 1 else 0) *
        PowerSeries.coeff (N-r) S := by
  rw [PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [markedSizes, PowerSeries.coeff_mk]
  symm
  apply sum_subset_zero_on_sdiff
  · intro r hr
    simpa only [mem_range, Nat.lt_succ_iff] using (mem_Icc.mp hr).2
  · intro r hr
    obtain ⟨hr,hn⟩ := mem_sdiff.mp hr
    have hN := Nat.le_of_lt_succ (mem_range.mp hr)
    have : r=0 := by by_contra! h; exact hn (mem_Icc.mpr ⟨by omega,hN⟩)
    simp [this]
  · intro r hr
    have h := (mem_Icc.mp hr).1
    simp [show r ≠ 0 by omega]

theorem complex_row_resolvent {j : ℕ} (hj : 1≤j) (t : ℂ) :
    complexRows j t=(1-markedSizes j t)⁻¹ := by
  symm
  apply (PowerSeries.inv_eq_iff_mul_eq_one (show
    PowerSeries.constantCoeff (1-markedSizes j t) ≠ 0 by simp [markedSizes])).mpr
  rw [mul_comm, sub_mul, one_mul]
  ext n
  rw [map_sub, block_coeff]
  cases n with
  | zero => simp [complexRows, row_zero hj]
  | succ n =>
    simp only [complexRows, PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero,
      if_false, sub_eq_zero]
    rw [row_recurrence n hj, eval₂_finsetSum, sum_div]
    apply sum_congr rfl
    intro r hr
    simp only [nsmul_eq_mul, eval₂_mul, eval₂_natCast, eval₂_pow, eval₂_X]
    rw [Nat.cast_choose ℂ (mem_Icc.mp hr).2]
    field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n+1))]

private def taylorAtZero (f : ℂ → ℂ) : PowerSeries ℂ :=
  PowerSeries.mk (fun n ↦ iteratedDeriv n f 0 / n.factorial)

private theorem coeff_taylorAtZero (f : ℂ → ℂ) (n : ℕ) :
    PowerSeries.coeff n (taylorAtZero f) = iteratedDeriv n f 0 / n.factorial := by
  simp [taylorAtZero]

private theorem taylor_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z ↦ f z * g z) = taylorAtZero f * taylorAtZero g := by
  ext n
  rw [coeff_taylorAtZero, PowerSeries.coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt, sum_div]
  apply sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (mem_range.mp hi)
  simp only [coeff_taylorAtZero]
  rw [Nat.cast_choose ℂ hin]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)]

private theorem taylor_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 0] g) :
    taylorAtZero f = taylorAtZero g := by
  ext n
  simp only [coeff_taylorAtZero, h.iteratedDeriv_eq n]

private theorem taylor_const_one : taylorAtZero (fun _ ↦ 1) = 1 := by
  ext n
  cases n <;> simp [coeff_taylorAtZero, PowerSeries.coeff_one, iteratedDeriv_const]


def generatingDen (j : ℕ) (s z : ℂ) :=
  2-Complex.exp z+s*(Complex.exp z-∑ i ∈ range j,z^i/(i.factorial:ℂ))

private theorem taylor_finite_exp (j : ℕ) :
    taylorAtZero (fun z ↦ ∑ i ∈ range j,z^i/(i.factorial:ℂ)) =
    PowerSeries.mk (fun n ↦ if n<j then (n.factorial:ℂ)⁻¹ else 0) := by
  ext n
  rw [coeff_taylorAtZero,PowerSeries.coeff_mk,iteratedDeriv_fun_sum (fun i _ ↦ by fun_prop)]
  simp only [iteratedDeriv_div_const,iteratedDeriv_fun_pow_zero]
  have pick (i : ℕ) : (if n=i then (i.factorial:ℂ) else 0)/(i.factorial:ℂ) =
      if n=i then 1 else 0 := by
    split <;> simp [Nat.factorial_ne_zero]
  push_cast
  simp_rw [pick]
  by_cases h : n<j
  · simp [h]
  · simp [h]

private theorem analytic_den (j : ℕ) (s : ℂ) (z : ℂ) : AnalyticAt ℂ (generatingDen j s) z := by
  unfold generatingDen
  fun_prop

private theorem taylor_den {j : ℕ} (hj : 1≤j) (s : ℂ) :
    taylorAtZero (generatingDen j s)=1-markedSizes j (1-s) := by
  ext n
  have finDer := congrArg (PowerSeries.coeff (R:=ℂ) n) (taylor_finite_exp j)
  rw [coeff_taylorAtZero,PowerSeries.coeff_mk] at finDer
  have ed : iteratedDeriv n Complex.exp 0=1 := by
    rw [iteratedDeriv_eq_iterate, Complex.iter_deriv_exp, Complex.exp_zero]
  rw [coeff_taylorAtZero,map_sub]
  unfold generatingDen
  rw [iteratedDeriv_fun_add (by fun_prop) (by fun_prop),iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),
      iteratedDeriv_const_mul_field,iteratedDeriv_fun_sub (by fun_prop) (by fun_prop),ed,iteratedDeriv_const]
  simp only [markedSizes,PowerSeries.coeff_mk,PowerSeries.coeff_one]
  by_cases z : n=0
  · subst n
    simp [show 0<j by omega] at finDer
    norm_num [finDer]
  · by_cases h : n<j
    · simp only [z,if_false,h,if_true,show ¬j≤n by omega,pow_zero,mul_one] at finDer ⊢
      linear_combination (norm := ring_nf) -s*finDer
    · simp only [z,if_false,h,show j≤n by omega,if_true,pow_one] at finDer ⊢
      linear_combination (norm := ring_nf) -s*finDer


private theorem den_zero_value {j : ℕ} (hj : 1≤j) (s : ℂ) : generatingDen j s 0=1 := by
  have v := congrArg (PowerSeries.coeff (R:=ℂ) 0) (taylor_den hj s)
  simpa [coeff_taylorAtZero,markedSizes] using v

/-- The Taylor coefficients of the inverse analytic denominator are the
true labelled ordered rows for every complex marker 1-s. -/
theorem inverse_den_coeff {j : ℕ} (hj : 1≤j) (s : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z ↦ (generatingDen j s z)⁻¹) 0 / (n.factorial:ℂ)
      = (row n j).eval₂ Complex.ofRealHom (1-s)/(n.factorial:ℂ) := by
  have nz := (den_zero_value hj s).trans_ne one_ne_zero
  have an : AnalyticAt ℂ (fun z ↦ (generatingDen j s z)⁻¹) 0 := (analytic_den j s 0).inv nz
  have eq : taylorAtZero (fun z ↦ (generatingDen j s z)⁻¹) = complexRows j (1-s) := by
    rw [complex_row_resolvent hj]
    refine (PowerSeries.eq_inv_iff_mul_eq_one (show PowerSeries.constantCoeff (1-markedSizes j (1-s))≠0 by simp [markedSizes])).mpr ?_
    rw [←taylor_den hj s,←taylor_mul an (analytic_den j s 0),←taylor_const_one]
    apply taylor_congr
    filter_upwards [(analytic_den j s 0).continuousAt.eventually_ne nz] with z hz
    exact inv_mul_cancel₀ hz
  simpa [coeff_taylorAtZero, complexRows] using congrArg (PowerSeries.coeff (R:=ℂ) n) eq

theorem inverse_den_series {j : ℕ} (hj : 1≤j) (s : ℂ) :
    HasFPowerSeriesAt (fun z ↦ (generatingDen j s z)⁻¹)
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦
        (row n j).eval₂ Complex.ofRealHom (1-s)/(n.factorial:ℂ)) 0 := by
  have an : AnalyticAt ℂ (fun z ↦ (generatingDen j s z)⁻¹) 0 := (analytic_den j s 0).inv ((den_zero_value hj s).trans_ne one_ne_zero)
  simpa only [inverse_den_coeff hj] using an.hasFPowerSeriesAt

#print axioms complex_row_resolvent
#print axioms inverse_den_coeff
#print axioms inverse_den_series
end OrderedPartitions.CriticalEdge
