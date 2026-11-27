import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The positive critical point for the nearest-root limit of the ordered rows. -/
noncomputable section
namespace OrderedPartitions.CriticalEdge
open Finset Set
def tap (n : ℕ) (x : ℝ) := x^n/(n.factorial:ℝ)
def tail (n : ℕ) (x : ℝ) := Real.exp x - ∑ k ∈ range n, tap k x
theorem tail_succ (n : ℕ) (x : ℝ) : tail (n+1) x = tail n x - tap n x := by
  simp only [tail,sum_range_succ]; ring
theorem tap_deriv (n : ℕ) (x : ℝ) : HasDerivAt (tap (n+1)) (tap n x) x := by
  have d := (hasDerivAt_pow (n+1) x).div_const (((n+1).factorial):ℝ)
  change HasDerivAt (fun y : ℝ ↦ y^(n+1)/((n+1).factorial:ℝ)) _ x
  apply d.congr_deriv
  unfold tap
  rw [Nat.factorial_succ,Nat.cast_mul]
  simp only [Nat.add_sub_cancel]
  field_simp
theorem tail_deriv (n : ℕ) (x : ℝ) : HasDerivAt (tail (n+1)) (tail n x) x := by
  induction n with
  | zero =>
    rw [show tail (0+1) = fun y ↦ Real.exp y-1 by funext y; simp [tail,tap]]
    simpa only [tail,range_zero,sum_empty,sub_zero] using (Real.hasDerivAt_exp x).sub_const 1
  | succ n ih =>
    rw [show tail (n+1+1) = fun y ↦ tail (n+1) y - tap (n+1) y from funext (tail_succ _)]
    simpa [tail_succ n x,Pi.sub_def] using ih.sub (tap_deriv n x)
theorem tail_pos (n : ℕ) {x : ℝ} (hx : 0<x) : 0<tail n x := by
  have h := Real.sum_le_exp_of_nonneg hx.le (n+1)
  rw [sum_range_succ] at h
  change 0 < Real.exp x - ∑ k ∈ range n,x^k/(k.factorial:ℝ)
  linarith [show 0<x^n/(n.factorial:ℝ) by positivity]

/-- Here j=k+2 and the sign of the derivative of (exp x−2)/tail j x
is the sign of this exponentially weighted numerator. -/
def criticalTest (k : ℕ) (x : ℝ) :=
  Real.exp (-x) * (2*tail (k+2) x - (Real.exp x-2)*tap (k+1) x)
theorem criticalTest_deriv (k : ℕ) (x : ℝ) :
    HasDerivAt (criticalTest k) (-(Real.exp (-x)*(Real.exp x-2)*tap k x)) x := by
  have d := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).mul
    (((tail_deriv (k+1) x).const_mul 2).sub (((Real.hasDerivAt_exp x).sub_const 2).mul (tap_deriv k x)))
  change HasDerivAt (fun y ↦ Real.exp (-y) * (2*tail (k+2) y - (Real.exp y-2)*tap (k+1) y)) _ x
  apply d.congr_deriv
  simp only [Function.comp_apply,tail_succ (k+1) x,Pi.sub_apply,Pi.mul_apply]
  ring
theorem criticalTest_strictAnti (k : ℕ) :
    StrictAntiOn (criticalTest k) (Ici (Real.log 2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _) (fun x _ ↦ (criticalTest_deriv k x).continuousAt.continuousWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  have hlog : Real.log 2 < x := hx
  have hp : 0<x := lt_trans (Real.log_pos (by norm_num)) hlog
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (by norm_num)] at he
  rw [(criticalTest_deriv k x).deriv]
  unfold tap
  exact neg_neg_of_pos (mul_pos (mul_pos (Real.exp_pos _) (sub_pos.mpr he)) (by positivity))

theorem criticalTest_at_log (k : ℕ) : 0<criticalTest k (Real.log 2) := by
  simp only [criticalTest,Real.exp_log (by norm_num : (0:ℝ)<2),sub_self,zero_mul,sub_zero]
  exact mul_pos (Real.exp_pos _) (mul_pos (by norm_num) (tail_pos _ (Real.log_pos (by norm_num))))

#print axioms criticalTest_deriv
#print axioms criticalTest_strictAnti

theorem criticalTest_at_one {k : ℕ} (hk : 2 ≤ k) : criticalTest k 1 < 0 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have ef : (0:ℝ)<((k+1).factorial:ℝ) := by positivity
  have hb := Real.exp_bound' (x:=1) (n:=k+2) (by norm_num) le_rfl (by omega)
  have bound : tail (k+2) 1 ≤ ((k:ℝ)+3)/((((k+2).factorial):ℝ)*((k:ℝ)+2)) := by
    unfold tail tap
    simp only [one_pow,one_mul,Nat.cast_add,Nat.cast_ofNat] at hb ⊢
    rw [show (k:ℝ)+2+1=k+3 by ring] at hb
    linarith
  have fac : (((k+2).factorial):ℝ)=((k:ℝ)+2)*((k+1).factorial:ℝ) := by
    rw [Nat.factorial_succ,Nat.cast_mul];push_cast;ring
  rw [fac] at bound
  have hdiv := (le_div_iff₀ (by positivity)).mp bound
  have tbound : 2*tail (k+2) 1*((k+1).factorial:ℝ) ≤ 5/8 := by
    apply le_of_mul_le_mul_right (a:=((k:ℝ)+2)^2) (by nlinarith [hdiv,mul_nonneg (show 0≤(k:ℝ)-2 by linarith) (show 0≤5*(k:ℝ)+14 by positivity)]) (by positivity)
  have he : (5:ℝ)/8<Real.exp 1-2 := by linarith [Real.exp_one_gt_d9]
  apply mul_neg_of_pos_of_neg (Real.exp_pos _) (sub_neg.mpr ?_)
  simp only [tap,one_pow,mul_one_div]
  exact (lt_div_iff₀ ef).mpr (tbound.trans_lt he)

/-- The positive stationary point is unique to the right of log 2 and lies below one. -/
theorem unique_critical {k : ℕ} (hk : 2≤k) :
    ∃ a : ℝ, Real.log 2<a ∧ a<1 ∧ criticalTest k a=0 ∧
      ∀ b, Real.log 2≤b → criticalTest k b=0 → b=a := by
  have lo : Real.log 2<1 := by linarith [Real.log_two_lt_d9]
  have h := intermediate_value_Icc' lo.le
    (f:=criticalTest k) (fun x _ ↦ (criticalTest_deriv k x).continuousAt.continuousWithinAt)
    (show (0:ℝ)∈Icc (criticalTest k 1) (criticalTest k (Real.log 2)) from
      ⟨(criticalTest_at_one hk).le,(criticalTest_at_log k).le⟩)
  obtain ⟨a,ha,z⟩ := h
  refine ⟨a,lt_of_le_of_ne ha.1 ?_,lt_of_le_of_ne ha.2 ?_,z,?_⟩
  · rintro rfl; linarith [criticalTest_at_log k]
  · rintro rfl; linarith [criticalTest_at_one hk]
  · intro b hb zb
    exact (criticalTest_strictAnti k).injOn hb ha.1 (zb.trans z.symm)

def ratio (k : ℕ) (x : ℝ) := (Real.exp x-2)/tail (k+2) x

theorem ratio_deriv {x : ℝ} (hx : 0<x) (k : ℕ) :
    HasDerivAt (ratio k) (Real.exp x*criticalTest k x / (tail (k+2) x)^2) x := by
  have h := ((Real.hasDerivAt_exp x).sub_const 2).div (tail_deriv (k+1) x) (tail_pos _ hx).ne'
  apply h.congr_deriv
  unfold criticalTest
  rw [←mul_assoc,←Real.exp_add,add_neg_cancel,Real.exp_zero,one_mul,tail_succ (k+1) x]
  ring

#print axioms unique_critical
#print axioms ratio_deriv

private theorem ratio_one_gt {k : ℕ} (hk : 2≤k) : 1<ratio k 1 := by
  have subs : range 3 ⊆ range (k+2) := range_mono (by omega)
  have lower := sum_le_sum_of_subset_of_nonneg (f:=fun i : ℕ ↦ tap i 1) subs
    (fun i _ _ ↦ by unfold tap; positivity)
  have small : (∑ i ∈ range 3,tap i 1) = 5/2 := by norm_num [sum_range_succ,tap,Nat.factorial]
  rw [small] at lower
  apply (lt_div_iff₀ (tail_pos (k+2) (by norm_num : (0:ℝ)<1))).mpr
  unfold tail
  linarith

/-- The unique maximizer and the global strict maximum value exceed the
unmarked singularity log 2 and the parameter radius one, respectively. -/
theorem strict_maximum {k : ℕ} (hk : 2≤k) :
    ∃ a : ℝ, Real.log 2<a ∧ a<1 ∧ criticalTest k a=0 ∧ 1<ratio k a ∧
      ∀ x : ℝ, 0<x → x≠a → ratio k x < ratio k a := by
  obtain ⟨a,ha,a1,zero,_⟩ := unique_critical hk
  have rho : 0<Real.log 2 := Real.log_pos (by norm_num)
  have cont (x : ℝ) (hx : 0<x) := (ratio_deriv hx k).continuousAt
  have up : StrictMonoOn (ratio k) (Icc (Real.log 2) a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun x hx ↦ (cont x (rho.trans_le hx.1)).continuousWithinAt)
    intro x hx
    rw [interior_Icc] at hx
    have turn := criticalTest_strictAnti k (show x∈Ici (Real.log 2) from hx.1.le) ha.le hx.2
    rw [zero] at turn
    rw [(ratio_deriv (rho.trans hx.1) k).deriv]
    exact div_pos (mul_pos (Real.exp_pos _) turn) (sq_pos_of_pos (tail_pos _ (rho.trans hx.1)))
  have down : StrictAntiOn (ratio k) (Ici a) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici _) (fun x hx ↦ (cont x ((rho.trans ha).trans_le hx)).continuousWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    have turn := criticalTest_strictAnti k ha.le (show x∈Ici (Real.log 2) from ha.le.trans hx.le) hx
    rw [zero] at turn
    rw [(ratio_deriv ((rho.trans ha).trans hx) k).deriv]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (Real.exp_pos _) turn)
      (sq_pos_of_pos (tail_pos _ ((rho.trans ha).trans hx)))
  have height := (ratio_one_gt hk).trans (down (show a∈Ici a from (le_rfl : a≤a)) a1.le a1)
  refine ⟨a,ha,a1,zero,height,?_⟩
  intro x xpos ne
  rcases lt_or_gt_of_ne ne with xa|ax
  · by_cases lo : Real.log 2≤x
    · exact up ⟨lo,xa.le⟩ ⟨ha.le,le_rfl⟩ xa
    · have ex : Real.exp x<2 := by
        simpa only [Real.exp_log (by norm_num : (0:ℝ)<2)] using Real.exp_lt_exp.mpr (lt_of_not_ge lo)
      exact (div_neg_of_neg_of_pos (sub_neg.mpr ex) (tail_pos _ xpos)).trans (by linarith)
  · exact down (show a∈Ici a from (le_rfl : a≤a)) ax.le ax

#print axioms strict_maximum

def den (k : ℕ) (s x : ℝ) := 2-Real.exp x+s*tail (k+2) x
def slope (k : ℕ) (s x : ℝ) := -Real.exp x+s*tail (k+1) x
def curvature (k : ℕ) (s x : ℝ) := -Real.exp x+s*tail k x

theorem den_deriv (k : ℕ) (s x : ℝ) : HasDerivAt (den k s) (slope k s x) x := by
  change HasDerivAt (fun y ↦ 2-Real.exp y+s*tail (k+2) y) _ x
  simpa only [den,slope,Pi.add_def,Pi.sub_def,zero_sub] using
    (((hasDerivAt_const x (2:ℝ)).sub (Real.hasDerivAt_exp x)).add ((tail_deriv (k+1) x).const_mul s))
theorem slope_deriv (k : ℕ) (s x : ℝ) : HasDerivAt (slope k s) (curvature k s x) x := by
  change HasDerivAt (fun y ↦ -Real.exp y+s*tail (k+1) y) _ x
  simpa only [slope,curvature,Pi.add_def,Pi.neg_def] using
    ((Real.hasDerivAt_exp x).neg.add ((tail_deriv k x).const_mul s))

theorem critical_contact (k : ℕ) {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) :
    den k (ratio k a) a=0 ∧ slope k (ratio k a) a=0 ∧
    curvature k (ratio k a) a=ratio k a*tap k a := by
  have hne := (tail_pos (k+2) ha).ne'
  unfold criticalTest at hz
  have turn := (mul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'
  have contact : ratio k a*tail (k+2) a=Real.exp a-2 := by
    unfold ratio
    field_simp
  have zero : slope k (ratio k a) a=0 := by
    unfold slope ratio
    field_simp [hne]
    rw [tail_succ (k+1) a] at turn ⊢
    linarith only [turn]
  refine ⟨by unfold den;rw [contact];ring,zero,?_⟩
  unfold slope at zero
  unfold curvature
  rw [tail_succ k a] at zero
  linarith only [zero]

#print axioms critical_contact

theorem critical_ratio {k : ℕ} {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) :
    ratio k a=2*((k+1).factorial:ℝ)/a^(k+1) := by
  have ht := (tail_pos (k+2) ha).ne'
  unfold criticalTest at hz
  have eq := (mul_eq_zero.mp hz).resolve_left (Real.exp_pos _).ne'
  unfold tap at eq
  unfold ratio
  field_simp [ha.ne',ht] at eq ⊢
  linarith only [eq]

theorem critical_curvature {k : ℕ} {a : ℝ} (ha : 0<a) (hz : criticalTest k a=0) :
    curvature k (ratio k a) a=2*((k:ℝ)+1)/a := by
  rw [(critical_contact k ha hz).2.2,critical_ratio ha hz]
  unfold tap
  rw [Nat.factorial_succ,Nat.cast_mul,pow_succ]
  push_cast
  field_simp

#print axioms critical_ratio
#print axioms critical_curvature
end OrderedPartitions.CriticalEdge
