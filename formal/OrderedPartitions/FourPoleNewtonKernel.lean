import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-! An elementary Hermite--Genocchi kernel without divisions by pole separation. -/
noncomputable section
namespace OrderedPartitions.ExpInterpolation
open Complex Polynomial MeasureTheory

/-- Time-ordered exponential integral with the last interpolation node free. -/
def kernel : List ℂ → ℂ→ℝ→ℂ
  | [], z, t => exp (z*t)
  | p::ps, z, t => exp (p*t) * ∫ s in (0:ℝ)..t, exp (-p*s) * kernel ps z s

theorem continuous_kernel (ps : List ℂ) (z : ℂ) : Continuous (kernel ps z) := by
  induction ps with
  | nil => change Continuous (fun t : ℝ ↦ exp (z*(t:ℂ)));fun_prop
  | cons p ps ih =>
    change Continuous (fun t : ℝ ↦ exp (p*(t:ℂ)) * ∫ s in (0:ℝ)..t, exp (-p*s) * kernel ps z s)
    apply Continuous.mul (by fun_prop)
    exact intervalIntegral.continuous_primitive
      (fun a b ↦ (Continuous.mul (by fun_prop) ih).intervalIntegrable a b) 0

/-- Appending either of two nodes gives the divided-difference recurrence. -/
theorem last_difference (ps : List ℂ) (a b : ℂ) (t : ℝ) :
    kernel (ps++[a]) b t*(b-a) = kernel ps b t-kernel ps a t := by
  by_cases ba : b=a
  · simp [ba]
  induction ps generalizing t with
  | nil =>
    have nz : b-a≠0 := sub_ne_zero.mpr ba
    simp only [List.nil_append,kernel]
    have prod (s : ℝ) : exp (-a*s)*exp (b*s)=exp ((b-a)*s) := by rw [←exp_add];congr 1;ring
    simp_rw [prod]
    rw [integral_exp_mul_complex nz]
    simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
    rw [mul_assoc,div_mul_cancel₀ _ nz,mul_sub,mul_one,←Complex.exp_add]
    congr 2
    ring
  | cons p ps ih =>
    simp only [List.cons_append,kernel]
    rw [mul_assoc,←intervalIntegral.integral_mul_const,←mul_sub]
    have ib (w : ℂ) : IntervalIntegrable (fun s : ℝ ↦ exp (-p*s)*kernel ps w s) volume 0 t :=
      (Continuous.mul (by fun_prop) (continuous_kernel ps w)).intervalIntegrable _ _
    rw [←intervalIntegral.integral_sub (ib b) (ib a)]
    congr 1
    apply intervalIntegral.integral_congr
    intro u _
    dsimp
    rw [mul_assoc,ih,mul_sub]

def reduce (p : ℂ[X]) (a : ℂ) := p /ₘ (X-C a)
private theorem reduce_eval (p : ℂ[X]) (a w : ℂ) :
    (w-a)*(reduce p a).eval w=p.eval w-p.eval a := by
  have h := X_sub_C_mul_divByMonic_eq_sub_modByMonic p a
  rw [modByMonic_X_sub_C_eq_C_eval] at h
  simpa [reduce] using congrArg (Polynomial.eval w) h

/-- Newton interpolation with an arbitrary finite list of prescribed exact hits.
The product formula holds even at one of the interpolation nodes. -/
theorem interpolates (p : ℂ[X]) (ps : List ℂ) (distinct : ps.Nodup)
    (hits : ∀ a∈ps, exp a=p.eval a) (w : ℂ) :
    exp w-p.eval w=(ps.map (fun a ↦ w-a)).prod *
      (kernel ps w 1-(ps.foldl reduce p).eval w) := by
  induction ps using List.reverseRecOn generalizing w with
  | nil => simp [kernel]
  | append_singleton ps a ih =>
    have dn := List.nodup_append.mp distinct
    have prev : ∀ c∈ps,exp c=p.eval c := fun c hc ↦ hits c (List.mem_append_left _ hc)
    have ha := hits a (by simp)
    have val := ih dn.1 prev a
    rw [ha,sub_self] at val
    have notmem : a∉ps := fun mem ↦ dn.2.2 a mem a (by simp) rfl
    have pn (xs : List ℂ) (avoid : a∉xs) : (xs.map (fun c ↦ a-c)).prod≠0 := by
      induction xs with
      | nil => simp
      | cons x xs hi =>
        simp only [List.mem_cons,not_or] at avoid
        simpa only [List.map_cons,List.prod_cons] using mul_ne_zero (sub_ne_zero.mpr avoid.1) (hi avoid.2)
    have prod := pn ps notmem
    have hit := sub_eq_zero.mp ((mul_eq_zero.mp val.symm).resolve_left prod)
    rw [ih dn.1 prev w]
    simp only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,
      mul_one,List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [mul_assoc]
    congr 1
    have d := last_difference ps a w 1
    have red := reduce_eval (ps.foldl reduce p) a w
    rw [hit] at d
    linear_combination -d+red

#print axioms last_difference
#print axioms interpolates
end OrderedPartitions.ExpInterpolation
