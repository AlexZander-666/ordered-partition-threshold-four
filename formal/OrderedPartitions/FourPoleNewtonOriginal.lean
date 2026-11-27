import OrderedPartitions.FourPoleNewtonKernel
import OrderedPartitions.FourPolePhysicalCompact

noncomputable section
namespace OrderedPartitions.ExpInterpolation
open Complex Polynomial

theorem joint_kernel (ps : List ℂ) : Continuous (fun p : ℂ×ℝ ↦ kernel ps p.1 p.2) := by
  induction ps with
  | nil => change Continuous (fun p : ℂ×ℝ ↦ exp (p.1*p.2));fun_prop
  | cons a ps ih =>
    change Continuous (fun p : ℂ×ℝ ↦ exp (a*p.2) * ∫ s in (0:ℝ)..p.2, exp (-a*s)*kernel ps p.1 s)
    apply Continuous.mul (by fun_prop)
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous _ continuous_snd
    change Continuous (fun u : (ℂ×ℝ)×ℝ ↦ exp (-a*(u.2:ℂ))*kernel ps u.1.1 u.2)
    exact Continuous.mul (by fun_prop) (ih.comp (continuous_fst.fst.prodMk continuous_snd))

private theorem reduce_zero (ps : List ℂ) : ps.foldl reduce 0=0 := by
  induction ps with
  | nil => rfl
  | cons a ps ih => simpa [List.foldl_cons,reduce] using ih
theorem reduced_below_length (ps : List ℂ) {p : ℂ[X]} (hp : p.natDegree<ps.length) :
    ps.foldl reduce p=0 := by
  induction ps generalizing p with
  | nil => simp at hp
  | cons a ps ih =>
    simp only [List.foldl_cons]
    by_cases h : p.natDegree=0
    · have small : p.degree<(X-C a).degree := lt_of_le_of_lt degree_le_natDegree (by simp [h])
      rw [reduce,(divByMonic_eq_zero_iff (monic_X_sub_C _)).mpr small,reduce_zero]
    · apply ih
      rw [reduce,natDegree_divByMonic _ (monic_X_sub_C _),natDegree_X_sub_C]
      simp only [List.length_cons] at hp
      omega

end OrderedPartitions.ExpInterpolation

namespace OrderedPartitions.FourPole
open Complex Polynomial ExpInterpolation

/-- The actual exponential-polynomial numerator factors exactly through the
order-four simplex integral. This uses only four distinct true zeros. -/
theorem four_zero_factorization {q : ℝ} (qp : 0<q) (ps : List ℂ) (four : ps.length=4)
    (dn : ps.Nodup) (hits : ∀ p∈ps,G q p=0) (z : ℂ) :
    G q z=(q:ℂ)*(ps.map (fun p ↦ z-p)).prod*kernel ps z 1 := by
  let P : ℂ[X] := C (q:ℂ)⁻¹*(C (2*(q:ℂ)-1)+X+C (1/2:ℂ)*X^2+C (1/6:ℂ)*X^3)
  have q0 : (q:ℂ)≠0 := by exact_mod_cast qp.ne'
  have eqn (w : ℂ) : G q w=(q:ℂ)*(exp w-P.eval w) := by
    unfold G
    simp only [P,eval_mul,eval_add,eval_C,eval_X,eval_pow]
    field_simp
    ring
  have hit : ∀ w∈ps,exp w=P.eval w := by
    intro w hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((eqn w).symm.trans (hits w hw))).resolve_left q0)
  have deg : P.natDegree≤3 := by dsimp [P];compute_degree
  have small := reduced_below_length ps (p:=P) (by omega)
  rw [eqn,interpolates P ps dn hit,small,eval_zero,sub_zero,mul_assoc]

#print axioms four_zero_factorization
end OrderedPartitions.FourPole
