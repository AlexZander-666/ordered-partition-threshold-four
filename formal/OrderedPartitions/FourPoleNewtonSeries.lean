import OrderedPartitions.FourPoleNewtonKernel
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

noncomputable section
namespace OrderedPartitions.ExpInterpolation
open Complex

/-- Complete homogeneous coefficient of degree n minus the interpolation order.
The zero extension in n makes the insertion recurrence free of divisions. -/
def word : ℕ → List ℂ → ℂ → ℂ
  | 0, [], _ => 1
  | 0, _::_, _ => 0
  | n+1, [], z => z^(n+1)
  | n+1, p::ps, z => p*word n (p::ps) z + word n ps z

@[simp] theorem word_nil (n : ℕ) (z : ℂ) : word n [] z=z^n := by
  cases n <;> simp [word]

theorem word_difference (n : ℕ) (ps : List ℂ) (a b : ℂ) :
    word n (ps++[a]) b*(b-a)=word n ps b-word n ps a := by
  induction n generalizing ps with
  | zero => cases ps <;> simp [word]
  | succ n ih =>
    cases ps with
    | nil =>
      have h := ih []
      simp only [List.nil_append,word_nil] at h
      simp only [List.nil_append,word,word_nil,pow_succ]
      linear_combination a*h
    | cons p ps =>
      simp only [List.cons_append,word]
      have h := ih (p::ps)
      simp only [List.cons_append] at h
      linear_combination p*h + ih ps

/-- Taylor series for the actual nested exponential integral at distinct nodes. -/
theorem kernel_series (ps : List ℂ) (distinct : ps.Nodup) (z : ℂ) (avoid : z∉ps) :
    HasSum (fun n : ℕ ↦ word n ps z/(n.factorial:ℂ)) (kernel ps z 1) := by
  induction ps using List.reverseRecOn generalizing z with
  | nil =>
    simpa [kernel,Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  | append_singleton ps a ih =>
    have dn := List.nodup_append.mp distinct
    have aout : a∉ps := fun h ↦ dn.2.2 a h a (by simp) rfl
    have zout : z∉ps := fun h ↦ avoid (List.mem_append_left _ h)
    have ne : z-a≠0 := sub_ne_zero.mpr fun e ↦ avoid (by simp [e])
    have h := ((ih dn.1 z zout).sub (ih dn.1 a aout)).div_const (z-a)
    rw [←last_difference ps a z 1,mul_div_cancel_right₀ _ ne] at h
    apply h.congr_fun
    intro n
    symm
    change (word n ps z/(n.factorial:ℂ)-word n ps a/(n.factorial:ℂ))/(z-a) = _
    rw [←sub_div,←word_difference]
    field_simp

/-- Translation identity for the actual kernel, including collisions of nodes. -/
theorem kernel_translate (ps : List ℂ) (z a : ℂ) (t : ℝ) :
    kernel (ps.map (fun p ↦ p+a)) (z+a) t=exp (a*t)*kernel ps z t := by
  induction ps generalizing t with
  | nil => simp only [List.map_nil,kernel,add_mul,exp_add];ring
  | cons p ps ih =>
    simp only [List.map_cons,kernel]
    have cancel (s : ℝ) : exp (-(p+a)*s)*kernel (ps.map (fun x ↦ x+a)) (z+a) s =
        exp (-p*s)*kernel ps z s := by
      rw [ih,←mul_assoc,←exp_add]
      congr 2
      ring
    simp_rw [cancel]
    rw [add_mul,exp_add]
    ring

/-- The combinatorial majorant has exactly the binomial normalization needed
to bound the entire exponential-series tail by an ordinary factorial tail. -/
theorem word_norm (n : ℕ) (ps : List ℂ) (z : ℂ) (M : ℝ) (hM : 0≤M)
    (bound : ∀ a∈ps, ‖a‖≤M) (hz : ‖z‖≤M) :
    ‖word n ps z‖ ≤ (n.choose ps.length:ℝ)*M^(n-ps.length) := by
  induction n generalizing ps with
  | zero => cases ps <;> simp [word]
  | succ n ih =>
    cases ps with
    | nil => simpa only [word_nil,List.length_nil,Nat.choose_zero_right,Nat.cast_one,
              one_mul,Nat.sub_zero,norm_pow] using pow_le_pow_left₀ (norm_nonneg z) hz (n+1)
    | cons a ps =>
      have hm := bound a (by simp)
      have hi := ih (a::ps) bound
      have hj := ih ps (fun b hb ↦ bound b (List.mem_cons_of_mem _ hb))
      simp only [List.length_cons] at hi ⊢
      rw [word,Nat.choose_succ_succ',Nat.cast_add,Nat.add_sub_add_right]
      have hp := mul_le_mul hm hi (norm_nonneg _) hM
      rw [←norm_mul] at hp
      have tri := (norm_add_le (a*word n (a::ps) z) (word n ps z)).trans (add_le_add hp hj)
      apply tri.trans
      by_cases h : ps.length+1≤n
      · rw [show n-ps.length=n-(ps.length+1)+1 by omega,pow_succ]
        apply le_of_eq
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega : n<ps.length+1)]
        simp

theorem normalized_word_bound (m : ℕ) (ps : List ℂ) (four : ps.length=4)
    (z : ℂ) (M : ℝ) (hM : 0≤M) (bound : ∀ a∈ps, ‖a‖≤M) (hz : ‖z‖≤M) :
    24*‖word (m+4) ps z/((m+4).factorial:ℂ)‖ ≤ M^m/(m.factorial:ℝ) := by
  have h := word_norm (m+4) ps z M hM bound hz
  rw [four,Nat.add_sub_cancel] at h
  have choose := Nat.choose_mul_factorial_mul_factorial (by omega : 4≤m+4)
  rw [Nat.add_sub_cancel] at choose
  have heq : ((m+4).choose 4:ℝ)*24*(m.factorial:ℝ)=(m+4).factorial := by
    norm_num [Nat.factorial] at choose
    exact_mod_cast choose
  rw [norm_div,Complex.norm_natCast,mul_div_assoc',div_le_div_iff₀ (by positivity) (by positivity)]
  calc
    _ ≤ 24*(((m+4).choose 4:ℝ)*M^m)*m.factorial := by gcongr
    _ = _ := by rw [←heq];ring

#print axioms normalized_word_bound
#print axioms kernel_series
#print axioms kernel_translate
end OrderedPartitions.ExpInterpolation
