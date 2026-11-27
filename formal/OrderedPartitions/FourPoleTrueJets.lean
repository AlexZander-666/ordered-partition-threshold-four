import OrderedPartitions.FourPolePhysicalDisks
import OrderedPartitions.FourPoleJetReadout
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! True derivatives of the scaled denominator and the degree-28 Taylor cutoff. -/
noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex Finset

def shortPoly (e : ℂ) (w : ℂ) := 2-24/e^4*(1+e*w+(e*w)^2/2+(e*w)^3/6)

def partialJet (e : ℝ) (m : ℕ) (w : ℂ) : ℂ :=
  iteratedDeriv m (shortPoly (e:ℂ)) w +
  (24/(e:ℂ)^4-1)*(e:ℂ)^m * ∑ a∈range (29-m), ((e:ℂ)*w)^a/a.factorial

theorem scaledG_split {e : ℝ} (he : 0<e) :
    scaledG e = fun w ↦ shortPoly (e:ℂ) w+(24/(e:ℂ)^4-1)*exp ((e:ℂ)*w) := by
  funext w
  unfold shortPoly scaledG G
  push_cast
  field_simp [show (e:ℂ)≠0 by exact_mod_cast he.ne']
  ring

theorem true_jet_remainder {e : ℝ} (he : 0<e) (w : ℂ) (m : ℕ) :
    iteratedDeriv m (scaledG e) w - partialJet e m w =
    (24/(e:ℂ)^4-1)*(e:ℂ)^m *
      (exp ((e:ℂ)*w) - ∑ a∈range (29-m),((e:ℂ)*w)^a/a.factorial) := by
  rw [scaledG_split he]
  have sh : ContDiffAt ℂ m (shortPoly (e:ℂ)) w := by unfold shortPoly;fun_prop
  have ex : ContDiffAt ℂ m (fun z : ℂ ↦ (24/(e:ℂ)^4-1)*exp ((e:ℂ)*z)) w := by fun_prop
  rw [iteratedDeriv_fun_add sh ex,iteratedDeriv_const_mul_field,iteratedDeriv_cexp_const_mul]
  unfold partialJet
  ring

/-- All true midpoint derivative errors up to order two have the common
rational majorant used in the full seventeen-cell table. -/
theorem partialJet_bound {e : ℝ} (he : 0<e) (small : e≤6/5) {w : ℂ} (hw : ‖w‖≤2)
    {m : ℕ} (hm : m≤2) :
    ‖iteratedDeriv m (scaledG e) w-partialJet e m w‖ ≤
      2*(24*e^25+e^29)*2^(29-m)/((29-m).factorial:ℝ) := by
  let N := 29-m
  have nbig : 27≤N := by dsimp [N]; omega
  have nsum : m+N=29 := by dsimp [N];omega
  have en : ‖(e:ℂ)‖=e := by simp [abs_of_pos he]
  have normx : ‖(e:ℂ)*w‖≤e*2 := by rw [norm_mul,en];gcongr
  have ins : ‖(e:ℂ)*w‖/(N.succ:ℝ)≤1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have v : (27:ℝ)≤N := by exact_mod_cast nbig
    push_cast
    linarith
  have expB := Complex.exp_bound' ins
  have mb : ‖(24/(e:ℂ)^4-1 : ℂ)‖≤24/e^4+1 := by
    have h := norm_sub_le (24/(e:ℂ)^4 : ℂ) 1
    simpa [norm_pow,abs_of_pos he] using h
  rw [true_jet_remainder he, norm_mul,norm_mul,norm_pow,en]
  have nb := mul_le_mul_of_nonneg_right mb (pow_nonneg he.le m)
  have p : ‖(e:ℂ)*w‖^N ≤ (e*2)^N := by gcongr
  calc
    _ ≤ ((24/e^4+1)*e^m)*((e*2)^N/N.factorial*2) := by
      apply mul_le_mul nb _ (norm_nonneg _) (by positivity)
      exact expB.trans (by gcongr)
    _ = _ := by
      change _ = 2*(24*e^25+e^29)*2^N/(N.factorial:ℝ)
      rw [mul_pow]
      have eqn : e^m*e^N=e^29 := by rw [←pow_add,nsum]
      calc
        _ = (24/e^4+1)*(e^m*e^N)*(2^N/N.factorial*2) := by ring
        _ = _ := by rw [eqn]; field_simp [he.ne']

#print axioms true_jet_remainder
#print axioms partialJet_bound
end OrderedPartitions.FourPole.Box
