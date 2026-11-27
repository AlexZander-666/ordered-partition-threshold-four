import OrderedPartitions.FourPoleJetIdentity
import OrderedPartitions.PolynomialDiskRouche

noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex Finset

def activeCoeff (e : ℝ) (i : ℕ) : ℝ :=
  if i=0 then 1 else ((if 4 ≤ i then 24*e^(i-4) else 0)-e^i)/i.factorial

private theorem expand_coeff (e : ℝ) (he : 0<e) (a : ℕ) :
    activeCoeff e a=(24/e^4-1)*e^a/a.factorial -
      (if a<4 then 24/e^4*e^a/a.factorial else 0)+(if a=0 then 2 else 0) := by
  by_cases a0 : a=0
  · subst a; simp [activeCoeff];ring
  · by_cases sm : a<4
    · simp [activeCoeff,a0,sm,show ¬4≤a by omega]
      ring
    · simp [activeCoeff,a0,sm,show 4≤a by omega]
      rw [show e^a=e^4*e^(a-4) by rw [←pow_add];congr 1;omega]
      field_simp

theorem polynomial_at_zero {e : ℝ} (he : 0<e) (w : ℂ) :
    PolynomialDisk.eval 29 (fun i ↦ (activeCoeff e i:ℂ)) w=partialJet e 0 w := by
  let a := (24/(e:ℂ)^4-1)
  let b := 24/(e:ℂ)^4
  let t := fun i : ℕ ↦ ((e:ℂ)*w)^i/(i.factorial:ℂ)
  have term (i : ℕ) : (activeCoeff e i:ℂ)*w^i =
      a*t i - (if i<4 then b*t i else 0) + (if i=0 then (2:ℂ) else 0) := by
    rw [expand_coeff e he]
    by_cases low : i<4
    · by_cases zero : i=0
      · subst i; simp [a,b,t]
      · simp [a,b,t,low,zero];ring
    · have nz : i≠0 := by omega
      simp [a,t,low,nz];ring
  have cutoff : (∑ i∈range 29, if i<4 then b*t i else 0) = b*∑ i∈range 4,t i := by
    rw [←sum_filter,show (range 29).filter (fun i ↦ i<4) = range 4 by decide,Finset.mul_sum]
  unfold PolynomialDisk.eval
  simp_rw [term]
  rw [sum_add_distrib,sum_sub_distrib,cutoff,←Finset.mul_sum]
  simp only [Finset.sum_ite_eq',Finset.mem_range,show 0<29 by decide,if_true]
  unfold partialJet
  rw [iteratedDeriv_zero]
  dsimp [shortPoly,a,b,t]
  rw [show (∑ i∈range 4,((e:ℂ)*w)^i/i.factorial) =
    1+(e:ℂ)*w+((e:ℂ)*w)^2/2+((e:ℂ)*w)^3/6 by norm_num [sum_range_succ,Nat.factorial]]
  ring

def powerSwing (lo hi mid : ℝ) (i : ℕ) := max (hi^i-mid^i) (mid^i-lo^i)
def swing (lo hi mid : ℝ) (i : ℕ) :=
  (powerSwing lo hi mid i + (if 4 ≤ i then 24*powerSwing lo hi mid (i-4) else 0))/(i.factorial:ℝ)

theorem actual_swing {lo hi e mid : ℝ} (nonneg : 0≤lo) (le : lo≤e) (eh : e≤hi)
    (_midlo : lo≤mid) (_midhi : mid≤hi) (i : ℕ) :
    ‖((activeCoeff e i:ℝ):ℂ)-(activeCoeff mid i:ℂ)‖≤swing lo hi mid i := by
  have p (h : ℕ) : |e^h-mid^h|≤powerSwing lo hi mid h := by
    unfold powerSwing
    exact abs_le.mpr ⟨by linarith only [pow_le_pow_left₀ nonneg le h,le_max_right (hi^h-mid^h) (mid^h-lo^h)],
      by linarith only [pow_le_pow_left₀ (nonneg.trans le) eh h,le_max_left (hi^h-mid^h) (mid^h-lo^h)]⟩
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  by_cases iz : i=0
  · subst i;simp [activeCoeff,swing,powerSwing]
  · by_cases large : 4 ≤ i
    · simp only [activeCoeff,if_neg iz,if_pos large,swing,← sub_div,abs_div,
        abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) i.factorial)]
      gcongr
      rw [show 24*e^(i-4)-e^i-(24*mid^(i-4)-mid^i)=24*(e^(i-4)-mid^(i-4))-(e^i-mid^i) by ring]
      have b := abs_sub (24*(e^(i-4)-mid^(i-4))) (e^i-mid^i)
      rw [abs_mul,abs_of_pos (show (0:ℝ)<24 by norm_num)] at b
      linarith only [b,p (i-4),p i]
    · simp only [activeCoeff,if_neg iz,if_neg large,swing,zero_sub,add_zero,←sub_div,
        abs_div,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) i.factorial)]
      gcongr
      simpa only [neg_sub_neg,abs_sub_comm] using p i

#print axioms polynomial_at_zero
#print axioms actual_swing
end OrderedPartitions.FourPole.Box
