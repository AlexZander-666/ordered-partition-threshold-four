import OrderedPartitions.FourPoleSmallPair

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals
open Complex

theorem ratio_bounds (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (eh : e≤(p.hi:ℝ)) {z v : ℂ} (pol : CirclePoles (1-e^4/24) 3 z v) :
    -2*(high p:ℝ)*e≤Real.log (‖z‖/‖v‖) ∧ Real.log (‖z‖/‖v‖)≤ -2*(low p:ℝ)*e ∧
    (low p:ℝ)*e≤Real.pi/4-z.arg ∧ Real.pi/4-z.arg≤(high p:ℝ)*e ∧
    (low p:ℝ)*e≤3*Real.pi/4-v.arg ∧ 3*Real.pi/4-v.arg≤(high p:ℝ)*e := by
  obtain ⟨w,y,ew,ey,wd,yd⟩ := small_pair i p id ep eh pol
  have W := small_chart i p id ep eh (Or.inl rfl) wd
  have Y := small_chart i p id ep eh (Or.inr rfl) yd
  have wn : w≠0 := by intro hz;have := pol.upperRight;rw [ew,hz] at this;simp at this
  have yn : y≠0 := by intro hz;have := pol.upperLeft;rw [ey,hz] at this;simp at this
  rw [ew,ey,Complex.arg_real_mul _ ep,Complex.arg_real_mul _ ep,norm_mul,norm_mul,
    mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (show (e:ℂ)≠0 by exact_mod_cast ep.ne')),
    Real.log_div (norm_ne_zero_iff.mpr wn) (norm_ne_zero_iff.mpr yn)]
  have V := abs_le.mp Y.2.2
  rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.cos_pi_div_four] at V
  have U := abs_le.mp W.2.2
  rw [Real.cos_pi_div_four] at U
  have val := id ▸ valid i
  have rp : 0≤(p.radius:ℝ) := by rcases val.disk with ⟨r,_⟩|⟨r,_⟩ <;> rw [r] <;> norm_num
  have sm : (u p:ℝ)*(p.hi:ℝ)<1 := by exact_mod_cast val.logr
  have Bc : (B p:ℝ)=(p.radius:ℝ)+(u p:ℝ)^2/(2*(1-(u p:ℝ)*(p.hi:ℝ))) := by unfold B;push_cast;rfl
  have bp : 0≤(B p:ℝ) := by rw [Bc]; exact add_nonneg rp (div_nonneg (sq_nonneg _) (by linarith))
  have shrink := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right eh ep.le) bp
  have lo : 2121320/10000000<(3/10:ℝ)*(Real.sqrt 2/2) := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have hi : (3/10:ℝ)*(Real.sqrt 2/2)<2121321/10000000 := by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  refine ⟨?_,?_,W.1,W.2.1,Y.1,Y.2.1⟩
  · unfold high;push_cast
    nlinarith only [shrink,U.1,V.2,mul_le_mul_of_nonneg_right hi.le ep.le]
  · unfold low;push_cast
    nlinarith only [shrink,U.2,V.1,mul_le_mul_of_nonneg_right lo.le ep.le]

/-- Bounds for both pieces of the four-step cancellation. The first uses the
actual visible lower cutoff n ε≥3; the second bounds the loss after four shifts. -/
theorem ratio_powers (i : Fin 6) (p : Cell) (id : p=cells i) {e : ℝ}
    (ep : 0<e) (el : (p.lo:ℝ)≤e) (eh : e≤(p.hi:ℝ)) {z v : ℂ}
    (pol : CirclePoles (1-e^4/24) 3 z v) {n : ℕ} (hn : 288≤n) (vis : 3≤(n:ℝ)*e) :
    (‖z‖/‖v‖)^(n+1)≤1/(trunc (x p):ℝ) ∧
      1-(‖z‖/‖v‖)^4≤8*(high p:ℝ)*e := by
  let L := ‖z‖/‖v‖
  have zpos := norm_pos_iff.mpr (show z≠0 by intro h;have := pol.upperRight;simp [h] at this)
  have vpos := norm_pos_iff.mpr (show v≠0 by intro h;have := pol.upperLeft;simp [h] at this)
  have lp : 0<L := div_pos zpos vpos
  obtain ⟨lg,ug,_⟩ := ratio_bounds i p id ep eh pol
  change -2*(high p:ℝ)*e≤Real.log L at lg
  change Real.log L≤ -2*(low p:ℝ)*e at ug
  have val := id ▸ valid i
  have lowpos : 0<(low p:ℝ) := by exact_mod_cast val.lower
  have en : max 3 (288*(p.lo:ℝ))≤ (n:ℝ)*e := max_le vis (by
    have h := mul_le_mul_of_nonneg_right (show (288:ℝ)≤n by exact_mod_cast hn) ep.le
    linarith)
  have xc : (x p:ℝ)=2*(low p:ℝ)*max 3 (288*(p.lo:ℝ)) := by unfold x;push_cast;rfl
  have xp : 0≤(x p:ℝ) := by rw [xc];exact mul_nonneg (by positivity) ((by norm_num : (0:ℝ)≤3).trans (le_max_left _ _))
  have tc : (trunc (x p):ℝ)=1+(x p:ℝ)+(x p:ℝ)^2/2+(x p:ℝ)^3/6+(x p:ℝ)^4/24+(x p:ℝ)^5/120 := by unfold trunc;push_cast;rfl
  have tp : 0<(trunc (x p):ℝ) := by rw [tc];positivity
  have expBound := Real.sum_le_exp_of_nonneg xp 6
  norm_num [Finset.sum_range_succ,Nat.factorial] at expBound
  have ex : (trunc (x p):ℝ)≤Real.exp (x p) := by rw [tc];linarith only [expBound]
  have powers (b : ℕ) : Real.exp ((b:ℝ)*Real.log L)=L^b := by rw [Real.exp_nat_mul,Real.exp_log lp]
  change L^(n+1)≤_ ∧ 1-L^4≤_
  constructor
  · rw [←powers]
    calc
      _ ≤ Real.exp (-(x p:ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [xc];push_cast
        nlinarith only [mul_le_mul_of_nonneg_left en (show 0≤2*(low p:ℝ) by positivity),
          mul_le_mul_of_nonneg_left ug (show 0≤(n:ℝ)+1 by positivity),mul_pos lowpos ep]
      _ ≤ _ := by rw [Real.exp_neg,one_div];exact inv_anti₀ tp ex
  · have le := Real.add_one_le_exp ((4:ℝ)*Real.log L)
    rw [show (4:ℝ)=((4:ℕ):ℝ) by norm_num,powers] at le
    push_cast at le
    linarith

#print axioms ratio_bounds
#print axioms ratio_powers
end OrderedPartitions.FourPole.SixIntervals
