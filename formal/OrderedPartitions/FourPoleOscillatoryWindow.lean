import OrderedPartitions.FourPoleActualCorner
import OrderedPartitions.FourPoleJetIdentity

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Finset

private theorem rational_activity : 1407/100<CriticalEdge.ratio 2 (19/20) := by
  have h := Real.exp_bound' (by norm_num : (0:ℝ)≤19/20) (by norm_num : (19/20:ℝ)≤1) (by decide : 0<10)
  norm_num [sum_range_succ,Nat.factorial] at h
  unfold CriticalEdge.ratio
  apply (lt_div_iff₀ (CriticalEdge.tail_pos _ (by norm_num))).mpr
  norm_num [CriticalEdge.tail,CriticalEdge.tap,sum_range_succ,Nat.factorial]
  linarith

/-- On the full oscillatory interval the genuine contour model holds for every
rank. The critical activity is the maximum determined by the true EGF. -/
theorem original_oscillatory_model :
    ∃ a : ℝ, Real.log 2<a ∧ a<1 ∧ CriticalEdge.criticalTest 2 a=0 ∧
    ∀ q : ℝ, 1-1/CriticalEdge.ratio 2 a<q → q<1 →
    ∃ z v : ℂ, CirclePoles q 3 z v ∧ z.im<z.re ∧ ‖z‖<‖v‖ ∧
        ∀ n : ℕ, 0<scaleRow n q z ∧ scaleRow n q z*(row n 4).eval (-q/(1-q)) =
        model (polarPhase n q z) (polarPhase n q v) (secondaryWeight n q z v) (circleError n q 3 z) ∧
        |circleError n q 3 z|≤450*‖first q z‖*(‖z‖/3)^(n+1) := by
  obtain ⟨a,al,au,cr,ac,mx⟩ := CriticalEdge.strict_maximum (k:=2) (by decide)
  refine ⟨a,al,au,cr,?_⟩
  intro q qc q1
  have lb : 1407/100<CriticalEdge.ratio 2 a := by
    by_cases eqn : 19/20=a
    · simpa [←eqn] using rational_activity
    · exact rational_activity.trans (mx _ (by norm_num) eqn)
  let e := Real.sqrt (Real.sqrt (24*(1-q)))
  have hv : 0<24*(1-q) := by linarith
  have ep : 0<e := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hv)
  have fourth : e^4=24*(1-q) := by
    dsimp [e]
    rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt hv.le]
  have C0 : 0<CriticalEdge.ratio 2 a := by linarith
  have osc : CriticalEdge.ratio 2 a < 1/(1-q) := by
    apply (lt_div_iff₀ (by linarith)).mpr
    have ht := mul_lt_mul_of_pos_right qc C0
    field_simp at ht
    nlinarith only [ht]
  have limit := (lt_div_iff₀ (by linarith : 0<1-q)).mp (lb.trans osc)
  have eh : e≤1143/1000 := by
    by_contra! high
    have := pow_lt_pow_left₀ high (by norm_num) (by decide : (4:ℕ)≠0)
    rw [fourth] at this
    norm_num at this
    linarith
  have eqn : 1-e^4/24=q := by rw [fourth];ring
  have model := original_window_model ep eh mx (by rwa [eqn])
  rw [eqn] at model
  obtain ⟨z,v,pol,ang,sz,sv,rest⟩ := model
  exact ⟨z,v,pol,ang,sz.trans sv,rest⟩

#print axioms original_oscillatory_model
end OrderedPartitions.FourPole
