import OrderedPartitions.CriticalEdgeOneResidue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! Additivity of the difference between a Taylor coefficient and its circle integral. -/
noncomputable section
namespace OrderedPartitions.FinitePoleCircle
open Complex Metric Filter Set
open scoped Topology

def coeff (f : ℂ→ℂ) (n : ℕ) := iteratedDeriv n f 0 / (n.factorial:ℂ)
def outer (f : ℂ→ℂ) (R : ℝ) (n : ℕ) :=
  (2*(Real.pi:ℂ)*I)⁻¹ • ∮ z in C(0,R), (z^(n+1))⁻¹*f z
def defect (f : ℂ→ℂ) (R : ℝ) (n : ℕ) := coeff f n-outer f R n

private theorem inverse_outer (g : ℂ→ℂ) (R : ℝ) (n : ℕ) :
    outer (fun z ↦ (g z)⁻¹) R n = CriticalEdge.circleRemainder g R n := by
  simp only [outer,CriticalEdge.circleRemainder,mul_inv_rev,mul_comm]

private theorem integral_ok {R : ℝ} (rpos : 0<R) {f : ℂ→ℂ}
    (hc : ContinuousOn f (sphere 0 R)) (n : ℕ) :
    CircleIntegrable (fun z ↦ (z^(n+1))⁻¹*f z) 0 R := by
  apply ContinuousOn.circleIntegrable rpos.le
  apply ContinuousOn.mul _ hc
  apply (continuousOn_id.pow _).inv₀
  intro z hz
  have h : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
  exact pow_ne_zero _ (norm_pos_iff.mp (h.symm ▸ rpos))

private theorem defect_add {f g : ℂ→ℂ} {R : ℝ} (rpos : 0<R) (n : ℕ)
    (fa : AnalyticAt ℂ f 0) (ga : AnalyticAt ℂ g 0)
    (fc : ContinuousOn f (sphere 0 R)) (gc : ContinuousOn g (sphere 0 R)) :
    defect (fun z ↦ f z+g z) R n=defect f R n+defect g R n := by
  simp only [defect,coeff,outer,iteratedDeriv_fun_add fa.contDiffAt ga.contDiffAt, add_div,mul_add]
  rw [circleIntegral.integral_add (integral_ok rpos fc n) (integral_ok rpos gc n),smul_add]
  ring

private theorem defect_const_mul (a : ℂ) (f : ℂ→ℂ) (R : ℝ) (n : ℕ) :
    defect (fun z ↦ a*f z) R n=a*defect f R n := by
  have g (z : ℂ) : (z^(n+1))⁻¹*(a*f z)=a*((z^(n+1))⁻¹*f z) := by ring
  simp only [defect,coeff,outer,iteratedDeriv_const_mul_field,g,circleIntegral.integral_const_mul,
    smul_eq_mul]
  ring

private theorem defect_term (g : ℂ→ℂ) {p : ℂ} {R : ℝ} (hr : 0<R)
    (hp : ‖p‖<R) (pn : p≠0) (n : ℕ) :
    defect (FiniteSimplePoles.term g p) R n = -(deriv g p)⁻¹/p^(n+1) := by
  have h := CriticalEdge.coefficient_one_pole (g:=fun z : ℂ ↦ z-p) (by fun_prop)
    hr hp pn (by simp) (by simp) (by intro w _ eqn; exact sub_eq_zero.mp eqn) n
  rw [← inverse_outer] at h
  simp only [deriv_sub_const,deriv_id'',inv_one] at h
  unfold FiniteSimplePoles.term
  rw [defect_const_mul]
  unfold defect coeff
  rw [h]
  ring

private theorem good_term (g : ℂ→ℂ) {p : ℂ} {R : ℝ} (hp : ‖p‖<R) (pn : p≠0) :
    AnalyticAt ℂ (FiniteSimplePoles.term g p) 0 ∧
    ContinuousOn (FiniteSimplePoles.term g p) (sphere 0 R) := by
  unfold FiniteSimplePoles.term
  constructor
  · apply analyticAt_const.mul
    apply (analyticAt_id.sub analyticAt_const).inv
    simpa using pn
  · apply continuousOn_const.mul
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz
    have h : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    apply sub_ne_zero.mpr
    intro eqn
    change z = p at eqn
    exact hp.ne (eqn ▸ h)

private theorem defect_sum {ι : Type*} (s : Finset ι) (f : ι→ℂ→ℂ) {R : ℝ} (hr : 0<R) (n : ℕ)
    (h : ∀ i∈s, AnalyticAt ℂ (f i) 0 ∧ ContinuousOn (f i) (sphere 0 R)) :
    defect (fun z ↦ ∑ i∈s, f i z) R n = ∑ i∈s,defect (f i) R n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [defect,coeff,outer,circleIntegral]
  | @insert a s han ih =>
    have ha := h a (Finset.mem_insert_self _ _)
    have hs i (hi : i∈s) := h i (Finset.mem_insert_of_mem hi)
    simp only [Finset.sum_insert han]
    rw [defect_add hr n ha.1 (Finset.analyticAt_fun_sum _ fun i hi ↦ (hs i hi).1) ha.2
      (continuousOn_finsetSum _ fun i hi ↦ (hs i hi).2),ih hs]

private theorem defect_holo {U : Set ℂ} {H : ℂ→ℂ} {R : ℝ} (hr : 0<R)
    (incl : closedBall 0 R ⊆ U) (hh : DifferentiableOn ℂ H U) (n : ℕ) :
    defect H R n=0 := by
  let r : NNReal := ⟨R,hr.le⟩
  have ps := ((hh.mono incl).hasFPowerSeriesOnBall (R:=r) hr).hasFPowerSeriesAt
  have h := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n)
    (ps.analyticAt.hasFPowerSeriesAt.eq_formalMultilinearSeries ps)
  change (FormalMultilinearSeries.ofScalars ℂ _).coeff n = (cauchyPowerSeries H 0 R).coeff n at h
  rw [FormalMultilinearSeries.coeff_ofScalars] at h
  have hc : (cauchyPowerSeries H 0 R).coeff n = outer H R n := by
    change (cauchyPowerSeries H 0 R n) (fun _ ↦ (1 : ℂ)) = _
    rw [cauchyPowerSeries_apply]
    simp only [outer,sub_zero,one_div,smul_eq_mul,← mul_assoc,← pow_succ,← inv_pow]
  exact sub_eq_zero.mpr (h.trans hc)

/-- Any finite set of distinct simple poles strictly inside the circle. -/
theorem coefficient {g : ℂ→ℂ} (hg : Differentiable ℂ g) {R : ℝ} (hr : 0<R)
    (S : Finset ℂ) (loc : ∀ p∈S, ‖p‖<R ∧ p≠0)
    (roots : ∀ p∈S,g p=0) (simple : ∀ p∈S,deriv g p≠0)
    (exhaust : ∀ w, ‖w‖≤R → g w=0 → w∈S) (n : ℕ) :
    coeff (fun z ↦ (g z)⁻¹) n =
      CriticalEdge.circleRemainder g R n - ∑ p∈S,(deriv g p)⁻¹/p^(n+1) := by
  classical
  let U := ball (0:ℂ) R ∪ {w|g w≠0}
  have op : IsOpen U := isOpen_ball.union (isOpen_ne_fun hg.continuous continuous_const)
  have inc : closedBall 0 R ⊆ U := by
    intro w hw
    by_cases gz : g w=0
    · have hw' : ‖w‖≤R := by simpa only [mem_closedBall,dist_zero_right] using hw
      exact Or.inl (by simpa only [mem_ball,dist_zero_right] using (loc w (exhaust w hw' gz)).1)
    · exact Or.inr gz
  obtain ⟨H,hh,split⟩ := FiniteSimplePoles.remove hg op S roots simple (fun w hw gz ↦ by
    have wb : w∈ball 0 R := hw.resolve_right (fun ne ↦ ne gz)
    exact exhaust w (by simpa only [mem_ball,dist_zero_right] using (mem_ball.mp wb).le) gz)
  let f := fun w : ℂ ↦ H w + ∑ p∈S, FiniteSimplePoles.term g p w
  have ns : (0:ℂ)∉S := fun h ↦ (loc 0 h).2 rfl
  have near : (fun w ↦ (g w)⁻¹) =ᶠ[𝓝 0] f := by
    filter_upwards [S.finite_toSet.isClosed.isOpen_compl.mem_nhds ns] with w hw
    exact split w hw
  have boundary : outer (fun w ↦ (g w)⁻¹) R n=outer f R n := by
    unfold outer
    congr 1
    apply circleIntegral.integral_congr hr.le
    intro z hz
    have zr : ‖z‖=R := by simpa only [mem_sphere,dist_zero_right] using hz
    exact congrArg (fun v : ℂ ↦ (z^(n+1))⁻¹*v) (split z (fun h ↦ (loc z h).1.ne zr))
  have agree : defect (fun w ↦ (g w)⁻¹) R n=defect f R n := by
    unfold defect coeff
    rw [boundary,near.iteratedDeriv_eq n]
  have good p (hp : p∈S) := good_term g (loc p hp).1 (loc p hp).2
  have hzero : (0:ℂ)∈U := inc (mem_closedBall_self hr.le)
  have hsum := defect_add hr n (hh.analyticAt (op.mem_nhds hzero))
    (Finset.analyticAt_fun_sum _ fun p hp ↦ (good p hp).1)
    (hh.continuousOn.mono (sphere_subset_closedBall.trans inc))
    (continuousOn_finsetSum _ fun p hp ↦ (good p hp).2)
  rw [show defect f R n = _ from hsum,defect_holo hr inc hh n,zero_add,
    defect_sum S _ hr n good, Finset.sum_congr rfl (fun p hp ↦ defect_term g hr (loc p hp).1 (loc p hp).2 n)] at agree
  unfold defect at agree
  rw [inverse_outer] at agree
  simp only [neg_div,Finset.sum_neg_distrib] at agree
  linear_combination agree

#print axioms coefficient
end OrderedPartitions.FinitePoleCircle
