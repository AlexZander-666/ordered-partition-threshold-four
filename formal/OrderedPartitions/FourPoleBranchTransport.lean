import OrderedPartitions.FourPoleOscillatoryWindow
import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Filter Set Metric
open scoped Topology ComplexConjugate

/-- Persistence of any genuine zero, including a multiple real zero, under a
real parameter change. No differentiability of a selected branch is assumed. -/
theorem pole_persists {q : ℝ} (q1 : q<1) {z : ℂ} (gz : G q z=0) {δ : ℝ} (dp : 0<δ) :
    ∀ᶠ t : ℝ in 𝓝 q, ∃ w∈ball z δ,G t w=0 := by
  have diff (t : ℝ) : Differentiable ℂ (G t) := fun w ↦ (hasDerivAt_G _ w).differentiableAt
  have ana := Complex.analyticOnNhd_univ_iff_differentiable.mpr (diff q)
  have iso := (ana z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero.resolve_left (by
    intro localZero
    have global := ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
                              (Set.mem_univ z) localZero
    have at0 := global (Set.mem_univ (0:ℂ))
    change G q 0=0 at at0
    simp [G] at at0
    have := congrArg re at0
    simp at this
    linarith)
  obtain ⟨η,ηp,rad⟩ := Metric.mem_nhdsWithin_iff.mp iso
  let r := min δ η / 2
  have rp : 0<r := by dsimp [r];positivity
  have rd : r<δ := by dsimp [r];linarith [min_le_left δ η]
  have re : r<η := by dsimp [r];linarith [min_le_right δ η]
  have no (w : ℂ) (hw : w∈sphere z r) : G q w≠0 := by
    apply rad
    have dist_eq := mem_sphere.mp hw
    exact ⟨mem_ball.mpr (dist_eq.trans_lt re),show w≠z from fun eqn ↦ by simp [eqn] at dist_eq;linarith⟩
  have nc := (isCompact_sphere z r).exists_isMinOn (NormedSpace.sphere_nonempty.mpr rp.le)
                               (diff q).continuous.norm.continuousOn
  obtain ⟨a,ain,minimum⟩ := nc
  have vpos := norm_pos_iff.mpr (no a ain)
  let B := Real.exp (r+‖z‖)+2
  have Bpos : 0<B := by dsimp [B];positivity
  have prox := Metric.ball_mem_nhds q (div_pos vpos Bpos)
  filter_upwards [prox] with t ht
  apply (ThreePole.exists_zero_of_boundary_dominance rp (diff t) (diff q) gz ?_).imp
  · intro w h
    exact ⟨ball_subset_ball rd.le h.1,h.2⟩
  · intro w hw
    have cap : ‖w‖≤r+‖z‖ := by
      have x := norm_add_le (w-z) z
      rwa [sub_add_cancel,←dist_eq_norm,mem_sphere.mp hw] at x
    have bnd : ‖exp w-2‖≤B := by
      apply (norm_sub_le _ _).trans
      rw [Complex.norm_exp,Complex.norm_ofNat]
      exact add_le_add (Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans cap)) le_rfl
    have e : G t w-G q w=((t-q:ℝ):ℂ)*(exp w-2) := by unfold G;push_cast;ring
    rw [e,norm_mul,Complex.norm_real,Real.norm_eq_abs]
    apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left bnd (abs_nonneg _))
    apply lt_of_lt_of_le _ (minimum hw)
    exact (lt_div_iff₀ Bpos).mp (by simpa [Real.dist_eq] using mem_ball.mp ht)

private theorem selector_near {q : ℝ} {z v : ℂ} (pol : CirclePoles q 3 z v)
    {s : Set ℝ} {A B : ℝ→ℂ} (data : ∀ t∈s,CirclePoles t 3 (A t) (B t)) (q1 : q<1) :
    Tendsto A (𝓝[s] q) (𝓝 z) := by
  apply Metric.tendsto_nhds.mpr
  intro δ dp
  let r := min (min z.re z.im) (min (3-‖z‖) δ)/2
  have rp : 0<r := by
    dsimp [r]; have := pol.right;have := pol.upperRight;have := pol.radiusRight;positivity
  have r1 : r<z.re := by unfold r at rp ⊢;linarith [(min_le_left (min z.re z.im) (min (3-‖z‖) δ)).trans (min_le_left z.re z.im)]
  have r2 : r<z.im := by unfold r at rp ⊢;linarith [(min_le_left (min z.re z.im) (min (3-‖z‖) δ)).trans (min_le_right z.re z.im)]
  have r3 : r<3-‖z‖ := by unfold r at rp ⊢;linarith [(min_le_right (min z.re z.im) (min (3-‖z‖) δ)).trans (min_le_left (3-‖z‖) δ)]
  have r4 : r<δ := by unfold r at rp ⊢;linarith [(min_le_right (min z.re z.im) (min (3-‖z‖) δ)).trans (min_le_right (3-‖z‖) δ)]
  filter_upwards [(pole_persists q1 pol.zeroRight rp).filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin]
    with t ex ts
  obtain ⟨w,wb,wg⟩ := ex
  have small : ‖w-z‖<r := by simpa [dist_eq_norm] using mem_ball.mp wb
  have cm := norm_add_le (w-z) z
  rw [sub_add_cancel] at cm
  have wr := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt small)
  have wi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt small)
  rw [sub_re] at wr
  rw [sub_im] at wi
  have spec := data t ts
  have values := spec.exhaustive w (by linarith) wg
  have eqn : w=A t := by
    rcases values with h|h|h|h
    · exact h
    · rw [h] at wi;change _ < -(A t).im-z.im ∧ _ at wi;linarith [spec.upperRight]
    · rw [h] at wr;linarith [spec.left]
    · rw [h] at wi;change _ < -(B t).im-z.im ∧ _ at wi;linarith [spec.upperLeft]
  rw [←eqn]
  exact (mem_ball.mp wb).trans r4

/-- Any selection of the two true quadrant poles has a continuous positive
primary pole and a continuous unwrapped primary phase throughout the window. -/
theorem primary_phase_continuous {s : Set ℝ} {A B : ℝ→ℂ}
    (data : ∀ q∈s,CirclePoles q 3 (A q) (B q) ∧ (A q).im<(A q).re ∧ q<1) (n : ℕ) :
    ContinuousOn A s ∧ ContinuousOn (fun t ↦ polarPhase n t (A t)) s := by
  have c : ContinuousOn A s := fun q hq ↦ selector_near (data q hq).1 (fun t ht ↦ (data t ht).1) (data q hq).2.2
  refine ⟨c,?_⟩
  intro q hq
  obtain ⟨p,ang,_⟩ := data q hq
  have angA := (Complex.continuousAt_arg (Or.inl p.right)).comp_continuousWithinAt (c q hq)
  have F : ContinuousWithinAt (fun t ↦ first t (A t)) s q := by
    have := c q hq;unfold first;fun_prop
  have ip : 0<(first q (A q)).im := by
    rw [first_at_root p.zeroRight]
    simp [pow_succ,mul_im,mul_re,div_ofNat_im]
    have hi := p.upperRight
    have hr := p.right
    nlinarith only [mul_pos hi (show 0<(A q).re^2-(A q).im^2 by
      nlinarith only [mul_pos (sub_pos.mpr ang) (add_pos hr hi)]),mul_pos hi (sq_pos_of_pos hr)]
  have argF := (Complex.continuousAt_arg (Or.inr ip.ne')).comp_continuousWithinAt (f:=fun t ↦ first t (A t)) F
  exact (continuousWithinAt_const.mul angA).add argF

#print axioms pole_persists
#print axioms primary_phase_continuous
end OrderedPartitions.FourPole
