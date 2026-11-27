import OrderedPartitions.FourPoleSeamPhase
import OrderedPartitions.FourPoleOscillatoryWindow
import OrderedPartitions.ThreePoleParameters

noncomputable section
namespace OrderedPartitions.FourPole
open Filter Set RootTracking
open scoped Topology

/-- Numerical inputs for the two-frequency phase argument. They involve only
the two amplitudes at old rank and the next row sign at an old zero. -/
def VisiblePointwise (n h : ℕ) : Prop :=
  ∀ {e : ℝ}, 0<e → e≤1143/1000 → 3≤(n:ℝ)*e →
    let q := 1-e^4/24
    ∀ {z v : ℂ}, CirclePoles q 3 z v → z.im<z.re → ‖z‖<‖v‖ →
    |secondaryWeight n q z v|+|circleError n q 3 z|≤2/5 ∧
      ((row n 4).eval (-q/(1-q))=0 →
        0<Real.sin (polarPhase n q z)*(row (n+h) 4).eval (-q/(1-q)))

/-- Genuine threshold-four rank-and-gap conclusion conditional only on the
pointwise residue budget on the visible interval. The endpoint, continuity,
numbers of real roots and evaluation of the old row are discharged here. -/
theorem original_pair_of_visible {n h : ℕ} (hn : 288≤n) (gap : h≤4)
    (budget : VisiblePointwise n h) :
    OrderedPair (n/4) (row n 4) (row (n+h) 4) := by
  classical
  obtain ⟨a,al,au,cr,data⟩ := original_oscillatory_model
  have ah : 1/2<a := (by linarith [Real.log_two_gt_d9] : 1/2<Real.log 2).trans al
  have ap : 0<a := by linarith
  let c := 1-1/CriticalEdge.ratio 2 a
  have ratio := CriticalEdge.critical_ratio ap cr
  norm_num [Nat.factorial] at ratio
  have qcrit : c=1-a^3/12 := by dsimp [c];rw [ratio];field_simp
  have cp : 0<c := by rw [qcrit];nlinarith only [pow_lt_pow_left₀ au ap.le (by decide : (3:ℕ)≠0)]
  have c1 : c<1 := by rw [qcrit];linarith only [pow_pos ap 3]
  have lower : 1407/100<CriticalEdge.ratio 2 a := by
    have uniq := (CriticalEdge.unique_critical (k:=2) (by decide))
    obtain ⟨b,ba,_,_,unique⟩ := uniq
    have ab : a=b := unique _ (show Real.log 2≤a from al.le) cr
    obtain ⟨b',b'l,_,b'cr,_,b'm⟩ := CriticalEdge.strict_maximum (k:=2) (by decide)
    have ee : b'=a := (unique _ b'l.le b'cr).trans ab.symm
    have one : 1407/100<CriticalEdge.ratio 2 (19/20) := by
      have h' := Real.exp_bound' (by norm_num : (0:ℝ)≤19/20) (by norm_num : (19/20:ℝ)≤1) (by decide : 0<10)
      norm_num [Finset.sum_range_succ,Nat.factorial] at h'
      unfold CriticalEdge.ratio
      apply (lt_div_iff₀ (CriticalEdge.tail_pos _ (by norm_num))).mpr
      norm_num [CriticalEdge.tail,CriticalEdge.tap,Finset.sum_range_succ,Nat.factorial]
      linarith
    subst b'
    by_cases eqn : (19/20:ℝ)=a
    · rwa [←eqn]
    · exact one.trans (b'm _ (by norm_num) eqn)
  have gc := real_critical_zero ap cr (by linarith [lower])
  let e0 := (3:ℝ)/n
  have np : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have ep : 0<e0 := by dsimp [e0];positivity
  have seam : (n:ℝ)*e0=3 := by dsimp [e0];field_simp
  have sm : e0≤1/96 := by nlinarith only [mul_le_mul_of_nonneg_right (show (288:ℝ)≤n by exact_mod_cast hn) ep.le,seam]
  let u := 1-e0^4/24
  have u1 : u<1 := by dsimp [u];linarith only [pow_pos ep 4]
  have cu : c<u := by
    rw [qcrit];dsimp [u]
    nlinarith only [pow_lt_pow_left₀ ah (by norm_num) (by decide : (3:ℕ)≠0),
      pow_le_pow_left₀ ep.le sm 4]
  let S := Ioo c 1
  choose zr vl pol ang order rest using fun t : S ↦ data t t.2.1 t.2.2
  let A := fun t : ℝ ↦ if ht : t∈S then zr ⟨t,ht⟩ else 0
  let B := fun t : ℝ ↦ if ht : t∈S then vl ⟨t,ht⟩ else 0
  have reps (t : ℝ) (ht : t∈S) : CirclePoles t 3 (A t) (B t) ∧ (A t).im<(A t).re ∧ ‖A t‖<‖B t‖ := by
    simpa only [A,B,dif_pos ht] using And.intro (pol ⟨t,ht⟩) (And.intro (ang ⟨t,ht⟩) (order ⟨t,ht⟩))
  let ψ := fun t ↦ polarPhase n t (A t)
  have cont : ContinuousOn ψ S := (primary_phase_continuous (fun t ht ↦ ⟨(reps t ht).1,(reps t ht).2.1,ht.2⟩) n).2
  have limit := phase_at_critical ap au c1 gc (fun t ht ↦ (reps t ht).1) n
  have : (𝓝[Ioo c 1] c).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ioo c1.ne];exact ⟨le_rfl,c1.le⟩
  have before : ∀ᶠ q in 𝓝[Ioo c 1] c, q<u := nhdsWithin_le_nhds (gt_mem_nhds cu)
  have inside : ∀ᶠ q in 𝓝[Ioo c 1] c, q∈Ioo c 1 := eventually_mem_nhdsWithin
  have back := limit.eventually_lt_const (show Real.pi/2<Real.pi+Real.pi/4 by linarith [Real.pi_pos])
  obtain ⟨l,ld,lu,bl⟩ := (inside.and (before.and back)).exists
  have closed : Icc l u ⊆ S := Icc_subset_Ioo ld.1 u1
  have front := original_seam_phase hn ep seam (reps u ⟨cu,u1⟩).1
  have point (t : ℝ) (ht : t∈Icc l u) :
      |secondaryWeight n t (A t) (B t)|+|circleError n t 3 (A t)|≤2/5 ∧
        ((row n 4).eval (-t/(1-t))=0 → 0<Real.sin (ψ t)*(row (n+h) 4).eval (-t/(1-t))) := by
    have dom := closed ht
    let e := Real.sqrt (Real.sqrt (24*(1-t)))
    have pos : 0<24*(1-t) := by linarith [dom.2]
    have p : 0<e := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr pos)
    have t4 : e^4=24*(1-t) := by dsimp [e];rw [show (4:ℕ)=2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt pos.le]
    have qid : 1-e^4/24=t := by linarith only [t4]
    have e0e : e0≤e := by
      by_contra! H
      have v := pow_lt_pow_left₀ H p.le (by decide : (4:ℕ)≠0)
      have t' := ht.2
      dsimp [u] at t'
      linarith
    have ub : e≤1143/1000 := by
      have th := dom.1
      dsimp [S,c] at th
      have ratioPos : 0<CriticalEdge.ratio 2 a := by linarith
      have a1 := mul_lt_mul_of_pos_right th ratioPos
      field_simp [ratioPos.ne'] at a1
      by_contra! H
      have E := pow_lt_pow_left₀ H (by norm_num) (by decide : (4:ℕ)≠0)
      norm_num at E
      nlinarith only [t4,E,mul_lt_mul_of_pos_right lower (sub_pos.mpr dom.2),a1]
    have hol : 3≤(n:ℝ)*e := by nlinarith only [seam,mul_le_mul_of_nonneg_left e0e np.le]
    have b := @budget e p ub hol (A t) (B t)
    rw [qid] at b
    exact b (reps t dom).1 (reps t dom).2.1 (reps t dom).2.2
  obtain ⟨dp,pl,_⟩ := original_shape n
  obtain ⟨dq,ql,q0⟩ := original_shape (n+h)
  apply ThreePole.ordered_pair_on_parameter dp (fun z ↦ by simp [z] at pl) (by rw [dq];omega)
    ql q0 (cp.trans ld.1) lu u1 (cont.mono closed) (by convert front using 1; ring) bl
  · intro t ht
    obtain ⟨pol',_,_⟩ := reps t (closed ht)
    let X := -secondaryWeight n t (A t) (B t)*Real.cos (polarPhase n t (B t))+circleError n t 3 (A t)
    refine ⟨scaleRow n t (A t),X,scaleRow_positive (closed ht).2 pol' n,?_,?_⟩
    · have trig := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (polarPhase n t (B t))) (abs_nonneg (secondaryWeight n t (A t) (B t)))
      dsimp [X];apply (abs_add_le _ _).trans
      rw [abs_mul,abs_neg];linarith only [trig,(point t ht).1]
    · rw [TwoPolePhase.negativeAxis,original_circle_model (closed ht).2 pol'];unfold model;dsimp [ψ,X];ring
  · exact fun t ht ↦ (point t ht).2

#print axioms original_pair_of_visible
end OrderedPartitions.FourPole
