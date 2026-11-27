import OrderedPartitions.FourPoleSmallContour
import OrderedPartitions.FourPoleEdgeWitness

/-! Exact original rows on the true four-pole parameter window. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex Filter Topology
open scoped ComplexConjugate

theorem original_window_model {e a : ℝ} (ep : 0<e) (hi : e≤1143/1000)
    (maximum : ∀ x : ℝ, 0<x → x≠a → CriticalEdge.ratio 2 x<CriticalEdge.ratio 2 a)
    (osc : CriticalEdge.ratio 2 a < 1/(1-(1-e^4/24))) :
    let q := 1-e^4/24
    ∃ z v : ℂ, CirclePoles q 3 z v ∧ z.im<z.re ∧ ‖z‖<e ∧ e<‖v‖ ∧
     ∀ n : ℕ, 0<scaleRow n q z ∧ scaleRow n q z*(row n 4).eval (-q/(1-q)) =
       model (polarPhase n q z) (polarPhase n q v) (secondaryWeight n q z v) (circleError n q 3 z) ∧
       |circleError n q 3 z|≤450*‖first q z‖*(‖z‖/3)^(n+1) := by
  dsimp only
  have ex := if h : e≤1/10 then small_contour ep h
       else compact_contour (by linarith : 1/32≤e) hi maximum osc
  obtain ⟨z,v,pol,ang,sz,sv,fl⟩ := ex
  have q1 : 1-e^4/24<1 := by linarith only [pow_pos ep 4]
  refine ⟨z,v,pol,ang,sz,sv,fun n ↦ ⟨scaleRow_positive q1 pol _,original_circle_model q1 pol _,?_⟩⟩
  exact (circle_error_bound (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)<1/300)
    (fun w hw ↦ (fl w hw).le) n z).trans_eq (by ring)

private theorem selected_rotations (x : ℝ) :
    (dir x).re=Real.cos x ∧ (dir x).im=Real.sin x := by
  simp [dir,Complex.exp_mul_I,←Complex.ofReal_sin,←Complex.ofReal_cos]

private theorem selected_poles {e : ℝ} (ep : 0<e) (eh : e≤1/100) :
    let q := 1-e^4/24
    CirclePoles q 3 ((e:ℂ)*rightBranch e) ((e:ℂ)*leftBranch e) ∧
       ∀ z : ℂ, ‖z‖=3 → 1/300<‖G q z‖ := by
  obtain ⟨a,b,pol,_,_,_,floor⟩ := small_contour ep (by linarith)
  have R := branch_spec quartic_dirs.1 (Complex.norm_exp_ofReal_mul_I _) ep eh
  have L := branch_spec quartic_dirs.2 (Complex.norm_exp_ofReal_mul_I _) ep eh
  change ‖rightBranch e-dir _‖<10*e ∧ _ at R
  change ‖leftBranch e-dir _‖<10*e ∧ _ at L
  have sq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have rt : 1<Real.sqrt 2 := by nlinarith [Real.sqrt_nonneg 2]
  have ar := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt R.1)
  have ai := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt R.1)
  have br := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt L.1)
  have bi := abs_lt.mp ((Complex.abs_im_le_norm _).trans_lt L.1)
  simp only [sub_re,sub_im,(selected_rotations _).1,(selected_rotations _).2,
    Real.cos_pi_div_four,Real.sin_pi_div_four] at ar ai
  simp only [sub_re,sub_im,(selected_rotations _).1,(selected_rotations _).2,
    show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub,Real.sin_pi_sub,
    Real.cos_pi_div_four,Real.sin_pi_div_four] at br bi
  have amag (w u : ℂ) (hu : ‖u‖=1) (h : ‖w-u‖<10*e) : ‖(e:ℂ)*w‖≤3 := by
    have t := norm_add_le (w-u) u
    rw [sub_add_cancel,hu] at t
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep]
    have w2 : ‖w‖≤2 := by linarith
    linarith only [mul_le_mul_of_nonneg_left w2 ep.le,eh]
  let A := (e:ℂ)*rightBranch e
  let B := (e:ℂ)*leftBranch e
  have classifyA := pol.exhaustive A (amag _ _ (Complex.norm_exp_ofReal_mul_I _) R.1) R.2
  have classifyB := pol.exhaustive B (amag _ _ (Complex.norm_exp_ofReal_mul_I _) L.1) L.2
  have Ap : 0<A.re := by change 0<((e:ℂ)*_).re;rw [re_ofReal_mul];exact mul_pos ep (by linarith)
  have Ai : 0<A.im := by change 0<((e:ℂ)*_).im;rw [im_ofReal_mul];exact mul_pos ep (by linarith)
  have Bn : B.re<0 := by change ((e:ℂ)*_).re<0;rw [re_ofReal_mul];exact mul_neg_of_pos_of_neg ep (by linarith)
  have Bi : 0<B.im := by change 0<((e:ℂ)*_).im;rw [im_ofReal_mul];exact mul_pos ep (by linarith)
  have neqConj {w u : ℂ} (wp : 0<w.im) (up : 0<u.im) : w≠star u := by
    intro eqn;rw [eqn] at wp;change 0< -u.im at wp;linarith
  have neqReal {w u : ℂ} (wp : 0<w.re) (un : u.re<0) : w≠u := fun eqn ↦ by rw [eqn] at wp;linarith
  have ha := classifyA.resolve_right (fun h ↦ (h.resolve_left (neqConj Ai pol.upperRight)).elim
    (neqReal Ap pol.left) (neqConj Ai pol.upperLeft))
  have hb := ((classifyB.resolve_left (neqReal pol.right Bn).symm).resolve_left
    (neqConj Bi pol.upperRight)).resolve_right (neqConj Bi pol.upperLeft)
  change CirclePoles _ _ A B ∧ _
  rw [ha,hb]
  exact ⟨pol,floor⟩

/-- Near the activity endpoint, fourth-shift cancellation holds at a zero
of the original ordered-partition row, uniformly in all n with n ε≥3. -/
theorem original_fourth_at_corner :
    ∀ᶠ e : ℝ in 𝓝[>] 0, ∀ n : ℕ, 3≤(n:ℝ)*e →
      let q := 1-e^4/24
      let z := (e:ℂ)*rightBranch e
      (row n 4).eval (-q/(1-q))=0 →
      0<Real.sin (polarPhase n q z)*(row (n+4) 4).eval (-q/(1-q)) := by
  have lim := tendsto_nhdsWithin_of_tendsto_nhds (s:=Set.Ioi (0:ℝ)) (tendsto_id (α:=ℝ) (x:=𝓝 0))
  filter_upwards [self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Set.Ioi 0),
    lim.eventually_lt_const (by norm_num : (0:ℝ)<1/100),selected_pole_fourth 450 (by norm_num)] with e ep eh sign
  intro n hne
  dsimp only
  intro zero
  have epos : 0<e := ep
  let q := 1-e^4/24
  let z := (e:ℂ)*rightBranch e
  let v := (e:ℂ)*leftBranch e
  obtain ⟨pol,fl⟩ := selected_poles epos eh.le
  have q1 : q<1 := by dsimp [q];linarith only [pow_pos epos 4]
  have roweq (m : ℕ) := original_circle_model q1 pol m
  have err (m : ℕ) : |circleError m q 3 z|≤450*‖first q z‖*(‖z‖/3)^(m+1) :=
    (circle_error_bound (by norm_num : (0:ℝ)<3) (by norm_num : (0:ℝ)<1/300)
    (fun w hw ↦ (fl w hw).le) m z).trans_eq (by ring)
  have ratio_eq : ‖z‖/‖v‖=ratio e := by
    dsimp only [z,v,ratio];rw [norm_mul,norm_mul,mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (by exact_mod_cast epos.ne'))]
  have amp_eq : ‖first q z‖/‖first q v‖=amplitude e := by
    rw [physical_residue_scale pol.zeroRight,physical_residue_scale pol.zeroLeft,norm_mul,norm_mul,
      mul_div_mul_left _ _ (pow_ne_zero 3 (by exact_mod_cast epos.ne') |> norm_ne_zero_iff.mpr)]
    rfl
  have weight (m : ℕ) : secondaryWeight m q z v=amplitude e*ratio e^(m+1) := by
    unfold secondaryWeight; rw [ratio_eq,amp_eq]
  have phases (u : ℂ) : polarPhase (n+4) q ((e:ℂ)*u)=polarPhase n q ((e:ℂ)*u)+4*u.arg := by
    unfold polarPhase
    push_cast;rw [Complex.arg_real_mul _ epos];ring
  have old := roweq n
  change scaleRow n q z*_=model _ _ _ _ at old
  rw [zero,mul_zero,weight] at old
  have strict := sign n hne _ _ _ _ (err n) (err (n+4)) old.symm
  have next := roweq (n+4)
  change scaleRow (n+4) q z*(row (n+4) 4).eval _=model _ _ _ _ at next
  rw [phases,phases,weight,show n+4+1=n+1+4 by omega,pow_add,←mul_assoc] at next
  rw [←next] at strict
  have pos := scaleRow_positive (n:=n+4) q1 pol
  change 0<Real.sin (polarPhase n q z)*_ 
  rw [mul_left_comm] at strict
  exact (mul_pos_iff_of_pos_left pos).mp strict

#print axioms original_window_model
#print axioms original_fourth_at_corner
end OrderedPartitions.FourPole
