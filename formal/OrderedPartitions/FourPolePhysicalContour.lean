import OrderedPartitions.FourPoleNewtonGeometry
import OrderedPartitions.FourPoleCirclePhase

/-! True four-pole contour on the entire compact oscillatory parameter range. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Complex ExpInterpolation
open scoped ComplexConjugate

theorem pinned_contour {e : ℝ} (ep : 0<e) (eh : e≤1143/1000)
    {a b : ℂ} (au : 0<a.im) (bu : 0<b.im) (ang : a.im<a.re) (left : b.re<0)
    (big : e<‖b‖) (ar : ‖a‖≤6/5) (br : ‖b‖≤8/5) (bx : |b.re|≤6/5)
    (ga : G (1-e^4/24) a=0) (gb : G (1-e^4/24) b=0) :
    CirclePoles (1-e^4/24) 3 a b ∧ ∀ z : ℂ, ‖z‖=3 → 1/300<‖G (1-e^4/24) z‖ := by
  classical
  let q := 1-e^4/24
  have qp : 116/125≤q := by
    have h := pow_le_pow_left₀ ep.le eh 4
    dsimp [q];norm_num at h;linarith
  have qpos : 0<q := by linarith
  have ap : 0<a.re := au.trans ang
  have sep {u v : ℂ} (ur : 0<u.re) (vr : v.re<0) : u≠v := by
    intro e;rw [e] at ur;linarith
  have uc {u : ℂ} (h : 0<u.im) : u≠conj u := fun eqn ↦ by
    have t := congrArg Complex.im eqn
    simp only [conj_im] at t;linarith
  have nod : [a,conj a,b,conj b].Nodup := by
    simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,List.nodup_nil,
      not_false_eq_true,and_true]
    exact ⟨⟨uc au,sep ap left,sep ap left⟩,⟨sep ap left,sep ap left⟩,uc bu⟩
  have conjG (w : ℂ) : G q (conj w)=conj (G q w) := by simp [G,exp_conj,Complex.conj_ofNat]
  have hits : ∀ w∈[a,conj a,b,conj b],G q w=0 := by
    intro w hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl
    · exact ga
    · rw [conjG,show G q a=0 from ga,map_zero]
    · exact gb
    · rw [conjG,show G q b=0 from gb,map_zero]
  have fac (z : ℂ) := four_zero_factorization qpos _ (by rfl) nod hits z
  have rg : first q a≠0 := by
    intro h
    have g := first_at_root ga
    change first q a = _ at g
    rw [h] at g
    have test := congrArg Complex.im g
    simp [pow_succ,mul_re,mul_im,sub_im,div_ofNat_im] at test
    nlinarith only [test,mul_pos au (show 0<a.re^2-a.im^2 by
        nlinarith only [mul_pos (sub_pos.mpr ang) (add_pos ap au)]),mul_pos au (sq_pos_of_pos ap)]
  have lf : first q b≠0 := by
    intro h
    have g := first_at_root gb
    change first q b = _ at g
    rw [h] at g
    have cube : b^3=((e^4/2:ℝ):ℂ) := by
      push_cast at g ⊢
      linear_combination -6*g
    have mag := congrArg norm cube
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at mag
    have grow := pow_lt_pow_left₀ big ep.le (by decide : (3:ℕ)≠0)
    have lim := mul_pos (pow_pos ep 3) (show 0<2-e by linarith)
    nlinarith only [mag,grow,lim]
  have rb (w : ℂ) (hw : w∈[a,conj a,b,conj b]) : ‖w‖≤8/5 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    have ha : ‖a‖≤8/5 := by linarith
    rcases hw with rfl|rfl|rfl|rfl <;> simp_all only [norm_conj]
  constructor
  · refine ⟨ap,left,au,bu,by linarith,by linarith,ga,gb,rg,lf,?_⟩
    intro w hw gz
    by_contra h
    have off : w∉[a,conj a,b,conj b] := by
      intro mem
      exact h (by simpa only [List.mem_cons,List.not_mem_nil,or_false,Complex.star_def] using mem)
    have fl := kernel_floor_off ap left ar br bx hw nod off
    have nz : kernel [a,conj a,b,conj b] w 1≠0 := by
      intro he;rw [he,norm_zero] at fl;norm_num at fl
    have rest := fac w
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at rest
    rw [gz] at rest
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at off
    exact (mul_ne_zero (mul_ne_zero (by exact_mod_cast qpos.ne')
      (mul_ne_zero (sub_ne_zero.mpr off.1) (mul_ne_zero (sub_ne_zero.mpr off.2.1)
        (mul_ne_zero (sub_ne_zero.mpr off.2.2.1) (sub_ne_zero.mpr off.2.2.2))))) nz) rest.symm
  · intro w hw
    have off : w∉[a,conj a,b,conj b] := fun mem ↦ by have := rb w mem;linarith
    have fl := kernel_floor_off ap left ar br bx hw.le nod off
    have dist {p : ℂ} {L : ℝ} (h : ‖p‖≤L) : 3-L≤‖w-p‖ := by
      have tri := norm_add_le (w-p) p
      rw [sub_add_cancel,hw] at tri
      linarith
    have cr : ‖conj a‖≤6/5 := by simpa using ar
    have cb : ‖conj b‖≤8/5 := by simpa using br
    rw [fac w]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos qpos]
    calc
      (1/300:ℝ) < (116/125)*((3-6/5)*((3-6/5)*((3-8/5)*(3-8/5))))*(1/1600) := by norm_num
      _ ≤ _ := by gcongr <;> first | exact qp | (apply dist; assumption)

theorem compact_contour {e a : ℝ} (lo : 1/32≤e) (hi : e≤1143/1000)
    (maximum : ∀ x : ℝ, 0<x → x≠a → CriticalEdge.ratio 2 x<CriticalEdge.ratio 2 a)
    (osc : CriticalEdge.ratio 2 a < 1/(1-(1-e^4/24))) :
    ∃ z v : ℂ, CirclePoles (1-e^4/24) 3 z v ∧ z.im<z.re ∧
      ‖z‖<e ∧ e<‖v‖ ∧ ∀ w : ℂ, ‖w‖=3 → 1/300<‖G (1-e^4/24) w‖ := by
  obtain ⟨z,v,zu,vu,za,vl,zs,vs,zr,vr,vx,gz,gv⟩ := Box.compact_physical_zeros lo hi maximum osc
  obtain ⟨pol,bound⟩ := pinned_contour (by linarith : 0<e) hi zu vu za vl vs zr vr vx gz gv
  exact ⟨z,v,pol,za,zs,vs,bound⟩

#print axioms pinned_contour
#print axioms compact_contour
end OrderedPartitions.FourPole
