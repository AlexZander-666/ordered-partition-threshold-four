import OrderedPartitions.FourPolePhysicalContour

noncomputable section
namespace OrderedPartitions.FourPole
open Complex ExpInterpolation
open scoped ComplexConjugate

/-- The boundary floor requires just the measured size of the four poles. -/
theorem circle_floor_of_sizes {q : ℝ} {a b : ℂ} (p : CirclePoles q 3 a b)
    (qp : 116/125≤q) (ar : ‖a‖≤6/5) (br : ‖b‖≤8/5) (bx : |b.re|≤6/5) :
    ∀ w : ℂ, ‖w‖=3 → 1/300<‖G q w‖ := by
  have qpos : 0<q := by linarith
  have ap := p.right
  have left := p.left
  have au := p.upperRight
  have bu := p.upperLeft
  have ga := p.zeroRight
  have gb := p.zeroLeft
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
  have rb (w : ℂ) (hw : w∈[a,conj a,b,conj b]) : ‖w‖≤8/5 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    have ha : ‖a‖≤8/5 := by linarith
    rcases hw with rfl|rfl|rfl|rfl <;> simp_all only [norm_conj]
  intro w hw
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
#print axioms circle_floor_of_sizes
end OrderedPartitions.FourPole
