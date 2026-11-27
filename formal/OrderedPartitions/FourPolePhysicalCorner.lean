import OrderedPartitions.FourPoleFunction
import OrderedPartitions.FourPoleUniformCorner
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

noncomputable section
namespace OrderedPartitions.FourPole
open Filter Topology

def dir (a : ℝ) : ℂ := Complex.exp ((a:ℂ)*Complex.I)

private theorem dir_arg {a : ℝ} (ha : a ∈ Set.Ioc (-Real.pi) Real.pi) : (dir a).arg = a := by
  unfold dir
  rw [Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ha

private theorem dir_mem {a : ℝ} (ha : a ∈ Set.Ioo (-Real.pi) Real.pi) : dir a ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_arg,dir_arg ⟨ha.1,ha.2.le⟩]
  exact ⟨ha.2.ne,Complex.exp_ne_zero _⟩

theorem quartic_dirs :
    (dir (Real.pi/4))^4 = -1 ∧ (dir (3*Real.pi/4))^4 = -1 := by
  unfold dir
  rw [← Complex.exp_nat_mul,← Complex.exp_nat_mul]
  push_cast
  rw [show (4:ℂ)*((Real.pi/4)*Complex.I)=Real.pi*Complex.I by ring,
    show (4:ℂ)*(3*Real.pi/4*Complex.I)=Real.pi*Complex.I + 2*Real.pi*Complex.I by ring,
    Complex.exp_add,Complex.exp_two_pi_mul_I,Complex.exp_pi_mul_I]
  norm_num

theorem physical_slopes {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w : ι→ℂ} {a : ℝ}
    (he : Tendsto e l (𝓝 0)) (ep : ∀ᶠ i in l, 0<e i) (W : Tendsto w l (𝓝 (dir a)))
    (regular : a ∈ Set.Ioo (-Real.pi) Real.pi) (quad : dir a^4 = -1)
    (zero : ∀ᶠ i in l, G (1-e i^4/24) ((e i:ℂ)*w i)=0) :
    Tendsto (fun i ↦ ((w i).arg-a)/e i) l (𝓝 (-(3/10)*Real.sin a)) ∧
    Tendsto (fun i ↦ Real.log ‖w i‖/e i) l (𝓝 (-(3/10)*Real.cos a)) := by
  have h := physical_root_velocity quad he W (ep.mono fun _ h ↦ h.ne') zero
  obtain ⟨ap,rp⟩ := polar_velocity W (dir_mem regular) h
  have algebra : (dir a)⁻¹ * (-(3/10)*(dir a)^2) = -(3/10)*dir a := by
    field_simp [show dir a ≠ 0 from Complex.exp_ne_zero _]
  rw [algebra,dir_arg ⟨regular.1,regular.2.le⟩] at ap
  rw [algebra,show ‖dir a‖=1 from Complex.norm_exp_ofReal_mul_I _,Real.log_one] at rp
  simp only [sub_zero] at rp
  constructor
  · convert ap using 2
    simp [dir,Complex.exp_mul_I,Complex.mul_im]
    rfl
  · convert rp using 2
    simp [dir,Complex.exp_mul_I,Complex.mul_re]
    rfl

def residueScale (e : ℝ) (w : ℂ) : ℂ := w^3/6-(e:ℂ)/12

theorem physical_residue_scale {e : ℝ} {w : ℂ} (zero : G (1-e^4/24) ((e:ℂ)*w)=0) :
    first (1-e^4/24) ((e:ℂ)*w)=(e:ℂ)^3*residueScale e w := by
  rw [first_at_root zero]
  unfold residueScale
  push_cast
  ring

/-- A fourth-step old-zero sign for zeros of the true exponential denominator,
assuming identification of the two upper branches and the signed residue formula.
Angles, radius ratio, and ratio of derivative norms are determined by these zeros. -/
theorem actual_pole_fourth {ι : Type*} {l : Filter ι} {e : ι→ℝ} {w z : ι→ℂ}
    (he : Tendsto e l (𝓝 0)) (ep : ∀ᶠ i in l, 0<e i)
    (W : Tendsto w l (𝓝 (dir (Real.pi/4)))) (Z : Tendsto z l (𝓝 (dir (3*Real.pi/4))))
    (zw : ∀ᶠ i in l, G (1-e i^4/24) ((e i:ℂ)*w i)=0)
    (zz : ∀ᶠ i in l, G (1-e i^4/24) ((e i:ℂ)*z i)=0) :
    let v (i : ι) := ‖w i‖/‖z i‖
    let A (i : ι) := ‖residueScale (e i) (w i)‖/‖residueScale (e i) (z i)‖
    ∀ᶠ i in l, ∀ n : ℕ, 3 ≤ (n:ℝ)*e i → ∀ ψ χ E F : ℝ,
      |E| ≤ e i^2 → |F| ≤ e i^2 → model ψ χ (A i*v i^(n+1)) E = 0 →
      0 < Real.sin ψ * model (ψ+4*(w i).arg) (χ+4*(z i).arg) ((A i*v i^(n+1))*v i^4) F := by
  have pi := Real.pi_pos
  have wp : (Real.pi/4) ∈ Set.Ioo (-Real.pi) Real.pi := ⟨by linarith,by linarith⟩
  have zp : (3*Real.pi/4) ∈ Set.Ioo (-Real.pi) Real.pi := ⟨by linarith,by linarith⟩
  obtain ⟨wa,wr⟩ := physical_slopes he ep W wp quartic_dirs.1 zw
  obtain ⟨za,zr⟩ := physical_slopes he ep Z zp quartic_dirs.2 zz
  have sin3 : Real.sin (3*Real.pi/4) = Real.sin (Real.pi/4) := by
    rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.sin_pi_sub]
  have cos3 : Real.cos (3*Real.pi/4) = -Real.cos (Real.pi/4) := by
    rw [show 3*Real.pi/4=Real.pi-Real.pi/4 by ring,Real.cos_pi_sub]
  have speed : -(3/10:ℝ)*(Real.sqrt 2/2) = -cornerSpeed := by
    unfold cornerSpeed
    field_simp [show Real.sqrt 2 ≠ 0 from (Real.sqrt_pos.2 (by norm_num)).ne']
    nlinarith [Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)]
  rw [Real.sin_pi_div_four,speed] at wa
  rw [sin3,Real.sin_pi_div_four,speed] at za
  rw [Real.cos_pi_div_four,speed] at wr
  rw [cos3,Real.cos_pi_div_four,mul_neg,speed,neg_neg] at zr
  have wn := W.eventually_ne (show dir _ ≠ 0 from Complex.exp_ne_zero _)
  have zn := Z.eventually_ne (show dir _ ≠ 0 from Complex.exp_ne_zero _)
  have hv : Tendsto (fun i ↦ (Real.log (‖w i‖/‖z i‖)-0)/e i) l (𝓝 (-2*cornerSpeed)) := by
    have h := wr.sub zr
    rw [show -cornerSpeed-cornerSpeed= -2*cornerSpeed by ring] at h
    refine h.congr' ?_
    filter_upwards [wn,zn] with i wi zi
    simp [Real.log_div (norm_ne_zero_iff.mpr wi) (norm_ne_zero_iff.mpr zi),sub_div]
  have vlim := scaled_chain he ep hv (Real.hasDerivAt_exp 0)
  simp only [Real.exp_zero,one_mul] at vlim
  apply uniform_fourth he _ _ wa za _ _
  · exact ep
  · filter_upwards [wn,zn] with i wi zi using div_pos (norm_pos_iff.mpr wi) (norm_pos_iff.mpr zi)
  · refine vlim.congr' ?_
    filter_upwards [wn,zn] with i wi zi
    rw [Real.exp_log (div_pos (norm_pos_iff.mpr wi) (norm_pos_iff.mpr zi))]
  · have ec : Tendsto (fun i ↦ (e i:ℂ)) l (𝓝 0) := by simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp he
    have wnrm : ‖dir (Real.pi/4)^3/(6:ℂ)‖ = 1/6 := by rw [norm_div,norm_pow,show ‖dir _‖=1 from Complex.norm_exp_ofReal_mul_I _]; norm_num
    have znrm : ‖dir (3*Real.pi/4)^3/(6:ℂ)‖ = 1/6 := by rw [norm_div,norm_pow,show ‖dir _‖=1 from Complex.norm_exp_ofReal_mul_I _]; norm_num
    have wl := ((W.pow 3).div_const 6 |>.sub (ec.div_const 12)).norm
    have zl := ((Z.pow 3).div_const 6 |>.sub (ec.div_const 12)).norm
    simp only [zero_div,sub_zero,wnrm,znrm] at wl zl
    have lh := wl.div zl (by norm_num)
    rw [div_self (by norm_num : (1/6:ℝ)≠0)] at lh
    exact lh.congr (fun i ↦ rfl)
#print axioms physical_residue_scale
#print axioms actual_pole_fourth
end OrderedPartitions.FourPole
