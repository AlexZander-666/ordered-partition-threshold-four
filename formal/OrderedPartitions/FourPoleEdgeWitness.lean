import OrderedPartitions.FourPolePhysicalDisks

/-! Selected actual poles and row-index-uniform attenuation of the Cauchy remainder. -/
noncomputable section
namespace OrderedPartitions.FourPole
open Filter Topology Set
open scoped Topology

def branch (ω : ℂ) (e : ℝ) : ℂ := by
  classical
  exact if h : ∃ w : ℂ, ‖w-ω‖<10*e ∧ G (1-e^4/24) ((e:ℂ)*w)=0
    then h.choose else ω

theorem branch_spec {ω : ℂ} (q : ω^4 = -1) (norm : ‖ω‖=1) {e : ℝ} (he : 0<e) (sm : e≤1/100) :
    ‖branch ω e-ω‖<10*e ∧ G (1-e^4/24) ((e:ℂ)*branch ω e)=0 := by
  obtain ex := small_disk_zero he sm q norm
  simpa [branch,dif_pos ex] using ex.choose_spec

theorem branch_tendsto {ω : ℂ} (q : ω^4 = -1) (norm : ‖ω‖=1) :
    Tendsto (branch ω) (𝓝[>] 0) (𝓝 ω) := by
  apply Metric.tendsto_nhds.mpr
  intro s hs
  have he : Tendsto (fun e : ℝ ↦ e) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have h := (he.const_mul 10).eventually_lt_const (show (10:ℝ)*0<s by linarith)
  filter_upwards [self_mem_nhdsWithin (a:=0) (s:=Ioi 0),
    he.eventually_lt_const (by norm_num : (0:ℝ)<1/100),h] with e ep sm cap
  exact (show dist (branch ω e) ω < 10*e by simpa [dist_eq_norm] using (branch_spec q norm ep sm.le).1).trans cap

def rightBranch := branch (dir (Real.pi/4))
def leftBranch := branch (dir (3*Real.pi/4))
def ratio (e : ℝ) : ℝ := ‖rightBranch e‖/‖leftBranch e‖
def amplitude (e : ℝ) : ℝ := ‖residueScale e (rightBranch e)‖/‖residueScale e (leftBranch e)‖

/-- A fixed circle error factor may be arbitrarily large. Only the small-epsilon
neighborhood depends on it. The same neighborhood works for all contour exponents. -/
theorem contour_epsilon_sq (K : ℝ) (K0 : 0≤K) :
    ∀ᶠ e : ℝ in 𝓝[>] 0, ∀ t : ℕ,
      K * ‖first (1-e^4/24) ((e:ℂ)*rightBranch e)‖ *
        (‖(e:ℂ)*rightBranch e‖/3)^t ≤ e^2 := by
  have tend := branch_tendsto quartic_dirs.1 (Complex.norm_exp_ofReal_mul_I _)
  have norm := tend.norm
  rw [show ‖dir (Real.pi/4)‖=1 from Complex.norm_exp_ofReal_mul_I _] at norm
  have he : Tendsto (fun e : ℝ ↦ e) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have bound := (he.const_mul K).eventually_lt_const (show K*0<1/2 by linarith)
  filter_upwards [norm.eventually_lt_const one_lt_two, self_mem_nhdsWithin (a:=(0:ℝ)) (s:=Ioi 0),
    he.eventually_lt_const (by norm_num : (0:ℝ)<1/100),bound] with e wbound ep sm cost
  intro t
  have epos : 0<e := ep
  have spec := branch_spec quartic_dirs.1 (Complex.norm_exp_ofReal_mul_I _) epos sm.le
  change ‖rightBranch e‖<2 at wbound
  have phys : first _ ((e:ℂ)*rightBranch e) = (e:ℂ)^3*residueScale e (rightBranch e) := physical_residue_scale spec.2
  rw [phys,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos epos]
  have cn : ‖residueScale e (rightBranch e)‖ ≤ 2 := by
    have h := norm_sub_le ((rightBranch e)^3/(6:ℂ)) ((e:ℂ)/12)
    rw [norm_div,norm_pow,norm_div,Complex.norm_ofNat,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos epos] at h
    change ‖(rightBranch e)^3/6-(e:ℂ)/12‖ ≤ 2
    have u : ‖rightBranch e‖^3 ≤ 2^3 := by gcongr
    linarith only [h,u,sm]
  have v : ‖(e:ℂ)*rightBranch e‖/3 ≤ 1 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos epos]
    have p := mul_le_mul_of_nonneg_left wbound.le epos.le
    linarith
  have hpow := pow_le_one₀ (by positivity : 0 ≤ ‖(e:ℂ)*rightBranch e‖/3) v (n:=t)
  calc
    _ ≤ K*(e^3*2)*1 := by gcongr
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right cost.le (sq_nonneg e)]

/-- For two selected zeros of the actual denominator, the fourth-step sign is
uniform in every n with n epsilon at least three and for every fixed contour cap. -/
theorem selected_pole_fourth (K : ℝ) (K0 : 0≤K) :
    ∀ᶠ e : ℝ in 𝓝[>] 0, ∀ n : ℕ, 3 ≤ (n:ℝ)*e → ∀ ψ χ E F : ℝ,
      |E| ≤ K*‖first (1-e^4/24) ((e:ℂ)*rightBranch e)‖*(‖(e:ℂ)*rightBranch e‖/3)^(n+1) →
      |F| ≤ K*‖first (1-e^4/24) ((e:ℂ)*rightBranch e)‖*(‖(e:ℂ)*rightBranch e‖/3)^(n+5) →
      model ψ χ (amplitude e*ratio e^(n+1)) E=0 →
      0 < Real.sin ψ * model (ψ+4*(rightBranch e).arg) (χ+4*(leftBranch e).arg)
        ((amplitude e*ratio e^(n+1))*ratio e^4) F := by
  have he : Tendsto (fun e : ℝ ↦ e) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have pos : ∀ᶠ e : ℝ in 𝓝[>] 0, 0<e := self_mem_nhdsWithin
  have zero {ω : ℂ} (q : ω^4 = -1) (unit : ‖ω‖=1) :
      ∀ᶠ e : ℝ in 𝓝[>] 0, G (1-e^4/24) ((e:ℂ)*branch ω e)=0 := by
    filter_upwards [pos,he.eventually_lt_const (by norm_num : (0:ℝ)<1/100)] with e ep sm
    exact (branch_spec q unit ep sm.le).2
  have a := actual_pole_fourth he pos
    (branch_tendsto quartic_dirs.1 (Complex.norm_exp_ofReal_mul_I _))
    (branch_tendsto quartic_dirs.2 (Complex.norm_exp_ofReal_mul_I _))
    (zero quartic_dirs.1 (Complex.norm_exp_ofReal_mul_I _)) (zero quartic_dirs.2 (Complex.norm_exp_ofReal_mul_I _))
  filter_upwards [a,contour_epsilon_sq K K0] with e sign bound
  intro n window ψ χ E F o d h
  exact sign n window ψ χ E F (o.trans (bound _)) (d.trans (bound _)) h

#print axioms branch_tendsto
#print axioms contour_epsilon_sq
#print axioms selected_pole_fourth
end OrderedPartitions.FourPole
