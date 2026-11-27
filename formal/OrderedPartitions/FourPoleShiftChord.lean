import OrderedPartitions.FourPolePhaseWindow

noncomputable section
namespace OrderedPartitions.FourPole
open Real

/-- Norm of the secondary phase error once the old zero removes its
in-phase component. This treats all integral phase shifts in the same formula. -/
def shiftChord (δ η L : ℝ) : ℝ := ‖(Real.cos δ:ℂ)-(L:ℂ)*dir η‖

private theorem chord_projection (χ δ η L : ℝ) :
    |Real.cos δ*Real.cos χ-L*Real.cos (χ+η)| ≤ shiftChord δ η L := by
  have trig (a : ℝ) : (dir a).re=Real.cos a ∧ (dir a).im=Real.sin a := by
    change (Complex.exp (↑a*Complex.I)).re=_ ∧ (Complex.exp (↑a*Complex.I)).im=_
    simp [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have h := Complex.abs_re_le_norm (((Real.cos δ:ℂ)-(L:ℂ)*dir η)*dir χ)
  rw [norm_mul,show ‖dir χ‖=1 from Complex.norm_exp_ofReal_mul_I _,mul_one] at h
  unfold shiftChord
  convert h using 2
  simp only [Real.cos_add,Complex.mul_re,Complex.sub_re,Complex.sub_im,
    Complex.im_ofReal_mul,Complex.ofReal_re,Complex.ofReal_im,(trig _).1,(trig _).2]
  ring

private theorem unit_power (z : ℂ) (h : ℕ) :
    (↑(‖z‖^h):ℂ)*dir ((h:ℝ)*z.arg)=z^h := by
  rw [←Complex.norm_mul_exp_arg_mul_I z] at ⊢
  conv_rhs => rw [mul_pow]
  simp only [Complex.norm_mul_exp_arg_mul_I]
  rw [dir,Complex.ofReal_mul,Complex.ofReal_natCast,mul_assoc,Complex.exp_nat_mul,Complex.ofReal_pow]

/-- Clearing the angular denominator makes the effective comparison algebraic
in the two complex poles. This identity still holds when h=0. -/
theorem polynomial_chord {z v : ℂ} (vn : v≠0) (h : ℕ) :
    ‖z‖^h*shiftChord ((h:ℝ)*z.arg) ((h:ℝ)*v.arg) ((‖z‖/‖v‖)^h) =
      ‖((z^h).re:ℂ)-(((‖z‖^2/‖v‖^2)^h:ℝ):ℂ)*v^h‖ ∧
    ‖z‖^h*Real.sin ((h:ℝ)*z.arg)=(z^h).im := by
  have trig (a : ℝ) : (dir a).re=Real.cos a ∧ (dir a).im=Real.sin a := by
    change (Complex.exp (↑a*Complex.I)).re=_ ∧ (Complex.exp (↑a*Complex.I)).im=_
    simp [Complex.exp_mul_I,←Complex.ofReal_cos,←Complex.ofReal_sin]
  have r := congrArg Complex.re (unit_power z h)
  have i := congrArg Complex.im (unit_power z h)
  rw [Complex.re_ofReal_mul,(trig _).1] at r
  rw [Complex.im_ofReal_mul,(trig _).2] at i
  refine ⟨?_,i⟩
  have vn' : ‖v‖≠0 := norm_ne_zero_iff.mpr vn
  have alg : ‖z‖^h*(‖z‖/‖v‖)^h=(‖z‖^2/‖v‖^2)^h*‖v‖^h := by
    rw [←mul_pow,←mul_pow];congr 1;field_simp
  dsimp [shiftChord]
  rw [←show ‖(↑(‖z‖^h):ℂ)‖=‖z‖^h by simp,←norm_mul]
  congr 1
  rw [mul_sub,←Complex.ofReal_mul,r,←mul_assoc,←Complex.ofReal_mul,alg,Complex.ofReal_mul,mul_assoc,unit_power]

/-- A scalar, rotation-invariant gate for the sign at an old zero. -/
theorem sign_of_chord {ψ χ δ η L A E E' : ℝ}
    (old : model ψ χ A E=0) (s : 0<Real.sin δ)
    (gate : (|A|+|E|)^2+
      ((|A| *shiftChord δ η L+|E'|+|E|)/Real.sin δ)^2<1) :
    0 < Real.sin ψ * model (ψ+δ) (χ+η) (A*L) E' := by
  have c : Real.cos ψ= -A*Real.cos χ+E := by unfold model at old;linarith
  have bound : |Real.cos ψ|≤|A|+|E| := by
    rw [c];apply (abs_add_le _ _).trans
    rw [abs_mul,abs_neg]
    linarith only [mul_le_mul_of_nonneg_left (Real.abs_cos_le_one χ) (abs_nonneg A)]
  let M := |A| *shiftChord δ η L+|E'|+|E|
  have force : M/Real.sin δ < |Real.sin ψ| := by
    by_contra! no
    have u := mul_self_le_mul_self (abs_nonneg _) bound
    have v := mul_self_le_mul_self (abs_nonneg _) no
    change (|A|+|E|)^2+(M/Real.sin δ)^2<1 at gate
    nlinarith only [u,v,gate,Real.sin_sq_add_cos_sq ψ,sq_abs (Real.cos ψ),sq_abs (Real.sin ψ)]
  have err : |model (ψ+δ) (χ+η) (A*L) E' -Real.sin ψ*Real.sin δ|≤M := by
    have alg : model (ψ+δ) (χ+η) (A*L) E' -Real.sin ψ*Real.sin δ =
      A*(Real.cos δ*Real.cos χ-L*Real.cos (χ+η))+E'-E*Real.cos δ := by
      unfold model;rw [Real.cos_add ψ δ,c];ring
    rw [alg]
    rw [sub_eq_add_neg]
    apply (abs_add_le _ _).trans
    rw [abs_neg]
    have add := abs_add_le (A*(Real.cos δ*Real.cos χ-L*Real.cos (χ+η))) E'
    rw [abs_mul] at add
    rw [abs_mul]
    dsimp [M]
    linarith only [add,mul_le_mul_of_nonneg_left (chord_projection χ δ η L) (abs_nonneg A),
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one δ) (abs_nonneg E)]
  have margin := (div_lt_iff₀ s).mp force
  obtain ⟨lo,hi⟩ := abs_le.mp err
  rcases le_or_gt (Real.sin ψ) 0 with neg|pos
  · rw [abs_of_nonpos neg] at margin
    apply mul_pos_of_neg_of_neg
    · by_contra! eqn
      have eq : Real.sin ψ=0 := le_antisymm neg eqn
      rw [eq] at margin;linarith
    · linarith
  · rw [abs_of_pos pos] at margin
    exact mul_pos pos (by linarith)

/-- Algebraic relative-frequency gate. It uses the two pole locations and
Cauchy errors, and never asks for evaluation at an unknown root of a row. -/
def PhysicalChordGate (n h : ℕ) : Prop :=
  ∀ {e : ℝ}, 0<e → e≤1143/1000 → 3≤(n:ℝ)*e →
    let q := 1-e^4/24
    ∀ {z v : ℂ}, CirclePoles q 3 z v → z.im<z.re → ‖z‖<‖v‖ →
    let A := secondaryWeight n q z v
    let E := circleError n q 3 z
    let E' := circleError (n+h) q 3 z
    let δ := (h:ℝ)*z.arg
    let η := (h:ℝ)*v.arg
    let L := (‖z‖/‖v‖)^h
    |A|+|E|≤2/5 ∧ 0<Real.sin δ ∧
      (|A|+|E|)^2+((|A| *shiftChord δ η L+|E'|+|E|)/Real.sin δ)^2<1

theorem visible_of_chord {n h : ℕ} (gate : PhysicalChordGate n h) : VisiblePointwise n h := by
  intro e ep eh vis
  dsimp only
  intro z v pol angle order
  let q := 1-e^4/24
  obtain ⟨amplitude,positive,metric⟩ := gate ep eh vis pol angle order
  refine ⟨amplitude,?_⟩
  intro hz
  have q1 : q<1 := by dsimp [q];linarith only [pow_pos ep 4]
  have old := original_circle_model q1 pol n
  have next := original_circle_model q1 pol (n+h)
  change (row n 4).eval (-q/(1-q))=0 at hz
  rw [hz,mul_zero] at old
  have phases (w : ℂ) : polarPhase (n+h) q w=polarPhase n q w+(h:ℝ)*w.arg := by
    unfold polarPhase;push_cast;ring
  have weight : secondaryWeight (n+h) q z v=secondaryWeight n q z v*(‖z‖/‖v‖)^h := by
    unfold secondaryWeight;rw [show n+h+1=n+1+h by omega,pow_add];ring
  rw [phases,phases,weight] at next
  have strict := sign_of_chord old.symm positive metric
  rw [←next,mul_left_comm] at strict
  exact pos_of_mul_pos_right strict (scaleRow_positive q1 pol (n+h)).le

theorem original_pair_of_chord {n h : ℕ} (hn : 288≤n) (gap : h≤4)
    (gate : PhysicalChordGate n h) :
    RootTracking.OrderedPair (n/4) (row n 4) (row (n+h) 4) :=
  original_pair_of_visible hn gap (visible_of_chord gate)

#print axioms polynomial_chord
#print axioms sign_of_chord
#print axioms visible_of_chord
#print axioms original_pair_of_chord
end OrderedPartitions.FourPole
