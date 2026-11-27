import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Euclidean disk inclusions used to separate two conjugate pairs. -/
namespace OrderedPartitions.FourPole
namespace Box

structure Disc where
  x : ℚ
  y : ℚ
  r : ℚ
  mode : ℕ
  deriving DecidableEq, Repr

structure Cell where
  lo : ℚ
  hi : ℚ
  right : Disc
  left : Disc
  deriving DecidableEq, Repr

noncomputable def center (D : Disc) : ℂ := (D.x : ℝ) + (D.y : ℝ)*Complex.I

def rightTest (D : Disc) : Prop :=
  0 < D.r ∧ D.r < 1 ∧ D.x^2+D.y^2 < (1-D.r)^2 ∧ 2*D.r < D.x-D.y ∧
  ((D.mode=1 ∧ D.r<D.y) ∨ (D.mode=2 ∧ D.y=0))
def leftTest (D : Disc) : Prop :=
  0 < D.r ∧ (1+D.r)^2 < D.x^2+D.y^2 ∧ D.x+D.r<0 ∧ D.r<D.y ∧ D.mode=1

instance (D : Disc) : Decidable (rightTest D) := by unfold rightTest; infer_instance
instance (D : Disc) : Decidable (leftTest D) := by unfold leftTest; infer_instance

private theorem norm_center (D : Disc) : ‖center D‖^2=(D.x:ℝ)^2+(D.y:ℝ)^2 := by
  rw [Complex.sq_norm]
  simp [center,Complex.normSq, pow_two]

private theorem coordinates (D : Disc) {w : ℂ} (inside : ‖w-center D‖ ≤ (D.r:ℝ)) :
    |w.re-(D.x:ℝ)| ≤ (D.r:ℝ) ∧ |w.im-(D.y:ℝ)| ≤ (D.r:ℝ) := by
  constructor
  · simpa [center] using (Complex.abs_re_le_norm (w-center D)).trans inside
  · simpa [center] using (Complex.abs_im_le_norm (w-center D)).trans inside

theorem right_location {D : Disc} (ok : rightTest D) {w : ℂ}
    (inside : ‖w-center D‖ ≤ (D.r:ℝ)) :
    ‖w‖ < 1 ∧ w.im < w.re ∧ (D.mode=1 → 0<w.im) := by
  rcases ok with ⟨_,r1,sq,sep,mode⟩
  have r1' : (D.r:ℝ)<1 := by exact_mod_cast r1
  have sq' : (D.x:ℝ)^2+(D.y:ℝ)^2<(1-(D.r:ℝ))^2 := by exact_mod_cast sq
  have sep' : 2*(D.r:ℝ)<(D.x:ℝ)-(D.y:ℝ) := by exact_mod_cast sep
  have bound : ‖center D‖ < 1-(D.r:ℝ) := by nlinarith [norm_center D, norm_nonneg (center D)]
  obtain ⟨rx,ry⟩ := coordinates D inside
  obtain ⟨xl,xh⟩ := abs_le.mp rx
  obtain ⟨yl,yh⟩ := abs_le.mp ry
  refine ⟨?_,by linarith,?_⟩
  · have := norm_add_le (w-center D) (center D)
    rw [sub_add_cancel] at this
    linarith
  · intro h
    rcases mode with ⟨_,r⟩|⟨no,_⟩
    · have r' : (D.r:ℝ)<(D.y:ℝ) := by exact_mod_cast r
      linarith
    · omega

theorem left_location {D : Disc} (ok : leftTest D) {w : ℂ}
    (inside : ‖w-center D‖ ≤ (D.r:ℝ)) : 1 < ‖w‖ ∧ w.re < 0 ∧ 0 < w.im := by
  obtain ⟨r0,sq,lr,lh,_⟩ := ok
  have rp : 0<(D.r:ℝ) := by exact_mod_cast r0
  have sq' : (1+(D.r:ℝ))^2<(D.x:ℝ)^2+(D.y:ℝ)^2 := by exact_mod_cast sq
  have h : 1+(D.r:ℝ)<‖center D‖ := by nlinarith [norm_center D,norm_nonneg (center D)]
  have xr : (D.x:ℝ)+(D.r:ℝ)<0 := by exact_mod_cast lr
  have yr : (D.r:ℝ)<(D.y:ℝ) := by exact_mod_cast lh
  obtain ⟨rx,ry⟩ := coordinates D inside
  obtain ⟨_,xh⟩ := abs_le.mp rx
  obtain ⟨yl,_⟩ := abs_le.mp ry
  have t := norm_add_le (center D-w) w
  rw [sub_add_cancel,norm_sub_rev] at t
  exact ⟨by linarith,by linarith,by linarith⟩

#print axioms right_location
#print axioms left_location
end Box
end OrderedPartitions.FourPole
