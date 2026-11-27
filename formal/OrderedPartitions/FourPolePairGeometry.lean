import OrderedPartitions.FourPoleCompactDisks
import OrderedPartitions.FourPoleCirclePhase
import OrderedPartitions.CriticalEdgeScalar

/-! Physical size and orientation of the two selected pole pairs. -/
noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex Metric Set

def envelope (c : Cell) (D : Disc) (R : ℚ) : Prop :=
  0<c.hi ∧ 0<D.r ∧ c.hi*D.r<R ∧
  c.hi^2*(D.x^2+D.y^2) ≤ (R-c.hi*D.r)^2 ∧ c.hi*(|D.x|+D.r) ≤ 6/5

instance (c : Cell) (D : Disc) (R : ℚ) : Decidable (envelope c D R) := by
  unfold envelope; infer_instance

theorem envelope_bound {cell : Cell} {D : Disc} {R : ℚ} (ok : envelope cell D R)
    {e : ℝ} (en : 0<e) (eh : e≤(cell.hi:ℝ)) {w : ℂ} (inside : w∈ball (center D) (D.r:ℝ)) :
    ‖(e:ℂ)*w‖ ≤ (R:ℝ) ∧ |((e:ℂ)*w).re|≤6/5 := by
  obtain ⟨hp,rp,rs,bs,sx⟩ := ok
  have hp' : 0<(cell.hi:ℝ) := by exact_mod_cast hp
  have cr : (cell.hi:ℝ)*(D.r:ℝ)<(R:ℝ) := by exact_mod_cast rs
  have bounds : (cell.hi:ℝ)^2*((D.x:ℝ)^2+(D.y:ℝ)^2) ≤ ((R:ℝ)-(cell.hi:ℝ)*(D.r:ℝ))^2 := by exact_mod_cast bs
  have boundsx : (cell.hi:ℝ)*(|(D.x:ℝ)|+(D.r:ℝ))≤((6/5:ℚ):ℝ) := by exact_mod_cast sx
  norm_num at boundsx
  have cn : ‖center D‖^2=(D.x:ℝ)^2+(D.y:ℝ)^2 := by
    rw [Complex.sq_norm];simp [center,Complex.normSq,pow_two]
  rw [←cn,←mul_pow] at bounds
  have cap : (cell.hi:ℝ)*‖center D‖≤(R:ℝ)-(cell.hi:ℝ)*(D.r:ℝ) := by nlinarith
  have disp : ‖w-center D‖<(D.r:ℝ) := by simpa [dist_eq_norm] using mem_ball.mp inside
  have wr := norm_add_le (w-center D) (center D)
  rw [sub_add_cancel] at wr
  have wx := abs_add_le (w-center D).re (center D).re
  rw [←Complex.add_re,sub_add_cancel] at wx
  have cRe : (center D).re = (D.x:ℝ) := by simp [center]
  rw [cRe] at wx
  have sub := Complex.abs_re_le_norm (w-center D)
  constructor
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos en]
    calc
      _ ≤ (cell.hi:ℝ)*‖w‖ := mul_le_mul_of_nonneg_right eh (norm_nonneg _)
      _ ≤ (cell.hi:ℝ)*(‖center D‖+(D.r:ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hp'.le
      _ ≤ _ := by linarith [mul_add (cell.hi:ℝ) ‖center D‖ (D.r:ℝ)]
  · simp only [Complex.re_ofReal_mul,abs_mul,abs_of_pos en]
    exact (mul_le_mul eh (by linarith : |w.re|≤|(D.x:ℝ)|+(D.r:ℝ)) (abs_nonneg _) hp'.le).trans boundsx

private theorem scaled_zero {e : ℝ} (ep : 0<e) {w : ℂ} (hz : scaledG e w=0) :
    G (1-e^4/24) ((e:ℂ)*w)=0 :=
  (mul_eq_zero.mp hz).resolve_left (div_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast ep.ne')))

/-- The real-axis hypothesis is needed only in the final, conjugation-invariant,
upper-right double disk. All physical norm estimates are pointwise. -/
theorem physical_pair {e : ℝ} (ep : 0<e) {cell : Cell} (eh : e≤(cell.hi:ℝ))
    (dr : rightTest cell.right) (dl : leftTest cell.left)
    (re : envelope cell cell.right (6/5)) (le : envelope cell cell.left (8/5))
    (right : ∃ w∈ball (center cell.right) (cell.right.r:ℝ), scaledG e w=0)
    (left : ∃ w∈ball (center cell.left) (cell.left.r:ℝ), scaledG e w=0)
    (noReal : ∀ x : ℝ, 0<x → G (1-e^4/24) (x:ℂ)≠0) :
    ∃ z v : ℂ, 0<z.im ∧ 0<v.im ∧ z.im<z.re ∧ v.re<0 ∧
      ‖z‖<e ∧ e<‖v‖ ∧ ‖z‖≤6/5 ∧ ‖v‖≤8/5 ∧ |v.re|≤6/5 ∧
      G (1-e^4/24) z=0 ∧ G (1-e^4/24) v=0 := by
  obtain ⟨w,wi,wz⟩ := right
  obtain ⟨u,ui,uz⟩ := left
  have getRight : ∃ t∈ball (center cell.right) (cell.right.r:ℝ), scaledG e t=0 ∧ 0<t.im := by
    by_cases pos : 0<w.im
    · exact ⟨w,wi,wz,pos⟩
    have ni : w.im≠0 := by
      intro eqn
      have realw : w=(w.re:ℂ) := by apply Complex.ext <;> simp [eqn]
      have wr := (right_location dr (by simpa [dist_eq_norm] using (mem_ball.mp wi).le)).2.1
      apply noReal (e*w.re) (mul_pos ep (eqn ▸ wr))
      simpa only [Complex.ofReal_mul,←realw] using scaled_zero ep wz
    have sym : cell.right.y=0 := by
      have keep := dr
      obtain ⟨_,_,_,_,case1|case2⟩ := keep
      · exact False.elim (pos ((right_location dr (by simpa [dist_eq_norm] using (mem_ball.mp wi).le)).2.2 case1.1))
      · exact case2.2
    have cent : star (center cell.right)=center cell.right := by simp [center,sym]
    have dist : ‖star w-center cell.right‖=‖w-center cell.right‖ := by
      nth_rw 1 [←cent];rw [←star_sub,norm_star]
    refine ⟨star w,?_,?_,by change 0 < -w.im;linarith [lt_of_le_of_ne (le_of_not_gt pos) ni]⟩
    · apply mem_ball.mpr;simpa only [dist_eq_norm,dist] using mem_ball.mp wi
    · have gstar (q : ℝ) (z : ℂ) : G q (star z)=star (G q z) := by simp [G,exp_conj]
      unfold scaledG
      rw [show (e:ℂ)*star w=star ((e:ℂ)*w) by simp,gstar,scaled_zero ep wz,star_zero,mul_zero]
  obtain ⟨t,ti,tz,tp⟩ := getRight
  have locr := right_location dr (by simpa [dist_eq_norm] using (mem_ball.mp ti).le)
  have locl := left_location dl (by simpa [dist_eq_norm] using (mem_ball.mp ui).le)
  obtain ⟨br,_⟩ := envelope_bound re ep eh ti
  obtain ⟨bl,bx⟩ := envelope_bound le ep eh ui
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at br bl
  refine ⟨(e:ℂ)*t,(e:ℂ)*u,?_,?_,?_,?_,?_,?_,br,bl,bx,scaled_zero ep tz,scaled_zero ep uz⟩
  · simpa only [Complex.im_ofReal_mul] using mul_pos ep tp
  · simpa only [Complex.im_ofReal_mul] using mul_pos ep locl.2.2
  · simpa only [Complex.im_ofReal_mul,Complex.re_ofReal_mul] using mul_lt_mul_of_pos_left locr.2.1 ep
  · simpa only [Complex.re_ofReal_mul] using mul_neg_of_pos_of_neg ep locl.2.1
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep];nlinarith [mul_lt_mul_of_pos_left locr.1 ep]
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ep];nlinarith [mul_lt_mul_of_pos_left locl.1 ep]

/-- The open oscillatory side of the already-formalized true positive critical
point excludes all positive real zeros of the quartic-threshold denominator. -/
theorem positive_real_free {q a : ℝ} (hq : q<1)
    (maximum : ∀ x : ℝ, 0<x → x≠a → CriticalEdge.ratio 2 x<CriticalEdge.ratio 2 a)
    (osc : CriticalEdge.ratio 2 a<1/(1-q)) {x : ℝ} (xp : 0<x) :
    G q (x:ℂ) ≠ 0 := by
  have tail := CriticalEdge.tail_pos 4 xp
  have rt : CriticalEdge.ratio 2 x<1/(1-q) := by
    by_cases eqn : x=a
    · simpa only [eqn] using osc
    · exact (maximum x xp eqn).trans osc
  change (Real.exp x-2)/CriticalEdge.tail 4 x<1/(1-q) at rt
  have dt := (div_lt_div_iff₀ tail (sub_pos.mpr hq)).mp rt
  have g : G q (x:ℂ)=((2*(1-q)-(1+x+x^2/2+x^3/6)+q*Real.exp x:ℝ):ℂ) := by
    unfold G
    push_cast
    ring
  rw [g,ne_eq,Complex.ofReal_eq_zero]
  unfold CriticalEdge.tail CriticalEdge.tap at dt
  norm_num [Finset.sum_range_succ,Nat.factorial] at dt
  linarith

#print axioms envelope_bound
#print axioms physical_pair
#print axioms positive_real_free
end OrderedPartitions.FourPole.Box
