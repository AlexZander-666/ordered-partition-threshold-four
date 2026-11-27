import OrderedPartitions.FourPolePhysicalContour
import OrderedPartitions.FourPoleSmallTaylor

noncomputable section
namespace OrderedPartitions.FourPole
open Complex

/-- All four distinct physical poles, with an effective boundary lower bound,
through the singular corner. -/
theorem small_contour {e : ℝ} (ep : 0<e) (eh : e≤1/10) :
    ∃ a b : ℂ, CirclePoles (1-e^4/24) 3 a b ∧ a.im<a.re ∧
      ‖a‖<e ∧ e<‖b‖ ∧ ∀ w : ℂ, ‖w‖=3 → 1/300<‖G (1-e^4/24) w‖ := by
  let s := Real.sqrt 2/2
  have sq : s^2=1/2 := by dsimp [s];nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  have sp : 0<s := by dsimp [s];positivity
  have sl : 7/10<s := by nlinarith
  have sh : s<3/4 := by nlinarith
  let A : ℂ := ⟨s,s⟩
  let B : ℂ := ⟨-s,s⟩
  have aa : A^2=I := by
    apply Complex.ext <;> simp [A,pow_two,mul_re,mul_im]; nlinarith
  have bb : B^2= -I := by
    apply Complex.ext <;> simp [B,pow_two,mul_re,mul_im]; nlinarith
  have normA : ‖A‖=1 := by
    have : ‖A‖^2=1 := by rw [Complex.sq_norm];dsimp [A,normSq];nlinarith
    nlinarith [norm_nonneg A]
  have normB : ‖B‖=1 := by
    have : ‖B‖^2=1 := by rw [Complex.sq_norm];dsimp [B,normSq];nlinarith
    nlinarith [norm_nonneg B]
  obtain ⟨w,wc,wz⟩ := tenth_corrected ep eh (show A^4= -1 by rw [show (4:ℕ)=2*2 by decide,pow_mul,aa,I_sq]) normA
  obtain ⟨v,vc,vz⟩ := tenth_corrected ep eh (show B^4= -1 by rw [show (4:ℕ)=2*2 by decide,pow_mul,bb,neg_sq,I_sq]) normB
  let C : ℂ := ⟨s,s-3/10*e⟩
  let D : ℂ := ⟨-s,s+3/10*e⟩
  have centerA : A-(3/10:ℂ)*A^2*e=C := by
    rw [aa];apply Complex.ext <;> simp [A,C,mul_re,mul_im,div_ofNat_re,div_ofNat_im]
  have centerB : B-(3/10:ℂ)*B^2*e=D := by
    rw [bb];apply Complex.ext <;> simp [B,D,mul_re,mul_im,div_ofNat_re,div_ofNat_im]
  rw [centerA] at wc
  rw [centerB] at vc
  have rad : (3/5:ℝ)*e^2≤(3/50:ℝ)*e := by nlinarith only [mul_le_mul_of_nonneg_left eh ep.le]
  have WR := abs_lt.mp ((abs_re_le_norm (w-C)).trans_lt wc)
  have WI := abs_lt.mp ((abs_im_le_norm (w-C)).trans_lt wc)
  have VR := abs_lt.mp ((abs_re_le_norm (v-D)).trans_lt vc)
  have VI := abs_lt.mp ((abs_im_le_norm (v-D)).trans_lt vc)
  change _<w.re-s ∧ w.re-s<_ at WR
  change _<w.im-(s-3/10*e) ∧ w.im-(s-3/10*e)<_ at WI
  change _<v.re-(-s) ∧ v.re-(-s)<_ at VR
  change _<v.im-(s+3/10*e) ∧ v.im-(s+3/10*e)<_ at VI
  have c2 : ‖C‖^2=s^2+(s-3/10*e)^2 := by rw [Complex.sq_norm];dsimp [C,normSq];ring
  have d2 : ‖D‖^2=s^2+(s+3/10*e)^2 := by rw [Complex.sq_norm];dsimp [D,normSq];ring
  have cn : ‖C‖≤1-e/8 := by
    nlinarith only [c2,sq,mul_lt_mul_of_pos_right sl ep,mul_le_mul_of_nonneg_left eh ep.le,
      norm_nonneg C,eh,ep]
  have dn : 1+e/8≤‖D‖ := by
    nlinarith only [d2,sq,mul_lt_mul_of_pos_right sl ep,norm_nonneg D,ep]
  have du : ‖D‖≤2 := by
    nlinarith only [d2,sq,mul_lt_mul_of_pos_right sh ep,mul_le_mul_of_nonneg_left eh ep.le,
       ep,eh,norm_nonneg D]
  have nw := norm_add_le (w-C) C
  rw [sub_add_cancel] at nw
  have nv := norm_sub_le v (v-D)
  rw [sub_sub_cancel] at nv
  have nvu := norm_add_le (v-D) D
  rw [sub_add_cancel] at nvu
  have wsm : ‖w‖<1 := by linarith
  have vlg : 1<‖v‖ := by linarith
  have vsm : ‖v‖≤3 := by linarith
  let a := (e:ℂ)*w
  let b := (e:ℂ)*v
  have au : 0<a.im := by rw [show a.im=e*w.im by simp [a]];exact mul_pos ep (by linarith)
  have bu : 0<b.im := by rw [show b.im=e*v.im by simp [b]];exact mul_pos ep (by linarith)
  have ang : a.im<a.re := by
    change ((e:ℂ)*w).im<((e:ℂ)*w).re
    simp only [Complex.im_ofReal_mul,Complex.re_ofReal_mul]
    exact mul_lt_mul_of_pos_left (by linarith) ep
  have bl : b.re<0 := by rw [show b.re=e*v.re by simp [b]];exact mul_neg_of_pos_of_neg ep (by linarith)
  have na : ‖a‖=e*‖w‖ := by simp [a,abs_of_pos ep]
  have nb : ‖b‖=e*‖v‖ := by simp [b,abs_of_pos ep]
  have small : ‖a‖<e := by rw [na];simpa using mul_lt_mul_of_pos_left wsm ep
  have big : e<‖b‖ := by rw [nb];simpa using mul_lt_mul_of_pos_left vlg ep
  have bound : ‖b‖≤3/10 := by rw [nb];nlinarith only [mul_le_mul_of_nonneg_left vsm ep.le,eh]
  obtain ⟨pol,floor⟩ := pinned_contour ep (by linarith) au bu ang bl big (by linarith)
      (by linarith) ((Complex.abs_re_le_norm b).trans (by linarith)) wz vz
  exact ⟨a,b,pol,ang,small,big,floor⟩

#print axioms small_contour
end OrderedPartitions.FourPole
