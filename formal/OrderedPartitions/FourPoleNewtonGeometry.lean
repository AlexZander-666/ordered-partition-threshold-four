import OrderedPartitions.FourPoleNewtonBound
import OrderedPartitions.FourPoleNewtonOriginal
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
namespace OrderedPartitions.FourPole
open Complex ExpInterpolation
open scoped ComplexConjugate

/-- The five-point interpolation test uses only the locations of the four pinned
nodes. It applies to every point of the closed disk outside those nodes. -/
theorem kernel_floor_off {a b z : ℂ} (right : 0<a.re) (left : b.re<0)
    (ar : ‖a‖≤6/5) (br : ‖b‖≤8/5) (bx : |b.re|≤6/5) (zr : ‖z‖≤3)
    (distinct : [a,conj a,b,conj b].Nodup) (off : z∉[a,conj a,b,conj b]) :
    1/1600 ≤ ‖kernel [a,conj a,b,conj b] z 1‖ := by
  let μ : ℂ := (a+conj a+b+conj b+z)/5
  have cs : a+conj a+b+conj b=((2*(a.re+b.re):ℝ):ℂ) := by
    rw [show a+conj a+b+conj b=(a+conj a)+(b+conj b) by ring,add_conj,add_conj]
    push_cast;ring
  have ap := (abs_le.mp (Complex.abs_re_le_norm a)).2
  have bp := (abs_le.mp bx).1
  have cent : ‖a+conj a+b+conj b‖≤12/5 := by
    rw [cs,Complex.norm_real,Real.norm_eq_abs,abs_le];constructor <;> linarith
  have muc : ‖μ‖≤27/25 := by
    dsimp only [μ];rw [norm_div,Complex.norm_ofNat]
    linarith only [norm_add_le (a+conj a+b+conj b) z,cent,zr]
  have zc : ‖z-μ‖≤72/25 := by
    rw [show z-μ=(4*z-(a+conj a+b+conj b))/5 by dsimp [μ];ring,
      norm_div,Complex.norm_ofNat]
    have t := norm_sub_le (4*z) (a+conj a+b+conj b)
    rw [norm_mul,Complex.norm_ofNat] at t
    linarith only [t,cent,zr]
  have c1 (p : ℂ) (hp : ‖p‖≤8/5) : ‖p-μ‖≤72/25 := by
    linarith only [norm_sub_le p μ,hp,muc]
  have ar8 : ‖a‖≤8/5 := by linarith
  have av : ‖a‖^2≤(6/5:ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) ar _
  have bv : ‖b‖^2≤(8/5:ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) br _
  have zv : ‖z‖^2≤(3:ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) zr _
  have variance : ‖a-μ‖^2+‖conj a-μ‖^2+‖b-μ‖^2+‖conj b-μ‖^2+‖z-μ‖^2 =
      2*‖a‖^2+2*‖b‖^2+‖z‖^2-5*‖μ‖^2 := by
    simp only [μ,Complex.sq_norm,normSq_apply,sub_re,sub_im,div_ofNat_re,div_ofNat_im,
      add_re,add_im,conj_re,conj_im]
    ring
  have var := variance.le.trans (show 2*‖a‖^2+2*‖b‖^2+‖z‖^2-5*‖μ‖^2≤17 by
                                  nlinarith only [av,bv,zv,sq_nonneg ‖μ‖])
  have du : [a-μ,conj a-μ,b-μ,conj b-μ].Nodup := by
    simpa only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,sub_left_inj] using distinct
  have ou : z-μ∉[a-μ,conj a-μ,b-μ,conj b-μ] := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false,sub_left_inj] using off
  have h := centered_kernel_bound du ou (show a-μ+(conj a-μ)+(b-μ)+(conj b-μ)+(z-μ)=0 by
      dsimp [μ];ring) (c1 _ ar8) (c1 _ (by simpa using ar8)) (c1 _ br)
      (c1 _ (by simpa using br)) zc var
  have tr := kernel_translate [a,conj a,b,conj b] z (-μ) 1
  simp only [List.map_cons,List.map_nil,←sub_eq_add_neg,Complex.ofReal_one,mul_one] at tr
  rw [tr,norm_mul,Complex.norm_exp] at h
  have expbound : Real.exp (-μ).re≤4 := by
    have hr : (-μ).re≤27/25 := (Complex.re_le_norm _).trans (by simpa using muc)
    apply (Real.exp_le_exp.mpr hr).trans
    rw [show (27/25:ℝ)=1+2/25 by norm_num,Real.exp_add]
    have step := Real.exp_bound_div_one_sub_of_interval (x:=2/25) (by norm_num) (by norm_num)
    norm_num at step
    nlinarith only [mul_le_mul Real.exp_one_lt_three.le step (Real.exp_pos _).le (by norm_num : (0:ℝ)≤3)]
  nlinarith only [h,mul_le_mul_of_nonneg_right expbound (norm_nonneg (kernel [a,conj a,b,conj b] z 1))]

#print axioms kernel_floor_off
end OrderedPartitions.FourPole
