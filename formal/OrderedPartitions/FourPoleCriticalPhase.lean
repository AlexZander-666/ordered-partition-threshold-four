import OrderedPartitions.FourPoleBranchTransport
import OrderedPartitions.TwoPoleAngles

noncomputable section
namespace OrderedPartitions.FourPole
open Complex Filter Set Metric
open scoped Topology ComplexConjugate

theorem real_critical_zero {a : ℝ} (ha : 0<a) (ht : CriticalEdge.criticalTest 2 a=0)
    (C0 : 0<CriticalEdge.ratio 2 a) : G (1-1/CriticalEdge.ratio 2 a) (a:ℂ)=0 := by
  let C := CriticalEdge.ratio 2 a
  have critical := (CriticalEdge.critical_contact 2 ha ht).1
  change CriticalEdge.den 2 C a=0 at critical
  norm_num [CriticalEdge.den,CriticalEdge.tail,CriticalEdge.tap,Finset.sum_range_succ,Nat.factorial] at critical
  have real : 1-2*(1-1/C)-a-a^2/2-a^3/6+(1-1/C)*Real.exp a=0 := by
    have nz : C≠0 := C0.ne'
    field_simp
    linear_combination 12*critical
  have t := congrArg (fun r : ℝ ↦ (r:ℂ)) real
  unfold G
  push_cast at t ⊢
  simpa only [Complex.ofReal_zero,Complex.ofReal_exp,C] using t

theorem primary_critical_limit {a c : ℝ} (ap : 0<a) (au : a<1) (c1 : c<1)
    (gc : G c (a:ℂ)=0) {A B : ℝ→ℂ} (data : ∀ t∈Ioo c 1,CirclePoles t 3 (A t) (B t)) :
    Tendsto A (𝓝[Ioo c 1] c) (𝓝 (a:ℂ)) := by
  apply Metric.tendsto_nhds.mpr
  intro δ dp
  let r := min (min δ a) 1/2
  have rp : 0<r := by dsimp [r];positivity
  have ra : r<a := by unfold r at rp ⊢;linarith [(min_le_left (min δ a) 1).trans (min_le_right δ a)]
  have rd : r<δ := by unfold r at rp ⊢;linarith [(min_le_left (min δ a) 1).trans (min_le_left δ a)]
  have r1 : r≤1 := by unfold r;linarith [min_le_right (min δ a) (1:ℝ)]
  filter_upwards [(pole_persists c1 gc rp).filter_mono nhdsWithin_le_nhds,eventually_mem_nhdsWithin]
    with t ex ts
  obtain ⟨w,wb,wg⟩ := ex
  have close := mem_ball.mp wb
  have nr : ‖w-(a:ℂ)‖<r := by simpa [dist_eq_norm] using close
  have re := abs_lt.mp ((Complex.abs_re_le_norm _).trans_lt nr)
  simp only [Complex.sub_re,Complex.ofReal_re] at re
  have nw := norm_add_le (w-(a:ℂ)) (a:ℂ)
  rw [sub_add_cancel,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ap] at nw
  have h := data t ts
  rcases h.exhaustive w (by linarith) wg with eqn|eqn|eqn|eqn
  · exact eqn ▸ close.trans rd
  · rw [eqn,Complex.star_def,Complex.dist_conj_comm,Complex.conj_ofReal] at close
    exact close.trans rd
  · rw [eqn] at re;linarith [h.left]
  · rw [eqn,Complex.star_def,Complex.conj_re] at re;linarith [h.left]

private theorem real_derivative {q : ℝ} {z : ℂ} (gz : G q z=0) (xp : 0<z.re)
    (xu : z.re<6/5) (yp : 0<z.im) (yu : z.im<1) : |(first q z).re|≤2*z.im^2 := by
  let x := z.re
  let y := z.im
  let V := 1+x+x^2/2-y^2/6
  have imag : q*Real.exp x*Real.sin y=y*V := by
    have t := congrArg Complex.im gz
    simp [G,pow_succ,Complex.mul_re,Complex.mul_im,Complex.div_ofNat_im,Complex.exp_im] at t
    dsimp [x,y,V];linarith only [t]
  have re : (first q z).re=q*Real.exp x*Real.cos y-(1+x+x^2/2-y^2/2) := by
    simp [first,x,y,pow_two,Complex.mul_re,Complex.div_ofNat_re,Complex.exp_re];ring
  have yr : y∈Ioo 0 (Real.pi/2) := ⟨yp,by change z.im<_;linarith [Real.pi_gt_three]⟩
  have sy := Real.sin_pos_of_pos_of_lt_pi yr.1 (by linarith [yr.2,Real.pi_pos])
  have eqn : (first q z).re=(y*Real.cos y/Real.sin y-1)*V+y^2/3 := by
    rw [re];field_simp [sy.ne'];dsimp [V] at *;linear_combination 6*Real.cos y*imag
  have Vpos : 0≤V := by
    change 0≤1+z.re+z.re^2/2-z.im^2/6
    nlinarith only [xp, sq_nonneg z.re,mul_lt_mul_of_pos_right yu yp,yu]
  have Vcap : V≤3 := by
    change 1+z.re+z.re^2/2-z.im^2/6≤3
    nlinarith only [xu,pow_le_pow_left₀ xp.le xu.le 2,sq_nonneg z.im]
  have cot := TwoPole.cot_deficit_bound yr
  have err : |y*Real.cos y/Real.sin y-1|≤y^2/2 := by rw [abs_sub_comm,abs_of_nonneg cot.1];exact cot.2
  rw [eqn]
  apply (abs_add_le _ _).trans
  rw [abs_mul,abs_of_nonneg Vpos,abs_of_nonneg (by positivity : 0≤y^2/3)]
  change _≤2*y^2
  nlinarith only [mul_le_mul err Vcap Vpos (by positivity),sq_nonneg y]

theorem phase_at_critical {a c : ℝ} (ap : 0<a) (au : a<1) (c1 : c<1)
    (gc : G c (a:ℂ)=0) {A B : ℝ→ℂ} (data : ∀ t∈Ioo c 1,CirclePoles t 3 (A t) (B t))
    (n : ℕ) : Tendsto (fun q ↦ polarPhase n q (A q)) (𝓝[Ioo c 1] c) (𝓝 (Real.pi/2)) := by
  have l := primary_critical_limit ap au c1 gc data
  have xr : Tendsto (fun q ↦ (A q).re) (𝓝[Ioo c 1] c) (𝓝 a) := Complex.continuous_re.continuousAt.tendsto.comp l
  have yi : Tendsto (fun q ↦ (A q).im) (𝓝[Ioo c 1] c) (𝓝 0) := Complex.continuous_im.continuousAt.tendsto.comp l
  have ang := (Complex.continuousAt_arg (x:=(a:ℂ)) (Or.inl ap)).tendsto.comp l
  rw [arg_ofReal_of_nonneg ap.le] at ang
  let L := 𝓝[Ioo c 1] c
  let R := fun q ↦ (first q (A q)).re/(A q).im
  let I := fun q ↦ (3*(A q).re^2-(A q).im^2)/6
  have imEq (q : ℝ) (hq : q∈Ioo c 1) : (first q (A q)).im=(A q).im*I q := by
    rw [first_at_root (data q hq).zeroRight]
    simp [I,pow_succ,Complex.div_ofNat_im,Complex.mul_im,Complex.mul_re];ring
  have ib : Tendsto I L (𝓝 (a^2/2)) := by
    have h := (((xr.pow 2).const_mul 3).sub (yi.pow 2)).div_const 6
    convert h using 1
    norm_num;ring
  have ip : 0<a^2/2 := by positivity
  have dom : ∀ᶠ t in L,t∈Ioo c 1 := eventually_mem_nhdsWithin
  have bound : ∀ᶠ q in L,|R q|≤2*(A q).im := by
    filter_upwards [dom,xr.eventually_lt_const (by linarith : a<6/5),yi.eventually_lt_const (by norm_num : (0:ℝ)<1)]
      with q hq hx hy
    obtain pol := data q hq
    rw [show |R q|=|(first q (A q)).re|/(A q).im by simp [R,abs_div,abs_of_pos pol.upperRight],
      div_le_iff₀ pol.upperRight]
    nlinarith only [real_derivative pol.zeroRight pol.right hx pol.upperRight hy]
  have rlim : Tendsto R L (𝓝 0) := by
    have upper : Tendsto (fun q ↦ 2*(A q).im) L (𝓝 0) := by simpa using yi.const_mul 2
    exact squeeze_zero_norm' (by simpa only [Real.norm_eq_abs] using bound) upper
  have rat := rlim.div ib ip.ne'
  rw [zero_div] at rat
  have beta := TwoPole.arg_vertical_limit (Z:=fun q ↦ first q (A q))
    (by filter_upwards [dom,ib.eventually_const_lt ip] with q hq hp;rw [imEq q hq];exact mul_pos (data q hq).upperRight hp)
    (rat.congr' (by
      filter_upwards [dom] with q hq
      simp only [Pi.div_apply,imEq q hq,R]
      rw [div_div]))
  simpa only [polarPhase,Function.comp_def,mul_zero,zero_add] using (ang.const_mul ((n+1:ℕ):ℝ)).add beta

#print axioms real_critical_zero
#print axioms primary_critical_limit
#print axioms phase_at_critical
end OrderedPartitions.FourPole
