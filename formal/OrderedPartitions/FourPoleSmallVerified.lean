import OrderedPartitions.FourPoleAngularBudget
import OrderedPartitions.FourPoleSmallResidues

noncomputable section
namespace OrderedPartitions.FourPole.SixIntervals
open Real Complex

private theorem finish {C A E V D S q : ℝ} (amp : A+E≤C) (c0 : 0≤A+E) (v0 : 0≤V)
    (s0 : 0<S) (den : S≤D) (cost : V≤q*S) (score : C^2+q^2<1) :
    0<D ∧ (A+E)^2+(V/D)^2<1 := by
  have dp := s0.trans_le den
  have qp : 0≤q := by by_contra! neg;linarith only [cost,v0,mul_neg_of_neg_of_pos neg s0]
  have r : V/D≤q := (div_le_iff₀ dp).mpr (cost.trans (mul_le_mul_of_nonneg_left den qp))
  exact ⟨dp,by nlinarith only [score,mul_self_le_mul_self c0 amp,
    mul_self_le_mul_self (div_nonneg v0 dp.le) r]⟩

/-- All four visible comparisons of the two physical pole pairs are
effective throughout 0<ε≤101/1000, beginning at row 288. -/
theorem actual_small_gate {n h : ℕ} (hn : 288≤n) (hp : 1≤h) (hg : h≤4)
    {e : ℝ} (ep : 0<e) (eh : e≤101/1000) (vis : 3≤(n:ℝ)*e) {z v : ℂ}
    (pol : CirclePoles (1-e^4/24) 3 z v) (order : ‖z‖<‖v‖) :
    let q := 1-e^4/24
    let A := secondaryWeight n q z v
    let E := circleError n q 3 z
    let E' := circleError (n+h) q 3 z
    let δ := (h:ℝ)*z.arg
    let η := (h:ℝ)*v.arg
    let L := (‖z‖/‖v‖)^h
    |A|+|E|≤2/5 ∧ 0<Real.sin δ ∧
      (|A|+|E|)^2+((|A| *shiftChord δ η L+|E'|+|E|)/Real.sin δ)^2<1 := by
  obtain ⟨i,el,eu⟩ := cover ep.le eh
  let p := cells i
  have val := valid i
  let q := 1-e^4/24
  let A := |secondaryWeight n q z v|
  let E := |circleError n q 3 z|
  let E' := |circleError (n+h) q 3 z|
  let L := (‖z‖/‖v‖)^h
  let H : ℝ := high p
  let b : ℝ := low p
  let R : ℝ := residue p
  let T : ℝ := amplitude p
  let C : ℝ := cosine p
  let δ := (h:ℝ)*z.arg
  let η := (h:ℝ)*v.arg
  let V := A*shiftChord δ η L+E'+E
  change A+E≤2/5 ∧ 0<Real.sin δ ∧ (A+E)^2+(V/Real.sin δ)^2<1
  have en : 0≤E := abs_nonneg _
  have an : 0≤A := abs_nonneg _
  have cn : 0≤A+E := add_nonneg an en
  have vn : 0≤V := by dsimp only [V,shiftChord];exact add_nonneg (add_nonneg (mul_nonneg an (norm_nonneg _)) (abs_nonneg _)) en
  have lp : 0≤L := by dsimp [L];positivity
  have vpos : 0<‖v‖ := (norm_nonneg _).trans_lt order
  have lu : L≤1 := pow_le_one₀ (by positivity) ((div_le_one vpos).mpr order.le)
  obtain ⟨am,tails⟩ := size_budgets i p rfl ep el eu pol hn vis
  have ab : A≤T := am
  have eb : E≤R*e := tails n (by omega)
  have eb' : E'≤R*e := tails (n+h) (by omega)
  have rp : 0≤R := by by_contra! neg;exact (not_lt_of_ge en) (eb.trans_lt (mul_neg_of_neg_of_pos neg ep))
  have tc : C=T+R*(p.hi:ℝ) := by dsimp [C,T,R,cosine,tailE];push_cast;rfl
  have cm : A+E≤C := by rw [tc];linarith only [ab,eb,mul_le_mul_of_nonneg_left eu rp]
  have cc := (Rat.cast_lt (K:=ℝ)).mpr val.cosine
  push_cast at cc
  refine ⟨cm.trans (show C<2/5 from cc).le,?_⟩
  obtain ⟨_,_,zl,zh,vl,vh⟩ := ratio_bounds i p rfl ep eu pol
  have bp : 0<b := by change 0<(low (cells i):ℝ);exact_mod_cast val.lower
  have bh : 0≤H := by by_contra! neg;linarith only [zl,zh,mul_pos bp ep,mul_neg_of_neg_of_pos neg ep]
  have sin3 : 0<(sinShort p:ℝ) := by exact_mod_cast val.sin3
  have sin4 : 0<(sinFour p:ℝ) := by exact_mod_cast val.sin4
  by_cases ht : h≤3
  · let Q : ℝ := short p
    let S : ℝ := sinShort p
    have Qs : Q*S=2*C := by
      dsimp [Q,S,short,C,cosine,tailE];push_cast;field_simp [sin3.ne']
    have lower : S≤Real.sin δ := by
      have tmp := sine_short hp ht ((mul_pos bp ep).le.trans zl) zh
      dsimp [S,sinShort];push_cast;dsimp only [δ];linarith only [tmp,mul_le_mul_of_nonneg_left eu bh]
    have cost : V≤Q*S := by
      rw [Qs];dsimp only [V]
      have ch := mul_le_mul_of_nonneg_left (chord_short (δ:=δ) (η:=η) lp lu) an
      rw [tc];linarith only [ch,ab,eb,eb',mul_le_mul_of_nonneg_left eu rp]
    have sc := (Rat.cast_lt (K:=ℝ)).mpr val.short
    push_cast at sc
    exact finish cm cn vn sin3 lower cost sc
  · have heq : h=4 := by omega
    subst h
    let Q : ℝ := fourth p
    let S : ℝ := sinFour p
    have Qs : Q*S=12*H*T+C*(4*H)^2*(p.hi:ℝ)/2+2*R := by
      dsimp only [Q,S,fourth,T,H,C,R];push_cast;field_simp [sin4.ne']
    have ab4 := sine_fourth (mul_pos bp ep).le zl zh
    have lS : S*e ≤ Real.sin δ := by
      change _≤Real.sin ((4:ℕ)*z.arg)
      norm_num only [Nat.cast_ofNat]
      have hiPow := pow_le_pow_left₀ ep.le eu 2
      have ext := mul_le_mul_of_nonneg_left hiPow (show 0≤(4*H)^3*e by positivity)
      dsimp only [S,sinFour];push_cast
      nlinarith only [ab4,ext]
    let a := 4*(π/4-z.arg)
    let a' := 4*(3*π/4-v.arg)
    have aa : 0≤a := by dsimp [a];linarith only [zl,mul_pos bp ep]
    have ap : 0≤a' := by dsimp [a'];linarith only [vl,mul_pos bp ep]
    have au : a≤4*H*e := by dsimp [a];linarith only [zh]
    have au' : a'≤4*H*e := by dsimp [a'];linarith only [vh]
    have Lb : 1-L≤8*H*e := (ratio_powers i p rfl ep el eu pol hn vis).2
    have ch : shiftChord δ η L≤(4*H)^2*e^2/2+12*H*e := by
      rw [show δ=π-a by dsimp [δ,a];ring,show η=3*π-a' by dsimp [η,a'];ring]
      have h := chord_fourth (a:=a) (b:=a') lp lu
      rw [abs_of_nonneg ap] at h
      nlinarith only [h,Lb,au',pow_le_pow_left₀ aa au 2]
    have e2 := mul_le_mul_of_nonneg_right eu ep.le
    have capA := mul_le_mul_of_nonneg_right (show A≤C by linarith) (show 0≤(4*H)^2*e^2 by positivity)
    have capT := mul_le_mul_of_nonneg_right ab (show 0≤12*H*e by positivity)
    have edge := mul_le_mul_of_nonneg_left e2 (show 0≤C*(4*H)^2 by exact mul_nonneg (cn.trans cm) (sq_nonneg _))
    have cost : V≤Q*(S*e) := by
      rw [←mul_assoc,Qs];dsimp only [V]
      nlinarith only [mul_le_mul_of_nonneg_left ch an,capA,capT,edge,eb,eb']
    have sc := (Rat.cast_lt (K:=ℝ)).mpr val.fourth
    push_cast at sc
    exact finish cm cn vn (mul_pos sin4 ep) lS cost sc

#print axioms actual_small_gate
end OrderedPartitions.FourPole.SixIntervals
