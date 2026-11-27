import OrderedPartitions.FourPoleTrueJets

/-! The table's exact Gaussian Horner vectors represent actual truncated derivatives. -/
noncomputable section
namespace OrderedPartitions.FourPole.Box
open Complex Finset

private def hornerStep (D : Disc) (a : ℚ) (z : ℚ×ℚ) : ℚ×ℚ :=
  (z.1*D.x-z.2*D.y+a,z.1*D.y+z.2*D.x)
private theorem gaussian_step (D : Disc) (a : ℚ) (z : ℚ×ℚ) :
    gaussian (hornerStep D a z)=gaussian z*center D+(a:ℂ) := by
  apply Complex.ext <;> simp [gaussian,hornerStep,center,Complex.mul_re,Complex.mul_im]

private theorem horner_readout (D : Disc) (f : ℕ→ℚ) (N : ℕ) (seed : ℚ×ℚ) :
    gaussian ((List.range N).reverse.foldl (fun v i ↦ hornerStep D (f i) v) seed) =
      gaussian seed*(center D)^N+∑ a∈range N,(f a:ℂ)*(center D)^a := by
  induction N generalizing seed with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.reverse_append,List.reverse_singleton,List.singleton_append,List.foldl_cons,
      ih,gaussian_step,Finset.sum_range_succ,pow_succ]
    ring

theorem jet_readout (D : Disc) (e : ℚ) (m : ℕ) :
    gaussian (jet D e m) =
    ∑ a∈range (29-m), ((polyCoeff e (m+a)*((m+a).factorial:ℚ)/(a.factorial:ℚ):ℚ):ℂ)*(center D)^a := by
  have h := horner_readout D (fun a ↦ polyCoeff e (m+a)*((m+a).factorial:ℚ)/(a.factorial:ℚ))
    (29-m) (0,0)
  simpa only [jet,hornerStep,gaussian,Rat.cast_zero,Complex.ofReal_zero,zero_mul,add_zero,zero_add] using h

private def low (e : ℂ) (m : ℕ) (w : ℂ) : ℂ :=
  (if m=0 then 2 else 0)-24/e^4*e^m*∑ a∈range (4-m),(e*w)^a/a.factorial

private theorem short_explicit (e : ℂ) (m : ℕ) (hm : m≤2) (w : ℂ) :
    iteratedDeriv m (shortPoly e) w=low e m w := by
  let b (z : ℂ) := -24/e^4*e*(1+e*z+(e*z)^2/2)
  let c (z : ℂ) := -24/e^4*e^2*(1+e*z)
  have d (z : ℂ) : HasDerivAt (fun x : ℂ ↦ e*x) e z := by simpa using (hasDerivAt_id z).const_mul e
  have db (z : ℂ) : HasDerivAt (shortPoly e) (b z) z := by
    have h := (hasDerivAt_const z (2:ℂ)).sub
      (((((hasDerivAt_const z (1:ℂ)).add (d z)).add (((d z).pow 2).div_const 2)).add
          (((d z).pow 3).div_const 6)).const_mul (24/e^4))
    convert! h using 1; first | rfl | (dsimp [shortPoly,b]; ring)
  have dc (z : ℂ) : HasDerivAt b (c z) z := by
    have h := ((((hasDerivAt_const z (1:ℂ)).add (d z)).add (((d z).pow 2).div_const 2)).const_mul (-24/e^4*e))
    convert! h using 1; first | rfl | (dsimp [b,c]; ring)
  have bp : deriv (shortPoly e)=b := funext fun z ↦ (db z).deriv
  have cp : deriv b = c := funext fun z ↦ (dc z).deriv
  interval_cases m
  · change shortPoly e w=_
    norm_num [shortPoly,low,sum_range_succ,Nat.factorial]
  · rw [show (1:ℕ)=0+1 by decide,iteratedDeriv_succ',bp,iteratedDeriv_zero]
    norm_num [low,b,sum_range_succ,Nat.factorial]
    ring
  · rw [show (2:ℕ)=1+1 by decide,iteratedDeriv_succ',bp,show (1:ℕ)=0+1 by decide,iteratedDeriv_succ',cp,iteratedDeriv_zero]
    norm_num [low,c,sum_range_succ,Nat.factorial]
    ring

private theorem coeff_split (e : ℚ) (he : e≠0) (m a : ℕ) :
    polyCoeff e (m+a)*(m+a).factorial/a.factorial =
    (24/e^4-1)*e^(m+a)/a.factorial -
      (if m+a<4 then 24/e^4*e^(m+a)/a.factorial else 0) +
      (if m=0 ∧ a=0 then 2 else 0) := by
  by_cases h : m+a=0
  · obtain ⟨rfl,rfl⟩ : m=0 ∧ a=0 := by omega
    simp [polyCoeff]; ring
  · have nz : ¬(m=0 ∧ a=0) := by omega
    by_cases small : m+a<4
    · simp [polyCoeff,nz,small,show ¬4≤m+a by omega]
      field_simp
      ring
    · have hi : 4≤m+a := by omega
      simp [polyCoeff,nz,small,hi]
      have split : e^(m+a)=e^4*e^(m+a-4) := by rw [← pow_add]; congr 1; omega
      rw [split]
      field_simp

/-- Algebraic identification of the certified rational midpoint with the
degree-28 truncation of the actual m-th complex derivative. -/
theorem physical_partial (D : Disc) (e : ℚ) (he : 0<e) (m : ℕ) (hm : m≤2) :
    gaussian (jet D e m) = partialJet (e:ℝ) m (center D) := by
  let w := center D
  let x := (e:ℂ)*w
  let t := fun a : ℕ ↦ x^a/(a.factorial:ℂ)
  let A := (24/(e:ℂ)^4-1)*(e:ℂ)^m
  let B := 24/(e:ℂ)^4*(e:ℂ)^m
  let C : ℂ := if m=0 then 2 else 0
  let N := 29-m
  let L := 4-m
  have point (a : ℕ) :
      ((polyCoeff e (m+a)*((m+a).factorial:ℚ)/(a.factorial:ℚ):ℚ):ℂ)*w^a =
      A*t a-(if a<L then B*t a else 0)+(if a=0 then C else 0) := by
    rw [coeff_split e he.ne']
    by_cases al : a<L
    · have small : m+a<4 := by dsimp [L] at al; omega
      by_cases a0 : a=0
      · subst a
        have ml : m<4 := by omega
        by_cases m0 : m=0 <;> simp [A,B,t,C,x,ml,al,m0]
      · simp [A,B,t,C,x,small,al,a0]
        ring
    · have large : ¬m+a<4 := by dsimp [L] at al; omega
      have a0 : a≠0 := by dsimp [L] at al; omega
      simp [A,t,x,al,large,a0]
      ring
  have subrange : (range N).filter (fun a ↦ a<L)=range L := by
    ext a
    simp only [mem_filter,mem_range]
    dsimp [N,L];omega
  have cutoff : (∑ a∈range N, if a<L then B*t a else 0) = B*∑ a∈range L,t a := by
    rw [←Finset.sum_filter,subrange,Finset.mul_sum]
  have at0 : (∑ a∈range N, if a=0 then C else 0)=C := by
    have hN : 0<N := by dsimp [N];omega
    simp [hN]
  rw [jet_readout]
  change (∑ a∈range N, _ * w^a)=_
  simp_rw [point]
  rw [sum_add_distrib,sum_sub_distrib,cutoff,at0,←Finset.mul_sum]
  unfold partialJet
  rw [short_explicit _ _ hm]
  dsimp [low,A,B,C,t,x,N,L,w]
  ring

theorem physical_jet_bound (D : Disc) {e : ℚ} (he : 0<e) (small : e≤6/5)
    (hw : ‖center D‖≤2) {m : ℕ} (hm : m≤2) :
    ‖iteratedDeriv m (scaledG (e:ℝ)) (center D)-gaussian (jet D e m)‖ ≤ (jetTail e m:ℝ) := by
  rw [physical_partial D e he m hm]
  have castSmall : (e:ℝ)≤((6/5:ℚ):ℝ) := by exact_mod_cast small
  norm_num at castSmall
  have b := partialJet_bound (e:=(e:ℝ)) (by exact_mod_cast he) castSmall hw hm
  unfold jetTail
  exact_mod_cast b

/-- No analytic estimates are left as hypotheses for the six midpoint inequalities. -/
theorem actual_midpoint_jets {cell : Cell} {D : Disc} {H : Witness}
    (ok : verifiedJet cell D H=true) (rad : 0≤D.r) :
    let e := (cell.lo+cell.hi)/2
    let J := fun m ↦ iteratedDeriv m (scaledG (e:ℝ)) (center D)
    ((H.lo0:ℝ)≤‖J 0‖ ∧ ‖J 0‖≤(H.hi0:ℝ)) ∧
    ((H.lo1:ℝ)≤‖J 1‖ ∧ ‖J 1‖≤(H.hi1:ℝ)) ∧
      (H.lo2:ℝ)≤‖J 2‖ ∧ ‖J 2‖≤(H.hi2:ℝ) := by
  intro e J
  have bare := ok
  simp only [verifiedJet,Bool.and_eq_true] at bare
  have frame := of_decide_eq_true bare.1.1.1
  have hh : 0≤H.centerCap ∧ D.x^2+D.y^2≤H.centerCap^2 ∧ H.centerCap+D.r≤2 ∧
      0<cell.lo ∧ cell.lo≤cell.hi ∧ cell.hi≤6/5 := ⟨frame.1,frame.2.1,frame.2.2.1,frame.2.2.2.1,
      frame.2.2.2.2.1,frame.2.2.2.2.2.1⟩
  apply verifiedJet_inputs ok J
  intro m hm
  apply physical_jet_bound D (by dsimp [e];linarith [hh.2.2.2.1,hh.2.2.2.2.1])
    (by dsimp [e];linarith [hh.2.2.2.2.1,hh.2.2.2.2.2]) _ hm
  have sr : ‖center D‖^2=(D.x:ℝ)^2+(D.y:ℝ)^2 := by
    rw [Complex.sq_norm];simp [center,Complex.normSq,pow_two]
  have cap : (D.x:ℝ)^2+(D.y:ℝ)^2≤(H.centerCap:ℝ)^2 := by exact_mod_cast hh.2.1
  have nonneg : 0≤(H.centerCap:ℝ) := by exact_mod_cast hh.1
  have cd : ‖center D‖ ≤ (H.centerCap:ℝ) := by nlinarith [norm_nonneg (center D)]
  exact cd.trans (by exact_mod_cast (show H.centerCap≤2 by linarith [hh.2.2.1]))

#print axioms jet_readout
#print axioms physical_partial
#print axioms physical_jet_bound
#print axioms actual_midpoint_jets
end OrderedPartitions.FourPole.Box
