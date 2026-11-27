import OrderedPartitions.FourPoleJetCatalogue

/-! Interpret the exact Gaussian-rational jet tests as complex norm estimates. -/
namespace OrderedPartitions.FourPole.Box
noncomputable def gaussian (z : ℚ×ℚ) : ℂ := (z.1:ℝ)+(z.2:ℝ)*Complex.I

theorem enclosesJet_norm {D : Disc} {e lo hi : ℚ} {m : ℕ} {J : ℂ}
    (verified : enclosesJet D e m lo hi=true)
    (tail : ‖J-gaussian (jet D e m)‖ ≤ (jetTail e m:ℝ)) :
    (lo:ℝ)≤‖J‖ ∧ ‖J‖≤(hi:ℝ) := by
  let z := jet D e m
  let q := jetTail e m
  have test : 0≤hi-q ∧ z.1^2+z.2^2≤(hi-q)^2 ∧ (lo≤0 ∨ (lo+q)^2≤z.1^2+z.2^2) :=
    of_decide_eq_true verified
  have sq : ‖gaussian z‖^2=(z.1:ℝ)^2+(z.2:ℝ)^2 := by
    rw [Complex.sq_norm]; simp [gaussian,Complex.normSq,pow_two]
  have t : ‖J-gaussian z‖≤(q:ℝ) := tail
  have tn : (0:ℝ)≤q := (norm_nonneg _).trans t
  have h1 : 0≤(hi:ℝ)-(q:ℝ) := by exact_mod_cast test.1
  have h2 : (z.1:ℝ)^2+(z.2:ℝ)^2≤((hi:ℝ)-(q:ℝ))^2 := by exact_mod_cast test.2.1
  have hm : ‖gaussian z‖≤(hi:ℝ)-(q:ℝ) := by nlinarith [norm_nonneg (gaussian z)]
  have pert := abs_norm_sub_norm_le J (gaussian z)
  obtain ⟨low,up⟩ := abs_le.mp (pert.trans t)
  refine ⟨?_,by linarith⟩
  rcases test.2.2 with non|pos
  · exact le_trans (by exact_mod_cast non) (norm_nonneg _)
  · have h : ((lo:ℝ)+(q:ℝ))^2≤(z.1:ℝ)^2+(z.2:ℝ)^2 := by exact_mod_cast pos
    have bound : (lo:ℝ)+(q:ℝ) ≤ ‖gaussian z‖ := by nlinarith [norm_nonneg (gaussian z)]
    linarith

theorem verifiedJet_inputs {c : Cell} {D : Disc} {H : Witness}
    (ok : verifiedJet c D H=true) :
    let e := (c.lo+c.hi)/2
    ∀ J : ℕ→ℂ, (∀ m ≤ 2, ‖J m-gaussian (jet D e m)‖ ≤ (jetTail e m:ℝ)) →
    ((H.lo0:ℝ)≤‖J 0‖ ∧ ‖J 0‖≤(H.hi0:ℝ)) ∧
    ((H.lo1:ℝ)≤‖J 1‖ ∧ ‖J 1‖≤(H.hi1:ℝ)) ∧
     (H.lo2:ℝ)≤‖J 2‖ ∧ ‖J 2‖≤(H.hi2:ℝ) := by
  simp only [verifiedJet,Bool.and_eq_true] at ok
  intro e J boundary
  exact ⟨enclosesJet_norm ok.1.1.2 (boundary 0 (by decide)),
    enclosesJet_norm ok.1.2 (boundary 1 (by decide)),enclosesJet_norm ok.2 (boundary 2 (by decide))⟩

#print axioms enclosesJet_norm
#print axioms verifiedJet_inputs
end OrderedPartitions.FourPole.Box
