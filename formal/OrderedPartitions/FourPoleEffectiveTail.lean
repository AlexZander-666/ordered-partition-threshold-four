import OrderedPartitions.FourPoleSmallVerified
import OrderedPartitions.FourPoleBulkBudgets

/-! Effective strict interlacing for four jumps of the threshold-four
ordered-set-partition enumerator. -/

noncomputable section
namespace OrderedPartitions.FourPole
open Real RootTracking

/-- The actual tail satisfies the chord-and-contour comparison at every
visible activity. The old root no longer occurs as an input. -/
theorem effective_chord_gate {n h : ℕ} (hn : 288≤n) (hp : 1≤h) (hg : h≤4) :
    PhysicalChordGate n h := by
  intro e ep eh visible
  dsimp only
  intro z v pol _ order
  by_cases sm : e≤101/1000
  · exact SixIntervals.actual_small_gate hn hp hg ep sm visible pol order
  obtain ⟨s,sp,s1,si,a,tail⟩ := bulk_budgets (le_of_not_ge sm) eh pol hn hp hg
  let q := 1-e^4/24
  let A := |secondaryWeight n q z v|
  let E := |circleError n q 3 z|
  let F := |circleError (n+h) q 3 z|
  let δ := (h:ℝ)*z.arg
  let η := (h:ℝ)*v.arg
  let L := (‖z‖/‖v‖)^h
  change s/50≤Real.sin δ at si
  have positive : 0<Real.sin δ := lt_of_lt_of_le (by positivity : 0<s/50) si
  have mass : A≤s/150 := a
  have o : E≤s/1000 := tail n hn
  have ne : F≤s/1000 := tail (n+h) (by omega)
  have cz : 0≤A+E := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have cm : A+E≤1/100 := by linarith
  have lu : L≤1 := pow_le_one₀ (by positivity) ((div_le_one ((norm_nonneg z).trans_lt order)).mpr order.le)
  have ch := chord_short (δ:=δ) (η:=η) (by dsimp [L];positivity : 0≤L) lu
  let T := A*shiftChord δ η L+F+E
  have tp : 0≤T := by dsimp [T,A,shiftChord,E,F];positivity
  have major : T/Real.sin δ≤4/5 := by
    apply (div_le_iff₀ positive).mpr
    dsimp only [T]
    nlinarith only [mul_le_mul_of_nonneg_left ch (show 0≤A from abs_nonneg _),mass,o,ne,si,sp]
  refine ⟨cm.trans (by norm_num),positive,?_⟩
  change (A+E)^2+(T/Real.sin δ)^2<1
  nlinarith only [mul_self_le_mul_self cz cm,mul_self_le_mul_self (div_nonneg tp positive.le) major]

/-- For every old rank at least 288, its row strictly interlaces each of
the next four original rows, with the orientation determined by their degrees. -/
theorem original_analytic {n h : ℕ} (hn : 288≤n) (hp : 1≤h) (hg : h≤4) :
    OrderedPair (n/4) (row n 4) (row (n+h) 4) :=
  original_pair_of_chord hn hg (effective_chord_gate hn hp hg)

#print axioms effective_chord_gate
#print axioms original_analytic
end OrderedPartitions.FourPole
