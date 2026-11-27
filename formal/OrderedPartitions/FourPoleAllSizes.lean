import OrderedPartitions.FourPoleEffectiveTail
import OrderedPartitions.FourPoleFiniteVerified

/-! The sharp five-row window for the original threshold-four ordered partition family. -/
namespace OrderedPartitions.FourPole
open RootTracking

theorem original_all (n h : ℕ) (hp : 1≤h) (hg : h≤4) :
    OrderedPair (n/4) (row n 4) (row (n+h) 4) := by
  by_cases hn : 288≤n
  · exact original_analytic hn hp hg
  · exact FourPoleFinite.original_finite n h (by omega) hp hg

theorem original_five_rows (n : ℕ) (i j : Fin 5) (ij : i<j) :
    OrderedPair ((n+i.val)/4) (row (n+i.val) 4) (row (n+j.val) 4) := by
  have lt : i.val<j.val := ij
  have bound := j.isLt
  have eqn : n+i.val+(j.val-i.val)=n+j.val := by omega
  simpa only [eqn] using original_all (n+i.val) (j.val-i.val) (by omega) (by omega)

/-- Arbitrarily late windows of six rows contain a forbidden degree jump. -/
theorem six_rows_fail (m : ℕ) :
    ¬ OrderedPair ((4*m+3)/4) (row (4*m+3) 4) (row (4*m+8) 4) := by
  rintro ⟨_,_,⟨ys,hy,_⟩|⟨ys,hy,_⟩⟩ <;>
    have bad := hy.degree <;> rw [(original_shape (4*m+8)).1] at bad <;> omega

#print axioms original_all
#print axioms original_five_rows
#print axioms six_rows_fail
end OrderedPartitions.FourPole
